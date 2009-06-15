(* camlp5r *)
(* $Id: q_ast.ml,v 1.12 2007/08/02 22:21:31 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Printf;

value not_impl f x =
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  failwith ("q_ast.ml: " ^ f ^ ", not impl: " ^ desc)
;

value call_with r v f a =
  let saved = r.val in
  try do {
    r.val := v;
    let b = f a in
    r.val := saved;
    b
  }
  with e -> do { r.val := saved; raise e }
;

value eval_antiquot entry s =
  try
    let i = String.index s ',' in
    let j = String.index_from s (i + 1) ':' in
    let k = String.index_from s (j + 1) ':' in
    let bp = int_of_string (String.sub s 0 i) in
    let ep = int_of_string (String.sub s (i + 1) (j - i - 1)) in
    let sh = int_of_string (String.sub s (j + 1) (k - j - 1)) in
    let str = String.sub s (k + 1) (String.length s - k - 1) in
    let r =
      call_with Plexer.dollar_for_antiquot_loc False
        (Grammar.Entry.parse entry) (Stream.of_string str)
    in
    let loc =
      let shift_bp = String.length "$" + sh in
      let shift_ep = String.length "$" in
      Stdpp.make_loc (bp + shift_bp, ep - shift_ep)
    in
    Some (loc, r)
  with
  [ Not_found -> None ]
;

(* horrible hack for opt antiquotations; a string has been installed in
   the ASt at the place of a list, an option or a bool, using Obj.repr;
   ugly but local to q_ast.ml *)
value eval_antiquot_patch entry v =
  if Obj.is_block (Obj.repr v) && Obj.tag (Obj.repr v) = Obj.string_tag then
    let s : string = Obj.magic v in
    match eval_antiquot entry s with
    [ Some loc_r -> Some loc_r
    | None -> assert False ]
  else None
;

value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value str_item_eoi = Grammar.Entry.create Pcaml.gram "str_item";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
value module_expr_eoi = Grammar.Entry.create Pcaml.gram "module_expr";

module Meta =
  struct
    open MLast;
    value loc = Stdpp.dummy_loc;
    value ln () = <:expr< $lid:Stdpp.loc_name.val$ >>;
    value e_list elem el =
      match eval_antiquot_patch expr_eoi el with
      [ Some (loc, r) -> <:expr< $anti:r$ >>
      | None ->
          loop el where rec loop =
            fun
            [ [] -> <:expr< [] >>
            | [e :: el] -> <:expr< [$elem e$ :: $loop el$] >> ] ]
    ;
    value p_list elem el =
      match eval_antiquot_patch patt_eoi el with
      [ Some (loc, r) -> <:patt< $anti:r$ >>
      | None ->
          loop el where rec loop =
            fun
            [ [] -> <:patt< [] >>
            | [e :: el] -> <:patt< [$elem e$ :: $loop el$] >> ] ]
    ;
    value e_option elem eo =
      match eval_antiquot_patch expr_eoi eo with
      [ Some (loc, r) -> <:expr< $anti:r$ >>
      | None ->
          match eo with
          [ None -> <:expr< None >>
          | Some e -> <:expr< Some $elem e$ >> ] ]
    ;
    value e_bool b =
      match eval_antiquot_patch expr_eoi b with
      [ Some (loc, r) -> <:expr< $anti:r$ >>
      | None -> if b then <:expr< True >> else <:expr< False >> ]
    ;
    value p_bool b =
      match eval_antiquot_patch patt_eoi b with
      [ Some (loc, r) -> <:patt< $anti:r$ >>
      | None -> if b then <:patt< True >> else <:patt< False >> ]
    ;
    value e_string s =
      match eval_antiquot expr_eoi s with
      [ Some (loc, r) -> <:expr< $anti:r$ >>
      | None -> <:expr< $str:s$ >> ]
    ;
    value p_string s =
      match eval_antiquot patt_eoi s with
      [ Some (loc, r) -> <:patt< $anti:r$ >>
      | None -> <:patt< $str:s$ >> ]
    ;
    value e_type t = 
      let ln = ln () in
      loop t where rec loop =
        fun 
        [ TyAcc _ t1 t2 -> <:expr< MLast.TyAcc $ln$ $loop t1$ $loop t2$ >> 
        | TyAny _ -> <:expr< MLast.TyAny $ln$ >>
        | TyApp _ t1 t2 -> <:expr< MLast.TyApp $ln$ $loop t1$ $loop t2$ >> 
        | TyLid _ s -> <:expr< MLast.TyLid $ln$ $e_string s$ >>
        | TyQuo _ s -> <:expr< MLast.TyQuo $ln$ $e_string s$ >>
        | TyUid _ s -> <:expr< MLast.TyUid $ln$ $e_string s$ >>
        | x -> not_impl "e_type" x ]
    ;
    value p_type =
      fun
      [ TyLid _ s -> <:patt< MLast.TyLid _ $p_string s$ >>
      | x -> not_impl "p_type" x ]
    ;
    value e_type_decl =
      fun
      [ x -> not_impl "e_type_decl" x ]
    ;
    value e_patt p =
      let ln = ln () in
      loop p where rec loop =
        fun
        [ PaAcc _ p1 p2 -> <:expr< MLast.PaAcc $ln$ $loop p1$ $loop p2$ >>
        | PaAli _ p1 p2 -> <:expr< MLast.PaAli $ln$ $loop p1$ $loop p2$ >>
        | PaAnt _ p ->
            match p with
            [ PaLid _ s ->
                match eval_antiquot expr_eoi s with
                [ Some (loc, r) ->
                    let r = <:expr< MLast.PaAnt $ln$ $r$ >> in
                    <:expr< $anti:r$ >>
                | None -> assert False ]
            | PaStr _ s ->
                match eval_antiquot expr_eoi s with
                [ Some (loc, r) -> <:expr< $anti:r$ >>
                | None -> assert False ]
            | _ -> assert False ]
        | PaAny _ -> <:expr< MLast.PaAny $ln$ >>
        | PaApp _ p1 p2 -> <:expr< MLast.PaApp $ln$ $loop p1$ $loop p2$ >>
        | PaInt _ s k -> <:expr< MLast.PaInt $ln$ $e_string s$ $str:k$ >>
        | PaFlo _ s -> <:expr< MLast.PaFlo $ln$ $e_string s$ >>
        | PaLid _ s -> <:expr< MLast.PaLid $ln$ $e_string s$ >>
        | PaStr _ s -> <:expr< MLast.PaStr $ln$ $e_string s$ >>
        | PaTyc _ p t -> <:expr< MLast.PaTyc $ln$ $loop p$ $e_type t$ >>
        | PaUid _ s -> <:expr< MLast.PaUid $ln$ $e_string s$ >>
        | x -> not_impl "e_patt" x ]
    ;
    value p_patt =
      fun
      [ x -> not_impl "p_patt" x ]
    ;
    value e_expr e =
      let ln = ln () in
      loop e where rec loop =
        fun
        [ ExAcc _ e1 e2 -> <:expr< MLast.ExAcc $ln$ $loop e1$ $loop e2$ >>
        | ExAnt _ e ->
            match e with
            [ ExLid _ s ->
                match eval_antiquot expr_eoi s with
                [ Some (loc, r) ->
                    let r = <:expr< MLast.ExAnt $ln$ $r$ >> in
                    <:expr< $anti:r$ >>
                | None -> assert False ]
            | ExStr _ s ->
                match eval_antiquot expr_eoi s with
                [ Some (loc, r) -> <:expr< $anti:r$ >>
                | None -> assert False ]
            | _ -> assert False ]
        | ExApp _ e1 e2 -> <:expr< MLast.ExApp $ln$ $loop e1$ $loop e2$ >>
        | ExArr _ el ->
            <:expr< MLast.ExArr $ln$ $e_list loop el$ >>
        | ExIfe _ e1 e2 e3 ->
            <:expr< MLast.ExIfe $ln$ $loop e1$ $loop e2$ $loop e3$ >>
        | ExInt _ s k -> <:expr< MLast.ExInt $ln$ $e_string s$ $str:k$ >>
        | ExFlo _ s -> <:expr< MLast.ExFlo $ln$ $e_string s$ >>
        | ExFun _ pwel ->
            let pwel =
              e_list
                (fun (p, eo, e) ->
                   <:expr< ($e_patt p$, $e_option loop eo$, $loop e$) >>)
                pwel
            in
            <:expr< MLast.ExFun $ln$ $pwel$ >>
        | ExLet _ rf lpe e ->
            let rf = e_bool rf in
            let lpe =
              e_list (fun (p, e) -> <:expr< ($e_patt p$, $loop e$) >>) lpe
            in
            <:expr< MLast.ExLet $ln$ $rf$ $lpe$ $loop e$ >>
        | ExLid _ s -> <:expr< MLast.ExLid $ln$ $e_string s$ >>
        | ExMat _ e pwel ->
            let pwel =
              e_list
                (fun (p, eo, e) ->
                   <:expr< ($e_patt p$, $e_option loop eo$, $loop e$) >>)
                pwel
            in
            <:expr< MLast.ExMat $ln$ $loop e$ $pwel$ >>
        | ExSeq _ el ->
            <:expr< MLast.ExSeq $ln$ $e_list loop el$ >>
        | ExStr _ s -> <:expr< MLast.ExStr $ln$ $e_string s$ >>
        | ExTup _ [e :: el] ->
            let el = <:expr< [$loop e$ :: $e_list loop el$] >> in
            <:expr< MLast.ExTup $ln$ $el$ >>
        | ExTyc _ e t -> <:expr< MLast.ExTyc $ln$ $loop e$ $e_type t$ >>
        | ExUid _ s -> <:expr< MLast.ExUid $ln$ $e_string s$ >>
        | x -> not_impl "e_expr" x ]
    ;
    value p_expr e =
      loop e where rec loop =
        fun
        [ ExAcc _ e1 e2 -> <:patt< MLast.ExAcc _ $loop e1$ $loop e2$ >>
        | ExAnt _ e ->
            match e with
            [ ExLid _ s ->
                match eval_antiquot patt_eoi s with
                [ Some (loc, r) ->
                    let r = <:patt< MLast.ExAnt _ $r$ >> in
                    <:patt< $anti:r$ >>
                | None -> assert False ]
            | ExStr _ s ->
                match eval_antiquot patt_eoi s with
                [ Some (loc, r) -> <:patt< $anti:r$ >>
                | None -> assert False ]
            | _ -> assert False ]
        | ExInt _ s k -> <:patt< MLast.ExInt _ $p_string s$ $str:k$ >>
        | ExFlo _ s -> <:patt< MLast.ExFlo _ $p_string s$ >>
        | ExLet _ rf lpe e ->
            let rf = p_bool rf in
            let lpe =
              p_list (fun (p, e) -> <:patt< ($p_patt p$, $loop e$) >>) lpe
            in
            <:patt< MLast.ExLet _ $rf$ $lpe$ $loop e$ >>
        | x -> not_impl "p_expr" x ]
    ;
    value e_sig_item =
      fun
      [ SgVal _ s t -> <:expr< MLast.SgVal $ln ()$ $e_string s$ $e_type t$ >>
      | x -> not_impl "e_sig_item" x ]
    ;
    value e_module_type mt =
      let ln = ln () in
      loop mt where rec loop =
        fun
        [ MtUid _ s -> <:expr< MLast.MtUid $ln$ $e_string s$ >>
        | x -> not_impl "e_module_type" x ]
    ;
    value rec e_str_item si =
      let ln = ln () in
      loop si where rec loop =
        fun
        [ StDcl _ lsi -> <:expr< MLast.StDcl $ln$ $e_list loop lsi$ >>
        | StExc _ s lt ls ->
            let ls =
              match eval_antiquot_patch expr_eoi ls with
              [ Some (loc, r) -> <:expr< $anti:r$ >>
              | None -> e_list e_string ls ]
            in
            <:expr< MLast.StExc $ln$ $e_string s$ $e_list e_type lt$ $ls$ >>
        | StExp _ e -> <:expr< MLast.StExp $ln$ $e_expr e$ >>
        | StExt _ s t ls ->
            let ls = e_list e_string ls in
            <:expr< MLast.StExt $ln$ $e_string s$ $e_type t$ $ls$ >>
        | StInc _ me -> <:expr< MLast.StInc $ln$ $e_module_expr me$ >>
        | StMod _ rf lsme ->
            let lsme =
              e_list
                (fun (s, me) -> <:expr< ($e_string s$, $e_module_expr me$) >>)
                lsme
            in
            <:expr< MLast.StMod $ln$ $e_bool rf$ $lsme$ >>
        | StMty _ s mt ->
            <:expr< MLast.StMty $ln$ $e_string s$ $e_module_type mt$ >>
        | StOpn _ sl ->
            <:expr< MLast.StOpn $ln$ $e_list e_string sl$ >>
        | StTyp _ ltd ->
            <:expr< MLast.StTyp $ln$ $e_list e_type_decl ltd$ >>
        | StVal _ rf lpe ->
            let lpe =
              e_list (fun (p, e) -> <:expr< ($e_patt p$, $e_expr e$) >>) lpe
            in
            <:expr< MLast.StVal $ln$ $e_bool rf$ $lpe$ >>
        | x -> not_impl "e_str_item" x ]
    and p_str_item =
      fun
      [ x -> not_impl "p_str_item" x ]
    and e_module_expr me =
      let ln = ln () in
      loop me where rec loop =
        fun
        [ MeAcc _ me1 me2 ->
            <:expr< MLast.MeAcc $ln$ $loop me1$ $loop me2$ >>
        | MeApp _ me1 me2 ->
            <:expr< MLast.MeApp $ln$ $loop me1$ $loop me2$ >>
        | MeFun _ s mt me ->
            let mt = e_module_type mt in
            <:expr< MLast.Mefun $ln$ $e_string s$ $mt$ $loop me$ >>
        | MeStr _ lsi -> <:expr< MLast.MeStr $ln$ $e_list e_str_item lsi$ >>
        | MeTyc _ me mt ->
            let mt = e_module_type mt in
            <:expr< MLast.MeTyc $ln$ $loop me$ $mt$ >>
        | MeUid _ s -> <:expr< MLast.MeUid $ln$ $e_string s$ >> ]
    and p_module_expr =
      fun
      [ x -> not_impl "p_module_expr" x ]
    ;
    value p_sig_item =
      fun
      [ SgVal _ s t -> <:patt< MLast.SgVal _ $p_string s$ $p_type t$ >>
      | x -> not_impl "p_sig_item" x ]
    ;
  end
;

EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
  str_item_eoi: [ [ x = Pcaml.str_item; EOI -> x ] ];
  module_expr_eoi: [ [ x = Pcaml.module_expr; EOI -> x ] ];
  Pcaml.expr:
    [ [ "do"; "{"; el = LIST0 Pcaml.expr SEP ";"; "}" ->
          MLast.ExSeq loc el ] ]
  ;
  Pcaml.expr: LEVEL "simple"
    [ [ s = ANTIQUOT_LOC "anti" -> MLast.ExAnt loc (MLast.ExLid loc s)
      | s = ANTIQUOT_LOC -> MLast.ExAnt loc (MLast.ExStr loc s) ] ]
  ;
  Pcaml.patt: LEVEL "simple"
    [ [ s = ANTIQUOT_LOC "anti" -> MLast.PaAnt loc (MLast.PaLid loc s)
      | s = ANTIQUOT_LOC -> MLast.PaAnt loc (MLast.PaStr loc s) ] ]
  ;
  Pcaml.ctyp: LEVEL "simple"
    [ [ s = ANTIQUOT_LOC -> MLast.TyUid loc s ] ]
  ;
  Pcaml.str_item:
    [ [ s = ANTIQUOT_LOC "exp" ->
          let e = MLast.ExAnt loc (MLast.ExLid loc s) in
          MLast.StExp loc e ] ]
  ;
  Pcaml.module_expr: LEVEL "simple"
    [ [ s = ANTIQUOT_LOC -> MLast.MeUid loc s ] ]
  ;
  Pcaml.module_type: LEVEL "simple"
    [ [ s = ANTIQUOT_LOC -> MLast.MtUid loc s ] ]
  ;
END;

let mod_ident = Grammar.Entry.find Pcaml.str_item "mod_ident" in
EXTEND
  mod_ident: FIRST
    [ [ s = ANTIQUOT_LOC "" -> Obj.repr s ] ]
  ;
END;

value eq_before_colon p e =
  loop 0 where rec loop i =
    if i == String.length e then
      failwith "Internal error in Plexer: incorrect ANTIQUOT"
    else if i == String.length p then e.[i] == ':'
    else if p.[i] == e.[i] then loop (i + 1)
    else False
;

value after_colon e =
  try
    let i = String.index e ':' in
    String.sub e (i + 1) (String.length e - i - 1)
  with
  [ Not_found -> "" ]
;

value check_anti_loc s kind =
  try
    let i = String.index s ':' in
    let (j, len) =
      loop (i + 1) where rec loop j =
        if j = String.length s then (i, 0)
        else
          match s.[j] with
          [ ':' -> (j, j - i - 1)
          | 'a'..'z' | 'A'..'Z' | '0'..'9' -> loop (j + 1)
          | _ -> (i, 0) ]
    in
    if String.sub s (i + 1) len = kind then
      sprintf "%s:%d:%s" (String.sub s 0 i) (j - i)
        (String.sub s (j + 1) (String.length s - j - 1))
    else raise Stream.Failure
  with
  [ Not_found -> raise Stream.Failure ]
;

let lex = Grammar.glexer Pcaml.gram in
lex.Token.tok_match :=
  fun
  [ ("ANTIQUOT_LOC", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm ""
      | _ -> raise Stream.Failure ]
  | ("ANTIQUOT_LOC", "anti") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "anti"
      | _ -> raise Stream.Failure ]
  | ("ANTIQUOT_LOC", "exp") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "exp"
      | _ -> raise Stream.Failure ]
  | ("INT", "") ->
      fun
      [ ("INT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "int"
      | _ -> raise Stream.Failure ]
  | ("FLOAT", "") ->
      fun
      [ ("FLOAT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "flo"
      | _ -> raise Stream.Failure ]
  | ("LIDENT", "") ->
      fun
      [ ("LIDENT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "lid"
      | _ -> raise Stream.Failure ]
  | ("UIDENT", "") ->
      fun
      [ ("UIDENT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "uid"
      | _ -> raise Stream.Failure ]
  | ("STRING", "") ->
      fun
      [ ("STRING", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "str"
      | _ -> raise Stream.Failure ]
  | ("LIST0" | "LIST1", "" | "SEP") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "list"
      | _ -> raise Stream.Failure ]
  | ("OPT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "opt"
      | _ -> raise Stream.Failure ]
  | ("FLAG", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "flag"
      | _ -> raise Stream.Failure ]
  | tok -> Token.default_match tok ]
;

(* reinit the entry functions to take the new tok_match into account *)
Grammar.iter_entry Grammar.reinit_entry_functions
  (Grammar.Entry.obj Pcaml.expr);

value apply_entry e me mp =
  let f s =
    call_with Plexer.dollar_for_antiquot_loc True
      (Grammar.Entry.parse e) (Stream.of_string s)
  in
  let expr s = me (f s) in
  let patt s = mp (f s) in
  Quotation.ExAst (expr, patt)
;

List.iter
  (fun (q, f) -> Quotation.add q f)
  [("expr", apply_entry expr_eoi Meta.e_expr Meta.p_expr);
   ("patt", apply_entry patt_eoi Meta.e_patt Meta.p_patt);
   ("str_item", apply_entry str_item_eoi Meta.e_str_item Meta.p_str_item);
   ("sig_item", apply_entry sig_item_eoi Meta.e_sig_item Meta.p_sig_item);
   ("module_expr",
    apply_entry module_expr_eoi Meta.e_module_expr Meta.p_module_expr)]
;
