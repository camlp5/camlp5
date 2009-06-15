(* camlp5r *)
(* $Id: q_ast.ml,v 1.27 2007/09/02 19:53:33 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

value not_impl f x =
let _ = do { Printf.eprintf "not_impl\n"; flush stderr; } in
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

value eval_anti entry loc typ str =
  let r =
    call_with Plexer.force_antiquot False
      (Grammar.Entry.parse entry) (Stream.of_string str)
  in
  let loc =
    let sh =
      if typ = "" then String.length "$"
      else
        String.length "$" + String.length typ + String.length ":"
    in
    let len = String.length str in
    Ploc.sub loc sh len
  in
  (loc, r)
;

value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value ctyp_eoi = Grammar.Entry.create Pcaml.gram "type";
value str_item_eoi = Grammar.Entry.create Pcaml.gram "str_item";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
value module_expr_eoi = Grammar.Entry.create Pcaml.gram "module_expr";

(* upper bound of tags of all syntax tree nodes *)
value anti_tag = 100;

value make_anti loc t s = do {
  let r = Obj.new_block anti_tag 3 in
  Obj.set_field r 0 (Obj.repr (loc : Ploc.t));
  Obj.set_field r 1 (Obj.repr (t : string));
  Obj.set_field r 2 (Obj.repr (s : string));
  Obj.magic r
};

value get_anti v =
  if Obj.tag (Obj.repr v) = anti_tag && Obj.size (Obj.repr v) = 3 then
    let loc : Ploc.t = Obj.magic (Obj.field (Obj.repr v) 0) in
    let t : string = Obj.magic (Obj.field (Obj.repr v) 1) in
    let s : string = Obj.magic (Obj.field (Obj.repr v) 2) in
    Some (loc, t, s)
  else None
;

module Meta =
  struct
    open MLast;
    value loc = Ploc.dummy;
    value ln () = <:expr< $lid:Ploc.name.val$ >>;
    value e_list elem el =
      loop el where rec loop =
        fun
        [ [] -> <:expr< [] >>
        | [e :: el] -> <:expr< [$elem e$ :: $loop el$] >> ]
    ;
    value e_option elem =
       fun
       [ None -> <:expr< None >>
       | Some e -> <:expr< Some $elem e$ >> ]
    ;
    value e_bool b = if b then <:expr< True >> else <:expr< False >>;
    value e_ctyp t = 
(*
      let ln = ln () in
*)
      loop t where rec loop =
        fun 
        [ (* TyAcc _ t1 t2 -> <:expr< MLast.TyAcc $ln$ $loop t1$ $loop t2$ >> 
        | TyAny _ -> <:expr< MLast.TyAny $ln$ >>
        | TyApp _ t1 t2 -> <:expr< MLast.TyApp $ln$ $loop t1$ $loop t2$ >> 
        | TyLid _ s -> <:expr< MLast.TyLid $ln$ $e_string s$ >>
        | TyQuo _ s -> <:expr< MLast.TyQuo $ln$ $e_string s$ >>
        | TyRec _ lld ->
            let lld =
              e_vala
                (e_list
                   (fun (loc, lab, mf, t) ->
                      <:expr< ($ln$, $str:lab$, $e_bool mf$, $loop t$) >>))
                lld
            in
            <:expr< MLast.TyRec $ln$ $lld$ >>
        | TyUid _ s -> <:expr< MLast.TyUid $ln$ $e_string s$ >>
        | *) x -> not_impl "e_ctyp" x ]
    ;
    value p_ctyp =
      fun
      [ (* TyLid _ s -> <:patt< MLast.TyLid _ $p_string s$ >>
      | *) x -> not_impl "p_ctyp" x ]
    ;
(*
    value e_type_decl =
      fun
      [ x -> not_impl "e_type_decl" x ]
    ;
*)
    value e_patt p =
      let ln = ln () in
      loop p where rec loop p =
        match get_anti p with
        [ Some (loc, typ, str) ->
            let r =
              let (loc, r) = eval_anti expr_eoi loc typ str in
              <:expr< $anti:r$ >>
            in
            match typ with
            [ ""  -> r
            | "chr" -> <:expr< MLast.PaChr $ln$ $r$ >>
            | "lid" -> <:expr< MLast.PaLid $ln$ $r$ >>
            | "uid" -> <:expr< MLast.PaUid $ln$ $r$ >>
            | x -> not_impl ("e_patt anti " ^ x) 0 ]
        | None ->
            match p with
            [ PaAcc _ p1 p2 -> <:expr< MLast.PaAcc $ln$ $loop p1$ $loop p2$ >>
            | PaAli _ p1 p2 -> <:expr< MLast.PaAli $ln$ $loop p1$ $loop p2$ >>
            | PaAny _ -> <:expr< MLast.PaAny $ln$ >>
            | PaApp _ p1 p2 -> <:expr< MLast.PaApp $ln$ $loop p1$ $loop p2$ >>
            | PaChr _ s -> <:expr< MLast.PaChr $ln$ $str:s$ >>
(*
            | PaInt _ s k -> <:expr< MLast.PaInt $ln$ $e_string s$ $str:k$ >>
            | PaFlo _ s -> <:expr< MLast.PaFlo $ln$ $e_string s$ >>
*)
            | PaLid _ s -> <:expr< MLast.PaLid $ln$ $str:s$ >>
            | PaOrp _ p1 p2 -> <:expr< MLast.PaOrp $ln$ $loop p1$ $loop p2$ >>
            | PaRng _ p1 p2 -> <:expr< MLast.PaRng $ln$ $loop p1$ $loop p2$ >>
(*
            | PaStr _ s -> <:expr< MLast.PaStr $ln$ $e_string s$ >>
            | PaTyc _ p t -> <:expr< MLast.PaTyc $ln$ $loop p$ $e_ctyp t$ >>
*)
            | PaUid _ s -> <:expr< MLast.PaUid $ln$ $str:s$ >>
            | x -> not_impl "e_patt" x ] ]
    ;
    value p_patt =
      loop where rec loop p =
        match get_anti p with
        [ Some (loc, typ, str) ->
            let r =
              let (loc, r) = eval_anti patt_eoi loc typ str in
              <:patt< $anti:r$ >>
            in
            match typ with
            [ "" -> r
            | "chr" -> <:patt< MLast.PaChr _ $r$ >>
            | "lid" -> <:patt< MLast.PaLid _ $r$ >>
            | x -> not_impl ("p_patt anti " ^ x) 0 ]
        | None ->
            match p with
            [ PaAli _ p1 p2 -> <:patt< MLast.PaAli _ $loop p1$ $loop p2$ >>
            | x -> not_impl "p_patt" x ] ]
    ;
    value rec e_expr e =
      let ln = ln () in
      loop e where rec loop e =
        match get_anti e with
        [ Some (loc, typ, str) ->
            let r =
              let (loc, r) = eval_anti expr_eoi loc typ str in
              <:expr< $anti:r$ >>
            in
            match typ with
            [ "" -> r
            | "anti" -> <:expr< MLast.ExAnt $ln$ $r$ >>
            | "chr" -> <:expr< MLast.ExChr $ln$ $r$ >>
            | "int" -> <:expr< MLast.ExInt $ln$ $r$ "" >>
            | "lid" -> <:expr< MLast.ExLid $ln$ $r$ >>
            | "str" -> <:expr< MLast.ExStr $ln$ $r$ >>
            | "uid" -> <:expr< MLast.ExUid $ln$ $r$ >>
            | x -> not_impl ("e_expr anti " ^ x) 0 ]
        | None ->
            match e with
            [ ExAcc _ e1 e2 -> <:expr< MLast.ExAcc $ln$ $loop e1$ $loop e2$ >>
            | ExApp _ e1 e2 -> <:expr< MLast.ExApp $ln$ $loop e1$ $loop e2$ >>
(*
            | ExArr _ el ->
                <:expr< MLast.ExArr $ln$ $e_list loop el$ >>
            | ExIfe _ e1 e2 e3 ->
                <:expr< MLast.ExIfe $ln$ $loop e1$ $loop e2$ $loop e3$ >>
*)
            | ExInt _ s k -> <:expr< MLast.ExInt $ln$ $str:s$ $str:k$ >>
(*
            | ExFlo _ s -> <:expr< MLast.ExFlo $ln$ $e_string s$ >>
*)
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
            | ExLid _ s -> <:expr< MLast.ExLid $ln$ $str:s$ >>
(*
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
*)
            | ExStr _ s -> <:expr< MLast.ExStr $ln$ $str:s$ >>
            | ExTup _ [e :: el] ->
                let el = <:expr< [$loop e$ :: $e_list loop el$] >> in
                <:expr< MLast.ExTup $ln$ $el$ >>
(*
            | ExTyc _ e t -> <:expr< MLast.ExTyc $ln$ $loop e$ $e_ctyp t$ >>
*)
            | ExUid _ s -> <:expr< MLast.ExUid $ln$ $str:s$ >>
            | x -> not_impl "e_expr" x ] ]
    ;
    value p_expr e =
      loop e where rec loop e =
        match get_anti e with
        [ Some (loc, typ, str) ->
            let r =
              let (loc, r) = eval_anti patt_eoi loc typ str in
              <:patt< $anti:r$ >>
            in
            match typ with
            [ "" -> r
            | "lid" -> <:patt< MLast.ExLid _ $r$ >>
            | "uid" -> <:patt< MLast.ExUid _ $r$ >>
            | x -> not_impl ("p_expr anti " ^ x) 0 ]
        | None ->
            match e with
            [ ExAcc _ e1 e2 -> <:patt< MLast.ExAcc _ $loop e1$ $loop e2$ >>
            | ExApp _ e1 e2 -> <:patt< MLast.ExApp _ $loop e1$ $loop e2$ >>
(*
            | ExIfe _ e1 e2 e3 ->
                <:patt< MLast.ExIfe _ $loop e1$ $loop e2$ $loop e3$ >>
            | ExInt _ s k -> <:patt< MLast.ExInt _ $p_string s$ $str:k$ >>
            | ExFlo _ s -> <:patt< MLast.ExFlo _ $p_string s$ >>
            | ExLet _ rf lpe e ->
                let rf = p_vala p_bool rf in
                let lpe =
                  p_list_p (fun (p, e) -> <:patt< ($p_patt p$, $loop e$) >>) lpe
                in
                <:patt< MLast.ExLet _ $rf$ $lpe$ $loop e$ >>
            | ExLid _ s -> <:patt< MLast.ExLid _ $p_string s$ >>
*)
            | ExUid _ s -> <:patt< MLast.ExUid _ $str:s$ >>
            | x -> not_impl "p_expr" x ] ]
    ;
    value e_sig_item =
      fun
      [ (* SgVal _ s t -> <:expr< MLast.SgVal $ln ()$ $e_string s$ $e_ctyp t$ >>
      | *) x -> not_impl "e_sig_item" x ]
    ;
(*
    value e_module_type mt =
      let ln = ln () in
      loop mt where rec loop =
        fun
        [ MtUid _ s -> <:expr< MLast.MtUid $ln$ $e_string s$ >>
        | x -> not_impl "e_module_type" x ]
    ;
*)
    value rec e_str_item si =
(*
      let ln = ln () in
*)
      loop si where rec loop =
        fun
        [ (* StDcl _ lsi -> <:expr< MLast.StDcl $ln$ $e_list loop lsi$ >>
        | StExc _ s lt ls ->
            let ls =
              match eval_antiquot_patch expr_eoi ls with
              [ Some (loc, r) -> <:expr< $anti:r$ >>
              | None -> e_list e_string ls ]
            in
            <:expr< MLast.StExc $ln$ $e_string s$ $e_list e_ctyp lt$ $ls$ >>
        | StExp _ e -> <:expr< MLast.StExp $ln$ $e_expr e$ >>
        | StExt _ s t ls ->
            let ls = e_list e_string ls in
            <:expr< MLast.StExt $ln$ $e_string s$ $e_ctyp t$ $ls$ >>
        | StInc _ me -> <:expr< MLast.StInc $ln$ $e_module_expr me$ >>
        | StMod _ rf lsme ->
            let lsme =
              e_list
                (fun (s, me) -> <:expr< ($e_string s$, $e_module_expr me$) >>)
                lsme
            in
            <:expr< MLast.StMod $ln$ $e_vala e_bool rf$ $lsme$ >>
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
            <:expr< MLast.StVal $ln$ $e_vala e_bool rf$ $lpe$ >>
        | *) x -> not_impl "e_str_item" x ]
    and p_str_item =
      fun
      [ x -> not_impl "p_str_item" x ]
    and e_module_expr me =
(*
      let ln = ln () in
*)
      loop me where rec loop =
        fun
        [ (* MeAcc _ me1 me2 ->
            <:expr< MLast.MeAcc $ln$ $loop me1$ $loop me2$ >>
        | MeApp _ me1 me2 ->
            <:expr< MLast.MeApp $ln$ $loop me1$ $loop me2$ >>
        | MeFun _ s mt me ->
            let mt = e_module_type mt in
            <:expr< MLast.MeFun $ln$ $e_string s$ $mt$ $loop me$ >>
        | MeStr _ lsi -> <:expr< MLast.MeStr $ln$ $e_list e_str_item lsi$ >>
        | MeTyc _ me mt ->
            let mt = e_module_type mt in
            <:expr< MLast.MeTyc $ln$ $loop me$ $mt$ >>
        | MeUid _ s -> <:expr< MLast.MeUid $ln$ $e_string s$ >>
        | *) x -> not_impl "e_module_expr" x ]
    and p_module_expr =
      fun
      [ x -> not_impl "p_module_expr" x ]
    ;
    value p_sig_item =
      fun
      [ (* SgVal _ s t -> <:patt< MLast.SgVal _ $p_string s$ $p_ctyp t$ >>
      | *) x -> not_impl "p_sig_item" x ]
    ;
  end
;

let ipatt = Grammar.Entry.find Pcaml.expr "ipatt" in
EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  ctyp_eoi: [ [ x = Pcaml.ctyp; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
  str_item_eoi: [ [ x = Pcaml.str_item; EOI -> x ] ];
  module_expr_eoi: [ [ x = Pcaml.module_expr; EOI -> x ] ];
  Pcaml.expr: LAST
    [ [ s = ANTIQUOT "" -> make_anti loc "" s
      | s = ANTIQUOT "anti" -> make_anti loc "anti" s
      | s = ANTIQUOT "chr" -> make_anti loc "chr" s
      | s = ANTIQUOT "int" -> make_anti loc "int" s
      | s = ANTIQUOT "lid" -> make_anti loc "lid" s
      | s = ANTIQUOT "str" -> make_anti loc "str" s
      | s = ANTIQUOT "uid" -> make_anti loc "uid" s ] ]
  ;
  Pcaml.patt: LAST
    [ [ s = ANTIQUOT "" -> make_anti loc "" s
      | s = ANTIQUOT "chr" -> make_anti loc "chr" s
      | s = ANTIQUOT "lid" -> make_anti loc "lid" s
      | s = ANTIQUOT "uid" -> make_anti loc "uid" s ] ]
  ;
  ipatt: LAST
    [ [ s = ANTIQUOT "lid" -> make_anti loc "lid" s ] ]
  ;
(*
  Pcaml.ctyp: LAST
    [ [ s = ANTIQUOT_LOC -> MLast.TyUid loc s ] ]
  ;
  Pcaml.str_item: LAST
    [ [ s = ANTIQUOT_LOC "exp" ->
          let e = MLast.ExAnt loc (MLast.ExLid loc s) in
          MLast.StExp loc e ] ]
  ;
  Pcaml.module_expr: LAST
    [ [ s = ANTIQUOT_LOC -> MLast.MeUid loc s ] ]
  ;
  Pcaml.module_type: LAST
    [ [ s = ANTIQUOT_LOC -> MLast.MtUid loc s ] ]
  ;
*)
END;

(*
let mod_ident = Grammar.Entry.find Pcaml.str_item "mod_ident" in
EXTEND
  mod_ident: FIRST
    [ [ s = ANTIQUOT_LOC "" -> Obj.repr s ] ]
  ;
END;

value check_anti_loc s kind =
  try
    let i = String.index s ':' in
    let (j, len) =
      loop (i + 1) where rec loop j =
        if j = String.length s then (i, 0)
        else
          match s.[j] with
          [ ':' -> (j, j - i - 1)
          | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> loop (j + 1)
          | _ -> (i, 0) ]
    in
    if String.sub s (i + 1) len = kind then
      sprintf "%s:%d:%s" (String.sub s 0 i) (j - i)
        (String.sub s (j + 1) (String.length s - j - 1))
    else raise Stream.Failure
  with
  [ Not_found -> raise Stream.Failure ]
;

value check_anti s kind =
  if String.length s > String.length kind then
    if String.sub s 0 (String.length kind + 1) = kind ^ ":" then s
    else raise Stream.Failure
  else raise Stream.Failure
;

let lex = Grammar.glexer Pcaml.gram in
lex.Plexing.tok_match :=
  fun
  [ (*("ANTIQUOT_LOC", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm ""
      | _ -> raise Stream.Failure ]
  | ("ANTIQUOT_LOC", p_prm) ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm p_prm
      | _ -> raise Stream.Failure ]
  | ("INT", "") ->
      fun
      [ ("INT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "a_int"
      | _ -> raise Stream.Failure ]
  | ("FLOAT", "") ->
      fun
      [ ("FLOAT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "a_flo"
      | _ -> raise Stream.Failure ]
  | ("LIDENT", "") ->
      fun
      [ ("LIDENT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "a_lid"
      | _ -> raise Stream.Failure ]
  | ("UIDENT", "") ->
      fun
      [ ("UIDENT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "a_uid"
      | _ -> raise Stream.Failure ]
  | ("STRING", "") ->
      fun
      [ ("STRING", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "a_str"
      | _ -> raise Stream.Failure ]
  | ("LIST", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "a_list"
      | _ -> raise Stream.Failure ]
  | ("OPT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "a_opt"
      | _ -> raise Stream.Failure ]
  | *) ("FLAG", prm) ->
let _ = do { Printf.eprintf "yop %s\n" prm; flush stderr; } in
      fun
      [ ("ANTIQUOT", prm) ->
let _ = do { Printf.eprintf "yep %s\n" prm; flush stderr; } in
          check_anti prm "flag"
      | _ -> raise Stream.Failure ]
  | tok -> Plexing.default_match tok ]
;

(* reinit the entry functions to take the new tok_match into account *)
Grammar.iter_entry Grammar.reinit_entry_functions
  (Grammar.Entry.obj Pcaml.expr);

*)

value apply_entry e me mp =
  let f s =
    call_with Plexer.force_antiquot True
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
   ("ctyp", apply_entry ctyp_eoi Meta.e_ctyp Meta.p_ctyp);
   ("str_item", apply_entry str_item_eoi Meta.e_str_item Meta.p_str_item);
   ("sig_item", apply_entry sig_item_eoi Meta.e_sig_item Meta.p_sig_item);
   ("module_expr",
    apply_entry module_expr_eoi Meta.e_module_expr Meta.p_module_expr)]
;
