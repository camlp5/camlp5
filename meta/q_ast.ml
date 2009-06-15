(* camlp5r *)
(* $Id: q_ast.ml,v 1.9 2007/08/02 03:25:43 deraugla Exp $ *)

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
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";

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
    value e_type t = 
      let ln = ln () in
      loop t where rec loop =
        fun 
        [ TyAcc _ t1 t2 -> <:expr< MLast.TyAcc $ln$ $loop t1$ $loop t2$ >> 
        | TyAny _ -> <:expr< MLast.TyAny $ln$ >>
        | TyApp _ t1 t2 -> <:expr< MLast.TyApp $ln$ $loop t1$ $loop t2$ >> 
        | TyLid _ s -> <:expr< MLast.TyLid $ln$ $str:s$ >>
        | TyUid _ s -> <:expr< MLast.TyUid $ln$ $str:s$ >>
        | x -> not_impl "e_type" x ]
    ;
    value p_type =
      fun
      [ TyLid _ s -> <:patt< MLast.TyLid _ $str:s$ >>
      | x -> not_impl "p_type" x ]
    ;
    value e_patt p =
      let ln = ln () in
      loop p where rec loop =
        fun
        [ PaAcc _ p1 p2 -> <:expr< MLast.PaAcc $ln$ $loop p1$ $loop p2$ >>
        | PaAnt _ p ->
            match p with
            [ PaLid _ s ->
                match eval_antiquot expr_eoi s with
                [ Some (loc, r) ->
                    let r = <:expr< MLast.PaAnt $ln$ $r$ >> in
                    <:expr< $anti:r$ >>
                | _ -> assert False ]
            | PaStr _ s ->
                match eval_antiquot expr_eoi s with
                [ Some (loc, r) -> <:expr< $anti:r$ >>
                | _ -> assert False ]
            | _ -> assert False ]
        | PaAny _ -> <:expr< MLast.PaAny $ln$ >>
        | PaApp _ p1 p2 -> <:expr< MLast.PaApp $ln$ $loop p1$ $loop p2$ >>
        | PaLid _ s ->
            let s =
              match eval_antiquot expr_eoi s with
              [ Some (loc, r) -> <:expr< $anti:r$ >>
              | _ -> <:expr< $str:s$ >> ]
            in
            <:expr< MLast.PaLid $ln$ $s$ >>
        | PaStr _ s ->
            let s =
              match eval_antiquot expr_eoi s with
              [ Some (loc, r) -> <:expr< $anti:r$ >>
              | None -> <:expr< $str:s$ >> ]
            in
            <:expr< MLast.PaStr $ln$ $s$ >>
        | PaTyc _ p t -> <:expr< MLast.PaTyc $ln$ $loop p$ $e_type t$ >>
        | PaUid _ s ->
            let s =
              match eval_antiquot expr_eoi s with
              [ Some (loc, r) -> <:expr< $anti:r$ >>
              | None -> <:expr< $str:s$ >> ]
            in
            <:expr< MLast.PaUid $ln$ $s$ >>
        | x -> not_impl "e_patt" x ]
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
                | _ -> assert False ]
            | ExStr _ s ->
                match eval_antiquot expr_eoi s with
                [ Some (loc, r) -> <:expr< $anti:r$ >>
                | _ -> assert False ]
            | _ -> assert False ]
        | ExApp _ e1 e2 -> <:expr< MLast.ExApp $ln$ $loop e1$ $loop e2$ >>
        | ExArr _ el ->
            <:expr< MLast.ExArr $ln$ $e_list loop el$ >>
        | ExIfe _ e1 e2 e3 ->
            <:expr< MLast.ExIfe $ln$ $loop e1$ $loop e2$ $loop e3$ >>
        | ExInt _ s k ->
            <:expr< MLast.ExInt $ln$ $str:s$ $str:k$ >>
        | ExFun _ pwel ->
            let pwel =
              e_list
                (fun (p, eo, e) ->
                   <:expr< ($e_patt p$, $e_option loop eo$, $loop e$) >>)
                pwel
            in
            <:expr< MLast.ExFun $ln$ $pwel$ >>
        | ExLet _ rf pel e ->
            let rf = e_bool rf in
            let pel =
              e_list (fun (p, e) -> <:expr< ($e_patt p$, $loop e$) >>) pel
            in
            <:expr< MLast.ExLet $ln$ $rf$ $pel$ $loop e$ >>
        | ExLid _ s ->
            let s =
              match eval_antiquot expr_eoi s with
              [ Some (loc, r) -> <:expr< $anti:r$ >>
              | None -> <:expr< $str:s$ >> ]
            in
            <:expr< MLast.ExLid $ln$ $s$ >>
        | ExStr _ s ->
            let s =
              match eval_antiquot expr_eoi s with
              [ Some (loc, r) -> <:expr< $anti:r$ >>
              | None -> <:expr< $str:s$ >> ]
            in
            <:expr< MLast.ExStr $ln$ $s$ >>
        | ExTup _ [e :: el] ->
            let el = <:expr< [$loop e$ :: $e_list loop el$] >> in
            <:expr< MLast.ExTup $ln$ $el$ >>
        | ExUid _ s ->
            <:expr< MLast.ExUid $ln$ $str:s$ >>
        | x -> not_impl "e_expr" x ]
    ;
    value p_patt =
      fun
      [ x -> not_impl "p_patt" x ]
    ;
    value p_expr =
      fun
      [ x -> not_impl "p_expr" x ]
    ;
    value e_sig_item =
      fun
      [ SgVal _ s t ->
          let s =
            match eval_antiquot expr_eoi s with
            [ Some (loc, r) -> <:expr< $anti:r$ >>
            | None -> <:expr< $str:s$ >> ]
          in
          <:expr< MLast.SgVal $ln ()$ $s$ $e_type t$ >>
      | x -> not_impl "e_sig_item" x ]
    ;
    value p_sig_item =
      fun
      [ SgVal _ s t ->
          let s =
            match eval_antiquot patt_eoi s with
            [ Some (loc, r) -> <:patt< $anti:r$ >>
            | None -> <:patt< $str:s$ >> ]
          in
          <:patt< MLast.SgVal _ $s$ $p_type t$ >>
      | x -> not_impl "p_sig_item" x ]
    ;
  end
;

EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
  Pcaml.expr: LEVEL "simple"
    [ [ s = ANTIQUOT_LOC "anti" -> MLast.ExAnt loc (MLast.ExLid loc s)
      | s = ANTIQUOT_LOC -> MLast.ExAnt loc (MLast.ExStr loc s) ] ]
  ;
  Pcaml.patt: LEVEL "simple"
    [ [ s = ANTIQUOT_LOC "anti" -> MLast.PaAnt loc (MLast.PaLid loc s)
      | s = ANTIQUOT_LOC -> MLast.PaAnt loc (MLast.PaStr loc s) ] ]
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
  | ("LIDENT", "") ->
      fun
      [ ("LIDENT", prm) -> prm
      | ("ANTIQUOT_LOC", prm) -> check_anti_loc prm "lid"
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
   ("sig_item", apply_entry sig_item_eoi Meta.e_sig_item Meta.p_sig_item)]
;
