(* camlp5r *)
(* $Id: q_ast.ml,v 1.4 2007/07/31 23:48:22 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

value not_impl f x =
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  failwith ("q_ast_r.ml: " ^ f ^ ", not impl: " ^ desc)
;

value antiquot_loc k loc =
  let shift_bp =
    if k = "" then String.length "$"
    else String.length "$" + String.length k + String.length ":"
  in
  let shift_ep = String.length "$" in
  Stdpp.make_lined_loc (Stdpp.line_nb loc) (Stdpp.bol_pos loc)
    (Stdpp.first_pos loc + shift_bp, Stdpp.last_pos loc - shift_ep)
;

value after_colon e =
  try
    let i = String.index e ':' in
    String.sub e (i + 1) (String.length e - i - 1)
  with
  [ Not_found -> "" ]
;

value eq_before_colon p e =
  loop 0 where rec loop i =
    if i == String.length e then
      failwith "Internal error in Plexer: incorrect ANTIQUOT"
    else if i == String.length p then e.[i] == ':'
    else if p.[i] == e.[i] then loop (i + 1)
    else False
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

value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
END;

module Meta =
  struct
    open MLast;
    value loc = Stdpp.dummy_loc;
    value ln () = <:expr< $lid:Stdpp.loc_name.val$ >>;
    value rec e_list elem =
      fun
      [ [] -> <:expr< [] >>
      | [e :: el] -> <:expr< [$elem e$ :: $e_list elem el$] >> ]
    ;
    value e_option elem =
      fun
      [ None -> <:expr< None >>
      | Some e -> <:expr< Some $elem e$ >> ]
    ;
    value e_bool b =
      if b then <:expr< True >> else <:expr< False >>
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
        [ PaLid loc s ->
            let a = after_colon s in
            if a = "" then <:expr< MLast.PaLid $ln$ $str:s$ >>
            else
              let r =
                let loc = Stdpp.make_loc (0, String.length a) in
                <:expr< MLast.PaLid $ln$ $lid:a$ >>
              in
              let loc = antiquot_loc "lid" loc in
              <:expr< $anti:r$ >>
        | PaTyc _ p t ->
            <:expr< MLast.PaTyc $ln$ $loop p$ $e_type t$ >>
        | x -> not_impl "e_patt" x ]
    ;
    value e_expr e =
      let ln = ln () in
      loop e where rec loop =
        fun
        [ ExAcc _ e1 e2 -> <:expr< MLast.ExAcc $ln$ $loop e1$ $loop e2$ >>
        | ExAnt _ <:expr< ("", $e$) >> -> e
        | ExApp _ e1 e2 -> <:expr< MLast.ExApp $ln$ $loop e1$ $loop e2$ >>
        | ExArr _ [ExAnt _ <:expr< ("list", $e$) >>] ->
            <:expr< MLast.ExArr $ln$ $e$ >>
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
                   <:expr<
                     ($e_patt p$, $e_option loop eo$, $loop e$)
                   >>)
                pwel
            in
            <:expr< MLast.ExFun $ln$ $pwel$ >>
        | ExLet _ rf [(<:patt< _ >>, ExAnt _ <:expr< ("list", $e1$) >>)] e ->
            let rf = e_bool rf in
            let pel = e1 in
            <:expr< MLast.ExLet $ln$ $rf$ $pel$ $loop e$ >>
        | ExLet _ rf pel e ->
            let rf = e_bool rf in
            let pel =
              e_list
                (fun (p, e) -> <:expr< ($e_patt p$, $loop e$) >>) pel
            in
            <:expr< MLast.ExLet $ln$ $rf$ $pel$ $loop e$ >>
        | ExLid loc s ->
            let a = after_colon s in
            if a = "" then <:expr< MLast.ExLid $ln$ $str:s$ >>
            else
              let r =
                let loc = Stdpp.make_loc (0, String.length a) in
                <:expr< MLast.ExLid $ln$ $lid:a$ >>
              in
              let loc = antiquot_loc "lid" loc in
              <:expr< $anti:r$ >>
        | ExStr loc s ->
            let a = after_colon s in
            if a = "" then <:expr< MLast.ExStr $ln$ $str:s$ >>
            else
              let r =
                let loc = Stdpp.make_loc (0, String.length a) in
                <:expr< MLast.ExStr $ln$ $lid:a$ >>
              in
              let loc = antiquot_loc "str" loc in
              <:expr< $anti:r$ >>
        | ExTup _ el ->
            <:expr< MLast.ExTup $ln$ $e_list loop el$ >>
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
            try
              let i = String.index s ',' in
              let j = String.index_from s (i + 1) ':' in
              let bp = int_of_string (String.sub s 0 i) in
              let ep = int_of_string (String.sub s (i + 1) (j - i - 1)) in
              let s = String.sub s (j + 1) (String.length s - j - 1) in
              let r =
                call_with Plexer.dollar_for_antiquot_loc False
                  (Grammar.Entry.parse expr_eoi) (Stream.of_string s)
              in
              let loc = antiquot_loc "lid" (Stdpp.make_loc (bp, ep)) in
              <:expr< $anti:r$ >>
            with
            [ Not_found | Failure _ -> <:expr< $str:s$ >> ]
          in
          <:expr< MLast.SgVal $ln ()$ $s$ $e_type t$ >>
      | x -> not_impl "e_sig_item" x ]
    ;
    value p_sig_item =
      fun
      [ SgVal _ s t ->
          let s =
            let a = after_colon s in
            if a = "" then <:patt< $str:s$ >> else <:patt< $lid:a$ >>
          in
          <:patt< MLast.SgVal _ $s$ $p_type t$ >>
      | x -> not_impl "p_sig_item" x ]
    ;
  end
;

value check_anti_loc s kind =
  try
    let i = String.index s ':' in
    let j = String.index_from s (i + 1) ':' in
    if String.sub s (i + 1) (j - i - 1) = "lid" then
      String.sub s 0 i ^ String.sub s j (String.length s - j)
    else raise Stream.Failure
  with
  [ Not_found -> raise Stream.Failure ]
;

let lex = Grammar.glexer Pcaml.gram in
lex.Token.tok_match :=
  fun
  [ ("ANTIQUOT", p_prm) ->
      fun
      [ ("ANTIQUOT", prm) when eq_before_colon p_prm prm -> after_colon prm
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
