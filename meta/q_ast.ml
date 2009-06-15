(* camlp5r *)
(* $Id: q_ast.ml,v 1.2 2007/07/31 14:29:41 deraugla Exp $ *)

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

module Meta =
  struct
    open MLast;
    value loc = Stdpp.dummy_loc;
    value ln () = <:expr< $lid:Stdpp.loc_name.val$ >>;
    value rec expr_of_list elem =
      fun
      [ [] -> <:expr< [] >>
      | [e :: el] -> <:expr< [$elem e$ :: $expr_of_list elem el$] >> ]
    ;
    value expr_of_option elem =
      fun
      [ None -> <:expr< None >>
      | Some e -> <:expr< Some $elem e$ >> ]
    ;
    value expr_of_bool b =
      if b then <:expr< True >> else <:expr< False >>
    ;
    value expr_of_type t = 
      let ln = ln () in
      loop t where rec loop =
        fun 
        [ TyAcc _ t1 t2 -> <:expr< MLast.TyAcc $ln$ $loop t1$ $loop t2$ >> 
        | TyAny _ -> <:expr< MLast.TyAny $ln$ >>
        | TyApp _ t1 t2 -> <:expr< MLast.TyApp $ln$ $loop t1$ $loop t2$ >> 
        | TyLid _ s -> <:expr< MLast.TyLid $ln$ $str:s$ >>
        | TyUid _ s -> <:expr< MLast.TyUid $ln$ $str:s$ >>
        | x -> not_impl "expr_of_type" x ]
    ;
    value patt_of_type =
      fun
      [ TyLid _ s -> <:patt< MLast.TyLid _ $str:s$ >>
      | x -> not_impl "patt_of_type" x ]
    ;
    value expr_of_patt p =
      let ln = ln () in
      loop p where rec loop =
        fun
        [ PaLid _ s -> <:expr< MLast.PaLid $ln$ $str:s$ >>
        | PaTyc _ p t ->
            <:expr< MLast.PaTyc $ln$ $loop p$ $expr_of_type t$ >>
        | x -> not_impl "expr_of_patt" x ]
    ;
    value expr_of_expr e =
      let ln = ln () in
      loop e where rec loop =
        fun
        [ ExAcc _ e1 e2 -> <:expr< MLast.ExAcc $ln$ $loop e1$ $loop e2$ >>
        | ExAnt _ <:expr< ("", $e$) >> -> e
        | ExApp _ e1 e2 -> <:expr< MLast.ExApp $ln$ $loop e1$ $loop e2$ >>
        | ExArr _ [ExAnt _ <:expr< ("list", $e$) >>] ->
            <:expr< MLast.ExArr $ln$ $e$ >>
        | ExArr _ el ->
            <:expr< MLast.ExArr $ln$ $expr_of_list loop el$ >>
        | ExIfe _ e1 e2 e3 ->
            <:expr< MLast.ExIfe $ln$ $loop e1$ $loop e2$ $loop e3$ >>
        | ExInt _ s k ->
            <:expr< MLast.ExInt $ln$ $str:s$ $str:k$ >>
        | ExFun _ pwel ->
            let pwel =
              expr_of_list
                (fun (p, eo, e) ->
                   <:expr<
                     ($expr_of_patt p$, $expr_of_option loop eo$, $loop e$)
                   >>)
                pwel
            in
            <:expr< MLast.ExFun $ln$ $pwel$ >>
        | ExLet _ rf [(<:patt< _ >>, ExAnt _ <:expr< ("list", $e1$) >>)] e ->
            let rf = expr_of_bool rf in
            let pel = e1 in
            <:expr< MLast.ExLet $ln$ $rf$ $pel$ $loop e$ >>
        | ExLet _ rf pel e ->
            let rf = expr_of_bool rf in
            let pel =
              expr_of_list
                (fun (p, e) -> <:expr< ($expr_of_patt p$, $loop e$) >>) pel
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
        | ExUid _ s ->
            <:expr< MLast.ExUid $ln$ $str:s$ >>
        | x -> not_impl "expr_of_expr" x ]
    ;
    value patt_of_patt =
      fun
      [ x -> not_impl "patt_of_patt" x ]
    ;
    value patt_of_expr =
      fun
      [ x -> not_impl "patt_of_expr" x ]
    ;
    value expr_of_sig_item =
      fun
      [ SgVal _ s t ->
          if String.length s > 0 && s.[0] = ':' then
            let s = String.sub s 1 (String.length s - 1) in
            <:expr< MLast.SgVal $ln ()$ $lid:s$ $expr_of_type t$ >>
          else
            <:expr< MLast.SgVal $ln ()$ $str:s$ $expr_of_type t$ >>
      | x -> not_impl "expr_of_sig_item" x ]
    ;
    value patt_of_sig_item =
      fun
      [ SgVal _ s t ->
          if String.length s > 0 && s.[0] = ':' then
            let s = String.sub s 1 (String.length s - 1) in
            <:patt< MLast.SgVal _ $lid:s$ $patt_of_type t$ >>
          else
            <:patt< MLast.SgVal _ $str:s$ $patt_of_type t$ >>
      | x -> not_impl "patt_of_sig_item" x ]
    ;
  end
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
      | ("ANTIQUOT", prm) when eq_before_colon "lid" prm -> prm
      | _ -> raise Stream.Failure ]
  | ("STRING", "") ->
      fun
      [ ("STRING", prm) -> prm
      | ("ANTIQUOT", prm) when eq_before_colon "str" prm -> prm
      | _ -> raise Stream.Failure ]
  | tok -> Token.default_match tok ]
;

Grammar.iter_entry Grammar.reinit_entry_functions
  (Grammar.Entry.obj Pcaml.expr);

Plexer.force_dollar_for_antiquotation.val := True;

value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
END;

value apply_expr_entry =
  let f s = Grammar.Entry.parse expr_eoi (Stream.of_string s) in
  let expr s = Meta.expr_of_expr (f s) in
  let patt s = Meta.patt_of_expr (f s) in
  Quotation.ExAst (expr, patt)
;

value apply_patt_entry =
  let f s = Grammar.Entry.parse patt_eoi (Stream.of_string s) in
  let expr s = Meta.expr_of_patt (f s) in
  let patt s = Meta.patt_of_patt (f s) in
  Quotation.ExAst (expr, patt)
;

value apply_sig_item_entry =
  let f s = Grammar.Entry.parse sig_item_eoi (Stream.of_string s) in
  let expr s = Meta.expr_of_sig_item (f s) in
  let patt s = Meta.patt_of_sig_item (f s) in
  Quotation.ExAst (expr, patt)
;

Quotation.add "expr" apply_expr_entry;
Quotation.add "patt" apply_patt_entry;

Quotation.add "sig_item" apply_sig_item_entry;
