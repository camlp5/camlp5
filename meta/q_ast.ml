(* camlp5r *)
(* $Id: q_ast.ml,v 1.1 2007/07/31 04:55:54 deraugla Exp $ *)

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

module Meta =
  struct
    open MLast;
    value loc = Stdpp.dummy_loc;
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
    value expr_of_type =
      loop where rec loop =
        fun 
        [ TyAcc _ t1 t2 -> <:expr< MLast.TyAcc loc $loop t1$ $loop t2$ >> 
        | TyAny _ -> <:expr< MLast.TyAny loc >>
        | TyApp _ t1 t2 -> <:expr< MLast.TyApp loc $loop t1$ $loop t2$ >> 
        | TyLid _ s -> <:expr< MLast.TyLid loc $str:s$ >>
        | TyUid _ s -> <:expr< MLast.TyUid loc $str:s$ >>
        | x -> not_impl "expr_of_type" x ]
    ;
    value patt_of_type =
      fun
      [ TyLid _ s -> <:patt< MLast.TyLid _ $str:s$ >>
      | x -> not_impl "patt_of_type" x ]
    ;
    value expr_of_patt =
      loop where rec loop =
        fun
        [ PaLid _ s -> <:expr< MLast.PaLid loc $str:s$ >>
        | PaTyc _ p t -> <:expr< MLast.PaTyc loc $loop p$ $expr_of_type t$ >>
        | x -> not_impl "expr_of_patt" x ]
    ;
    value expr_of_expr =
      loop where rec loop =
        fun
        [ ExAcc _ e1 e2 -> <:expr< MLast.ExAcc loc $loop e1$ $loop e2$ >>
        | ExAnt _ <:expr< ("", $e$) >> -> e
        | ExApp _ e1 e2 -> <:expr< MLast.ExApp loc $loop e1$ $loop e2$ >>
        | ExArr _ [ExAnt _ <:expr< ("list", $e$) >>] ->
            <:expr< MLast.ExArr loc $e$ >>
        | ExArr _ el ->
            <:expr< MLast.ExArr loc $expr_of_list loop el$ >>
        | ExIfe _ e1 e2 e3 ->
            <:expr< MLast.ExIfe loc $loop e1$ $loop e2$ $loop e3$ >>
        | ExInt _ s k ->
            <:expr< MLast.ExInt loc $str:s$ $str:k$ >>
        | ExFun _ pwel ->
            let pwel =
              expr_of_list
                (fun (p, eo, e) ->
                   <:expr<
                     ($expr_of_patt p$, $expr_of_option loop eo$, $loop e$)
                   >>)
                pwel
            in
            <:expr< MLast.ExFun loc $pwel$ >>
        | ExLet _ rf [(<:patt< _ >>, ExAnt _ <:expr< ("list", $e1$) >>)] e ->
            let rf = expr_of_bool rf in
            let pel = e1 in
            <:expr< MLast.ExLet loc $rf$ $pel$ $loop e$ >>
        | ExLet _ rf pel e ->
            let rf = expr_of_bool rf in
            let pel =
              expr_of_list
                (fun (p, e) -> <:expr< ($expr_of_patt p$, $loop e$) >>) pel
            in
            <:expr< MLast.ExLet loc $rf$ $pel$ $loop e$ >>
        | ExLid _ s ->
            <:expr< MLast.ExLid loc $str:s$ >>
        | ExUid _ s ->
            <:expr< MLast.ExUid loc $str:s$ >>
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
            <:expr< MLast.SgVal loc $lid:s$ $expr_of_type t$ >>
          else
            <:expr< MLast.SgVal loc $str:s$ $expr_of_type t$ >>
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

value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
  Pcaml.expr: LEVEL "top"
    [ [ "let"; "$"; "list"; ":"; e1 = SELF; "in"; e = SELF ->
          let a = <:expr< ("list", $e1$) >> in
          let pel = [(<:patt< _ >>, <:expr< $anti:a$ >>)] in
          <:expr< let $list:pel$ in $e$ >> ] ]
  ;
  Pcaml.expr: LEVEL "simple"
    [ [ "$:"; e = SELF ->
          let a = <:expr< ("", $e$) >> in
          <:expr< $anti:a$ >>
      | "$"; k = LIDENT; ":"; e = SELF ->
          let a = <:expr< ($str:k$, $e$) >> in
          <:expr< $anti:a$ >> ] ]
  ;
  Pcaml.sig_item:
    [ [ "value"; "$:"; s = LIDENT; ":"; t = Pcaml.ctyp ->
          <:sig_item< value $lid:":" ^ s$ : $t$ >> ] ]
  ;
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
