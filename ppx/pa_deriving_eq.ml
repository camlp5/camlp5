(* camlp5r *)
(* pa_passthru.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";
#load "pa_extfun.cmo";

open Asttools;
open MLast;
open Pa_passthru ;
open Ppxutil ;

ef_str_item.val :=
  extfun ef_str_item.val with [
    <:str_item:< type $_flag:_$ $list:tdl$ >> as z
    when List.exists (fun td -> List.exists is_deriving_show (Pcaml.unvala td.tdAttributes)) tdl ->
    fun arg -> do {
    let f = str_item_gen_show loc arg tdl in
      <:str_item< declare $list:[z ; f ]$ end >>
}
  ]
;

ef_sig_item.val :=
  extfun ef_sig_item.val with [
    <:sig_item:< type $_flag:_$ $list:tdl$ >> as z
    when List.exists (fun td -> List.exists is_deriving_show (Pcaml.unvala td.tdAttributes)) tdl ->
    fun arg -> do {
    let f = sig_item_gen_show loc arg tdl in
      <:sig_item< declare $list:[z ; f ]$ end >>
}
  ]
;


value argle = fun [
  <:expr:< [%show: $type:t$ ] >> as z -> z
]
;

ef_expr.val :=
  extfun ef_expr.val with [
    <:expr:< [%show: $type:t$ ] >> as z ->
      fun arg -> expr_show arg t
  ]
;

