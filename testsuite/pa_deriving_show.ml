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

ef_str_item.val :=
  extfun ef_str_item.val with [
    <:str_item< type $tp:tyname$ $list:params$ = $tk$ [@@deriving show;] >> as z -> z
  ]
;
