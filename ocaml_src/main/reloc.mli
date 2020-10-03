(* camlp5r *)
(* reloc.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

val expr : (MLast.loc -> MLast.loc) -> int -> MLast.expr -> MLast.expr;;
val longid : (MLast.loc -> MLast.loc) -> int -> MLast.longid -> MLast.longid;;
val longid_lident :
  (MLast.loc -> MLast.loc) -> int -> MLast.longid_lident ->
    MLast.longid_lident;;
val patt : (MLast.loc -> MLast.loc) -> int -> MLast.patt -> MLast.patt;;
val ctyp : (MLast.loc -> MLast.loc) -> int -> MLast.ctyp -> MLast.ctyp;;
val sig_item :
  (MLast.loc -> MLast.loc) -> int -> MLast.sig_item -> MLast.sig_item;;
val str_item :
  (MLast.loc -> MLast.loc) -> int -> MLast.str_item -> MLast.str_item;;

(* Equality over syntax trees *)

val eq_longid : MLast.longid -> MLast.longid -> bool;;
val eq_longid_lident : MLast.longid_lident -> MLast.longid_lident -> bool;;
val eq_expr : MLast.expr -> MLast.expr -> bool;;
val eq_patt : MLast.patt -> MLast.patt -> bool;;
val eq_ctyp : MLast.ctyp -> MLast.ctyp -> bool;;
val eq_str_item : MLast.str_item -> MLast.str_item -> bool;;
val eq_sig_item : MLast.sig_item -> MLast.sig_item -> bool;;
val eq_module_expr : MLast.module_expr -> MLast.module_expr -> bool;;
val eq_module_type : MLast.module_type -> MLast.module_type -> bool;;
val eq_class_sig_item : MLast.class_sig_item -> MLast.class_sig_item -> bool;;
val eq_class_str_item : MLast.class_str_item -> MLast.class_str_item -> bool;;
val eq_class_type : MLast.class_type -> MLast.class_type -> bool;;
val eq_class_expr : MLast.class_expr -> MLast.class_expr -> bool;;
