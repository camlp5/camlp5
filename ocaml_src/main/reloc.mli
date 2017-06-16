(* camlp5r *)
(* reloc.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

val expr : (MLast.loc -> MLast.loc) -> int -> MLast.expr -> MLast.expr;;
val patt : (MLast.loc -> MLast.loc) -> int -> MLast.patt -> MLast.patt;;

(* Equality over syntax trees *)

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
