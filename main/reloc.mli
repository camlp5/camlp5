(* camlp5r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp5                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: reloc.mli,v 1.4 2007/08/26 20:05:38 deraugla Exp $ *)

value expr : (MLast.loc -> MLast.loc) -> int -> MLast.expr -> MLast.expr;
value patt : (MLast.loc -> MLast.loc) -> int -> MLast.patt -> MLast.patt;

(* Equality over syntax trees *)

value eq_expr : MLast.expr -> MLast.expr -> bool;
value eq_patt : MLast.patt -> MLast.patt -> bool;
value eq_ctyp : MLast.ctyp -> MLast.ctyp -> bool;
value eq_str_item : MLast.str_item -> MLast.str_item -> bool;
value eq_sig_item : MLast.sig_item -> MLast.sig_item -> bool;
value eq_module_expr : MLast.module_expr -> MLast.module_expr -> bool;
value eq_module_type : MLast.module_type -> MLast.module_type -> bool;
value eq_class_sig_item :
  MLast.class_sig_item -> MLast.class_sig_item -> bool;
value eq_class_str_item :
  MLast.class_str_item -> MLast.class_str_item -> bool;
value eq_class_type : MLast.class_type -> MLast.class_type -> bool;
value eq_class_expr : MLast.class_expr -> MLast.class_expr -> bool;
