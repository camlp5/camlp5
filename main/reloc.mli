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

(* $Id: reloc.mli,v 1.3 2007/08/21 17:50:22 deraugla Exp $ *)

value patt : (MLast.loc -> MLast.loc) -> int -> MLast.patt -> MLast.patt;
value expr : (MLast.loc -> MLast.loc) -> int -> MLast.expr -> MLast.expr;

value ctyp : (MLast.loc -> MLast.loc) -> int -> MLast.ctyp -> MLast.ctyp;
value sig_item :
  (MLast.loc -> MLast.loc) -> int -> MLast.sig_item -> MLast.sig_item;
value str_item :
  (MLast.loc -> MLast.loc) -> int -> MLast.str_item -> MLast.str_item;
value module_expr :
  (MLast.loc -> MLast.loc) -> int -> MLast.module_expr -> MLast.module_expr;
value module_type :
  (MLast.loc -> MLast.loc) -> int -> MLast.module_type -> MLast.module_type;
value class_sig_item :
  (MLast.loc -> MLast.loc) -> int -> MLast.class_sig_item ->
    MLast.class_sig_item;
value class_str_item :
  (MLast.loc -> MLast.loc) -> int -> MLast.class_str_item ->
    MLast.class_str_item;
value class_expr :
  (MLast.loc -> MLast.loc) -> int -> MLast.class_expr -> MLast.class_expr;
value class_type :
  (MLast.loc -> MLast.loc) -> int -> MLast.class_type -> MLast.class_type;
