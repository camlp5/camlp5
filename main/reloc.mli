(* camlp4r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: reloc.mli,v 1.1 2007/07/11 09:46:18 deraugla Exp $ *)

value patt : (MLast.loc -> MLast.loc) -> int -> MLast.patt -> MLast.patt;
value expr : (MLast.loc -> MLast.loc) -> int -> MLast.expr -> MLast.expr;
