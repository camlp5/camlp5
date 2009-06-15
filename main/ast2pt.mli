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

(* $Id: ast2pt.mli,v 1.3 2007/08/20 09:16:18 deraugla Exp $ *)

value fast : ref bool;
value no_constructors_arity : ref bool;
value mkloc : Stdpp.location -> Location.t;
value long_id_of_string_list : Stdpp.location -> list string -> Longident.t;

value str_item : MLast.str_item -> Parsetree.structure -> Parsetree.structure;
value interf : string -> list MLast.sig_item -> Parsetree.signature;
value implem : string -> list MLast.str_item -> Parsetree.structure;
value phrase : MLast.str_item -> Parsetree.toplevel_phrase;
