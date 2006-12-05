(* camlp4r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2006 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

value fast : ref bool;
value no_constructors_arity : ref bool;
value mkloc : Token.location -> Location.t;
value long_id_of_string_list : Token.location -> list string -> Longident.t;

value str_item : MLast.str_item -> Parsetree.structure -> Parsetree.structure;
value interf : string -> list MLast.sig_item -> Parsetree.signature;
value implem : string -> list MLast.str_item -> Parsetree.structure;
value phrase : MLast.str_item -> Parsetree.toplevel_phrase;
