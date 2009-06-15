(* camlp5r *)
(* $Id: ast2pt.mli,v 1.4 2007/08/23 08:32:35 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

value interf : string -> list MLast.sig_item -> Parsetree.signature;
value implem : string -> list MLast.str_item -> Parsetree.structure;
value phrase : MLast.str_item -> Parsetree.toplevel_phrase;

value mkloc : Stdpp.location -> Location.t;

value fast : ref bool;
value no_constructors_arity : ref bool;
