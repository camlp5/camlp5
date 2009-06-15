(* camlp5r *)
(* $Id: ast2pt.mli,v 1.6 2007/09/01 19:42:28 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(** Conversion between Camlp5 AST into OCaml AST *)

value interf : string -> list MLast.sig_item -> Parsetree.signature;
   (** [interf fname ast] return the OCaml equivalent AST of an
       interface (mli file), [fname] being the input file name. *)
value implem : string -> list MLast.str_item -> Parsetree.structure;
   (** [implem fname ast] return the OCaml equivalent AST of an
       implementation (ml file), [fname] being the input file name. *)
value phrase : MLast.str_item -> Parsetree.toplevel_phrase;
   (** [phrase sil] return the OCaml equivalent AST of a toplevel phrase. *)

value mkloc : Ploc.t -> Location.t;
   (** Convert a Camlp5 location into a OCaml location. *)

value fast : ref bool;
   (** Flag to generate fast (unsafe) access to arrays. Default: False. *)
value no_constructors_arity : ref bool;
   (** Flag to generate nodes telling that constructor arity is not taken
       into account in the AST (e.g. True for normal syntax, False for
       revised syntax). Default: False. *)
