(* camlp5r *)
(* $Id: versdep.mli,v 1.2 2010/08/25 15:31:51 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

module Ast2pt :
  sig
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
   end
;

value action_arg : string -> list string -> Arg.spec -> option (list string);
value arg_symbol : Arg.spec -> option (list string);
