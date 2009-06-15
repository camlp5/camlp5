(* camlp5r *)
(* $Id: eprinter.mli,v 1.5 2007/12/07 23:29:04 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(** Extensible printers.

    This module allows creation of printers, apply them and clear them.
    It is also internally used by the [EXTEND_PRINTER] statement. *)

type t 'a = 'abstract;
   (** Printer type, to print values of type "'a". *)

type pr_context = { ind : int; bef : string; aft : string; dang : string };
   (** Printing context.
    - "ind" : the current indendation
    - "bef" : what should be printed before, in the same line
    - "aft" : what should be printed after, in the same line
    - "dang" : the dangling token to know whether parentheses are necessary *)

value make : string -> t 'a;
   (** Builds a printer. The string parameter is used in error messages.
       The printer is created empty and can be extended with the
       [EXTEND_PRINTER] statement. *)

value apply : t 'a -> pr_context -> 'a -> string;
   (** Applies a printer, returning the printed string of the parameter. *)
value apply_level : t 'a -> string -> pr_context -> 'a -> string;
   (** Applies a printer at some specific level. Raises [Failure] if the
       given level does not exist. *)

value clear : t 'a -> unit;
   (** Clears a printer, removing all its levels and rules. *)
value print : t 'a -> unit;
   (** Print printer patterns, in the order they are recorded, for
       debugging purposes. *)

value empty_pc : pr_context;
   (** Empty printer context, equal to:
       [{ind = 0; bef = ""; aft = ""; dang = ""}] *)

(**/**)

(* for system use *)

type position =
  [ First
  | Last
  | Before of string
  | After of string
  | Level of string ]
;

type pr_fun 'a = pr_context -> 'a -> string;

type pr_rule 'a =
  Extfun.t 'a (pr_fun 'a -> pr_fun 'a -> pr_context -> string)
;

value extend :
  t 'a -> option position ->
    list (option string * pr_rule 'a -> pr_rule 'a) -> unit;
