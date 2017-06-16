(* camlp5r *)
(* eprinter.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Extensible printers.

    This module allows creation of printers, apply them and clear them.
    It is also used by the [EXTEND_PRINTER] and [pprintf] statements,
    added by the [pa_extprint.cmo] parsing kit. *)

type t 'a = 'abstract;
   (** Printer type, to print values of type "'a". *)

type pr_context =
  Pprintf.pr_context ==
    { ind : int; bef : string; aft : string; dang : string }
;

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

(**/**)

(* for system use *)

type position =
  [ First
  | Last
  | Before of string
  | After of string
  | Level of string ]
;

type pr_fun 'a = Pprintf.pr_fun 'a;

type pr_rule 'a =
  Extfun.t 'a (pr_fun 'a -> pr_fun 'a -> pr_context -> string)
;

value extend :
  t 'a -> option position ->
    list (option string * pr_rule 'a -> pr_rule 'a) -> unit;
