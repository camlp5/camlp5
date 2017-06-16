(* camlp5r *)
(* eprinter.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Extensible printers.

    This module allows creation of printers, apply them and clear them.
    It is also used by the [EXTEND_PRINTER] and [pprintf] statements,
    added by the [pa_extprint.cmo] parsing kit. *)

type 'a t;;
   (** Printer type, to print values of type "'a". *)

type pr_context =
  Pprintf.pr_context =
    { ind : int; bef : string; aft : string; dang : string }
;;

val make : string -> 'a t;;
   (** Builds a printer. The string parameter is used in error messages.
       The printer is created empty and can be extended with the
       [EXTEND_PRINTER] statement. *)

val apply : 'a t -> pr_context -> 'a -> string;;
   (** Applies a printer, returning the printed string of the parameter. *)
val apply_level : 'a t -> string -> pr_context -> 'a -> string;;
   (** Applies a printer at some specific level. Raises [Failure] if the
       given level does not exist. *)

val clear : 'a t -> unit;;
   (** Clears a printer, removing all its levels and rules. *)
val print : 'a t -> unit;;
   (** Print printer patterns, in the order they are recorded, for
       debugging purposes. *)

(**/**)

(* for system use *)

type position =
    First
  | Last
  | Before of string
  | After of string
  | Level of string
;;

type 'a pr_fun = 'a Pprintf.pr_fun;;

type 'a pr_rule =
  ('a, 'a pr_fun -> 'a pr_fun -> pr_context -> string) Extfun.t
;;

val extend :
  'a t -> position option ->
    (string option * ('a pr_rule -> 'a pr_rule)) list -> unit;;
