(* camlp5r *)
(* prtools.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type pr_context =
  Pprintf.pr_context =
    { ind : int; bef : string; aft : string; dang : string }
;;

type 'a pr_fun = 'a Pprintf.pr_fun;;

(* comments *)

val comm_bef : int -> MLast.loc -> string;;
   (** [comm_bef ind loc] get the comment from the source just before the
       given location [loc]. May be reindented using [ind]. Returns the
       empty string if no comment found. *)

(* meta functions to treat lists *)

val hlist : 'a pr_fun -> 'a list pr_fun;;
   (** horizontal list
       [hlist elem pc e] returns the horizontally pretty printed string
       of a list of elements; elements are separated with spaces.
       The list is displayed in one only line. If this function is called
       in the context of the [horiz] function of the function [horiz_vertic]
       of the module Printing, and if the line overflows or contains newlines,
       the function fails (the exception is catched by [horiz_vertic] for
       a vertical pretty print). *)
val hlist2 : 'a pr_fun -> 'a pr_fun -> 'a list pr_fun;;
   (** horizontal list with different function from 2nd element on *)
val hlistl : 'a pr_fun -> 'a pr_fun -> 'a list pr_fun;;
   (** horizontal list with different function for the last element *)

val vlist : 'a pr_fun -> 'a list pr_fun;;
   (** vertical list
       [vlist elem pc e] returns the vertically pretty printed string
       of a list of elements; elements are separated with newlines and
       indentations. *)
val vlist2 : 'a pr_fun -> 'a pr_fun -> 'a list pr_fun;;
   (** vertical list with different function from 2nd element on. *)
val vlist3 : ('a * bool) pr_fun -> ('a * bool) pr_fun -> 'a list pr_fun;;
   (** vertical list with different function from 2nd element on, the
       boolean value being True if it is the last element of the list. *)
val vlistl : 'a pr_fun -> 'a pr_fun -> 'a list pr_fun;;
   (** vertical list with different function for the last element *)

val vlistf : (pr_context -> string) list pr_fun;;
   (** [vlistf pc fl] acts like [vlist] except that the list is a
       list of functions returning the pretty printed string. *)

val plist : 'a pr_fun -> int -> ('a * string) list pr_fun;;
   (** paragraph list
       [plist elem sh pc el] returns the pretty printed string of a list
       of elements with separators. The elements are printed horizontally
       as far as possible. When an element does not fit on the line, a
       newline is added and the element is displayed in the next line with
       an indentation of [sh]. [elem] is the function to print elements,
       [el] a list of pairs (element * separator) (the last separator is
       ignored). *)
val plistb : 'a pr_fun -> int -> ('a * string) list pr_fun;;
   (** paragraph list with possible cut already after the beginner
       [plist elem sh pc el] returns the pretty printed string of
       the list of elements, like with [plist] but the value of
       [pc.bef] corresponds to an element already printed, as it were
       on the list. Therefore, if the first element of [el] does not fit
       in the line, a newline and a tabulation is added after [pc.bef]. *)
val plistl : 'a pr_fun -> 'a pr_fun -> int -> ('a * string) list pr_fun;;
   (** paragraph list with a different function for the last element *)

val plistf : int -> ((pr_context -> string) * string) list pr_fun;;
   (** [plistf sh pc fl] acts like [plist] except that the list is a
       list of functions returning the pretty printed string. *)
val plistbf : int -> ((pr_context -> string) * string) list pr_fun;;
   (** [plistbf sh pc fl] acts like [plistb] except that the list is a
       list of functions returning the pretty printed string. *)

val hvlistl : 'a pr_fun -> 'a pr_fun -> 'a list pr_fun;;
   (** applies [hlistl] if the context is horizontal; else applies [vlistl] *)

(* miscellaneous *)

val tab : int -> string;;

val expand_module_prefix :
  string -> (MLast.patt * 'a) list -> (MLast.patt * 'a) list ->
    (MLast.patt * 'a) list;;

val do_split_or_patterns_with_bindings :
  (MLast.patt * 'a * 'b) list -> (MLast.patt * 'a * 'b) list;;

val record_without_with :
  Ploc.t -> MLast.expr -> (MLast.patt * MLast.expr) list ->
    MLast.expr option;;

val no_constructors_arity : bool ref;;
   (** Flag to generate nodes telling that constructor arity is not taken
       into account in the AST (e.g. True for normal syntax, False for
       revised syntax). Default: False. *)
