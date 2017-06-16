(* camlp5r *)
(* prtools.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type pr_context =
  Pprintf.pr_context ==
    { ind : int; bef : string; aft : string; dang : string }
;

type pr_fun 'a = Pprintf.pr_fun 'a;

(* comments *)

value comm_bef : int -> MLast.loc -> string;
   (** [comm_bef ind loc] get the comment from the source just before the
       given location [loc]. May be reindented using [ind]. Returns the
       empty string if no comment found. *)

(* meta functions to treat lists *)

value hlist : pr_fun 'a -> pr_fun (list 'a);
   (** horizontal list
       [hlist elem pc e] returns the horizontally pretty printed string
       of a list of elements; elements are separated with spaces.
       The list is displayed in one only line. If this function is called
       in the context of the [horiz] function of the function [horiz_vertic]
       of the module Printing, and if the line overflows or contains newlines,
       the function fails (the exception is catched by [horiz_vertic] for
       a vertical pretty print). *)
value hlist2 : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);
   (** horizontal list with different function from 2nd element on *)
value hlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);
   (** horizontal list with different function for the last element *)

value vlist : pr_fun 'a -> pr_fun (list 'a);
   (** vertical list
       [vlist elem pc e] returns the vertically pretty printed string
       of a list of elements; elements are separated with newlines and
       indentations. *)
value vlist2 : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);
   (** vertical list with different function from 2nd element on. *)
value vlist3 : pr_fun ('a * bool) -> pr_fun ('a * bool) -> pr_fun (list 'a);
   (** vertical list with different function from 2nd element on, the
       boolean value being True if it is the last element of the list. *)
value vlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);
   (** vertical list with different function for the last element *)

value vlistf : pr_fun (list (pr_context -> string));
   (** [vlistf pc fl] acts like [vlist] except that the list is a
       list of functions returning the pretty printed string. *)

value plist : pr_fun 'a -> int -> pr_fun (list ('a * string));
   (** paragraph list
       [plist elem sh pc el] returns the pretty printed string of a list
       of elements with separators. The elements are printed horizontally
       as far as possible. When an element does not fit on the line, a
       newline is added and the element is displayed in the next line with
       an indentation of [sh]. [elem] is the function to print elements,
       [el] a list of pairs (element * separator) (the last separator is
       ignored). *)
value plistb : pr_fun 'a -> int -> pr_fun (list ('a * string));
   (** paragraph list with possible cut already after the beginner
       [plist elem sh pc el] returns the pretty printed string of
       the list of elements, like with [plist] but the value of
       [pc.bef] corresponds to an element already printed, as it were
       on the list. Therefore, if the first element of [el] does not fit
       in the line, a newline and a tabulation is added after [pc.bef]. *)
value plistl : pr_fun 'a -> pr_fun 'a -> int -> pr_fun (list ('a * string));
   (** paragraph list with a different function for the last element *)

value plistf : int -> pr_fun (list (pr_context -> string * string));
   (** [plistf sh pc fl] acts like [plist] except that the list is a
       list of functions returning the pretty printed string. *)
value plistbf : int -> pr_fun (list (pr_context -> string * string));
   (** [plistbf sh pc fl] acts like [plistb] except that the list is a
       list of functions returning the pretty printed string. *)

value hvlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);
   (** applies [hlistl] if the context is horizontal; else applies [vlistl] *)

(* miscellaneous *)

value tab : int -> string;

value expand_module_prefix :
  string -> list (MLast.patt * 'a) -> list (MLast.patt * 'a) ->
    list (MLast.patt * 'a);

value do_split_or_patterns_with_bindings :
  list (MLast.patt * 'a * 'b) -> list (MLast.patt * 'a * 'b);

value record_without_with :
  Ploc.t -> MLast.expr -> list (MLast.patt * MLast.expr) -> option MLast.expr;

value no_constructors_arity : ref bool;
   (** Flag to generate nodes telling that constructor arity is not taken
       into account in the AST (e.g. True for normal syntax, False for
       revised syntax). Default: False. *)
