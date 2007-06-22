(* camlp4r *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Pcaml.NewPrinters;

type pr_gfun 'a 'b = pr_ctx -> string -> 'a -> 'b -> string;

value shi : pr_ctx -> int -> pr_ctx;
value tab : pr_ctx -> string;

value hlist : pr_fun 'a -> pr_fun (list 'a);
   (** horizontal list
       [hlist elem ctx b e k] returns the horizontally pretty printed
       string of a list of elements; elements are separated with spaces.
       The list is displayed in one only line. If this function is called
       in the context of the [horiz] function of the function [horiz_vertic]
       of the module Printing, and if the line overflows or contains newlines,
       the function fails (the exception is catched by [horiz_vertic] for
       a vertical pretty print). *)
value hlist2 : pr_gfun 'a 'b -> pr_gfun 'a 'b -> pr_gfun (list 'a) ('b * 'b);
   (** horizontal list with different function from 2nd element on *)
value hlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);
   (** horizontal list with different function for the last element *)

value vlist : pr_fun 'a -> pr_fun (list 'a);
   (** vertical list
       [vlist elem ctx b e k] returns the vertically pretty printed
       string of a list of elements; elements are separated with newlines
       and indentations. *)
value vlist2 : pr_gfun 'a 'b -> pr_gfun 'a 'b -> pr_gfun (list 'a) ('b * 'b);
   (** vertical list with different function from 2nd element on *)
value vlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);
   (** vertical list with different function for the last element *)

value plist : pr_fun 'a -> int -> pr_fun (list ('a * string));
   (** paragraph list
       [plist elem sh ctx b el k] returns the pretty printed string of
       a list of elements with separators. The elements are printed
       horizontally as far as possible. When an element does not fit
       on the line, a newline is added and the element is displayed
       in the next line with an indentation of [sh]. [elem] is the
       function to print elements, [ctx] is the context, [b] the
       beginning of the line, [el] a list of pairs (element * separator)
       (the last separator is ignored), and [k] the end of the line *)
value plistb : pr_fun 'a -> int -> pr_fun (list ('a * string));
   (** paragraph list with possible cut already after the beginner
       [plist elem sh ctx b el k] returns the pretty printed string of
       the list of elements, like with [plist] but the [b] variable
       correspond to an element already printed. Therefore, if the
       first element of [el] does not fit in the line, a newline and
       a tabulation is added after [b]. *)
value plistl : pr_fun 'a -> pr_fun 'a -> int -> pr_fun (list ('a * string));
   (** paragraph list with a different function for the last element *)

value flatten_sequence : MLast.expr -> option (list MLast.expr);
   (** [flatten_sequence e]. If [e] is an expression representing a sequence,
       return the list of expressions of the sequence. If some of these
       expressions are already sequences, they are expanded in the list.
       If that list contains expressions of the form let..in sequence, this
       sub-sequence is also flattened with the let..in spplies only to the
       first expression of the sequence. If [e] is a let..in sequence, it
       works the same way. If [e] is not a sequence nor a let..in sequence,
       return None. *)

value source : ref string;
   (** The initial source string, which must be set by the pretty printing
       kit. Used by [comm_bef] below. *)
value comm_bef : pr_ctx -> MLast.loc -> string;
   (** [comm_bef ctx loc] get the comment from the source (in the global
       variable [source] just before the given location [loc]. May be
       reindented using the printing context [ctx]. No comment returns
       the empty string. *)
