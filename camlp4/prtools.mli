(* camlp4r *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Pcaml.NewPrinter;

type pr_gfun 'a 'b = pr_ctx -> string -> 'a -> 'b -> string;

value shi : pr_ctx -> int -> pr_ctx;
value tab : pr_ctx -> string;

value hlist : pr_fun 'a -> pr_fun (list 'a);
   (** horizontal list
       [hlist elem ctx b e k] returns the horizontally pretty printed
       string of a list of elements; elements are separated with spaces.
       The list is displayed in one only line. If this function is called
       in the context of the [horiz] function of the function [horiz_vertic]
       of the module Sformat, and if the line overflows or contains newlines,
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
value plistl : pr_fun 'a -> pr_fun 'a -> int -> pr_fun (list ('a * string));
   (** paragraph list with a different function for the last element *)
