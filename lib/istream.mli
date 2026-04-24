(* camlp5r *)
(***********************************************************************)
(*                                                                     *)
(*                             Ocaml                                   *)
(*                                                                     *)
(*        Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt     *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(** Streams and parsers. *)

type t α = β;
(** The type of streams holding values of type ['a]. *)

exception Failure;
(** Raised by parsers when none of the first components of the stream
   patterns is accepted. *)

exception Error of string;
(** Raised by parsers when the first component of a stream pattern is
   accepted, but one of the following components is rejected. *)


(** {6 Stream builders}

   Warning: these functions create streams with fast access; it is illegal
   to mix them with streams built with [[< >]]; would raise [Failure]
   when accessing such mixed streams.
*)

value from : (int → option α) → t α;
(** [Stream.from f] returns a stream built from the function [f].
   To create a new stream element, the function [f] is called with
   the current stream count. The user function [f] must return either
   [Some <value>] for a value or [None] to specify the end of the
   stream. *)

value of_list : list α → t α;
(** Return the stream holding the elements of the list in the same
   order. *)

value of_string : string → t char;
(** Return the stream of the characters of the string parameter. *)

value of_channel : in_channel → t char;
(** Return the stream of the characters read from the input channel. *)


(** {6 Stream iterator} *)

value iter : (α → unit) → t α → unit;
(** [Stream.iter f s] scans the whole stream s, applying function [f]
   in turn to each stream element encountered. *)


(** {6 Predefined parsers} *)

value next : t α → α;
(** Return the first element of the stream and remove it from the
   stream. Raise Stream.Failure if the stream is empty. *)

value empty : t α → unit;
(** Return [()] if the stream is empty, else raise [Stream.Failure]. *)


(** {6 Useful functions} *)

value peek : t α → option α;
(** Return [Some] of "the first element" of the stream, or [None] if
   the stream is empty. *)

value junk : t α → unit;
(** Remove the first element of the stream, possibly unfreezing
   it before. *)

value count : t α → int;
(** Return the current count of the stream elements, i.e. the number
   of the stream elements discarded. *)

value npeek : int → t α → list α;
(** [npeek n] returns the list of the [n] first elements of
   the stream, or all its remaining elements if less than [n]
   elements are available. *)

(**/**)

(** {6 For system use only, not for the casual user} *)

value iapp : t α → t α → t α;
value icons : α → t α → t α;
value ising : α → t α;

value lapp : (unit → t α) → t α → t α;
value lcons : (unit → α) → t α → t α;
value lsing : (unit → α) → t α;

value sempty : t α;
value slazy : (unit → t α) → t α;

value dump : (α → unit) → t α → unit;
