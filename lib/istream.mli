(* camlp5r *)
(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*         Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt       *)
(*                                                                        *)
(*   Copyright 1997 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Istreams and parsers. *)

type t 'a = 'b;
(** The type of streams holding values of type ['a]. *)

exception Failure;
(** Raised by parsers when none of the first components of the stream
   patterns is accepted. *)

exception Error of string;
(** Raised by parsers when the first component of a stream pattern is
   accepted, but one of the following components is rejected. *)


(** {1 Istream builders} *)

value from : (int → option α) → t α;
(** [Istream.from f] returns a stream built from the function [f].
   To create a new stream element, the function [f] is called with
   the current stream count. The user function [f] must return either
   [Some <value>] for a value or [None] to specify the end of the
   stream.

   Do note that the indices passed to [f] may not start at [0] in the
   general case. For example, [[< '0; '1; Istream.from f >]] would call
   [f] the first time with count [2].
*)

value of_list : list α → t α;
(** Return the stream holding the elements of the list in the same
   order. *)

value of_string : string → t char;
(** Return the stream of the characters of the string parameter. *)

value of_bytes : bytes → t char;
(** Return the stream of the characters of the bytes parameter.
    @since 4.02.0 *)

value of_channel : in_channel → t char;
(** Return the stream of the characters read from the input channel. *)


(** {1 Istream iterator} *)

value iter : (α → unit) → t α → unit;
(** [Istream.iter f s] scans the whole stream s, applying function [f]
   in turn to each stream element encountered. *)


(** {1 Predefined parsers} *)

value next : t α → α;
(** Return the first element of the stream and remove it from the
   stream.
   @raise Istream.Failure if the stream is empty. *)

value empty : t α → unit;
(** Return [()] if the stream is empty, else raise {!Istream.Failure}. *)


(** {1 Useful functions} *)

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

(* The following is for system use only. Do not call directly. *)

value iapp : t α → t α → t α;
value icons : α → t α → t α;
value ising : α → t α;

value lapp : (unit → t α) → t α → t α;
value lcons : (unit → α) → t α → t α;
value lsing : (unit → α) → t α;

value sempty : t α;
value slazy : (unit → t α) → t α;

value dump : (α → unit) → t α → unit;
