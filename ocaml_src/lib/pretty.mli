(* camlp5r *)
(* pretty.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Pretty printing on strings *)

val horiz_vertic : (unit -> 'a) -> (unit -> 'a) -> 'a;;
  (** [horiz_vertic h v] first calls [h] to print the data horizontally,
      i.e. without newlines. If the displaying contains newlines or if
      its size exceeds the maximum line length (see variable [line_length]
      below), then the function [h] stops and the function [v] is called
      which can print using several lines. *)

val sprintf : ('a, unit, string) format -> 'a;;
  (** [sprintf fmt ...] formats some string like [Printf.sprintf]
      does, except that, if it is called in the context of the *first*
      function of [horiz_vertic] above, it checks whether the resulting
      string has chances to fit in the line. If not, i.e. if it contains
      newlines or if its length is greater than [max_line_length.val],
      the function gives up (raising some internal exception). Otherwise
      the built string is returned.
        [sprintf] behaves like [Printf.sprintf] if it is called in
      the context of the *second* function of [horiz_vertic] or without
      context at all. *)

val line_length : int ref;;
  (** [line_length] is the maximum length (in characters) of the
      line. Default = 78. Can be set to any other value before
      printing. *)

val horizontally : unit -> bool;;
  (** [horizontally ()] returns the fact that the context is an
      horizontal print. *)
