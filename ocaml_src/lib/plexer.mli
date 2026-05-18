(* camlp5r *)
(* plexer.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** This module contains the lexer used for ocaml syntax (revised and
    normal). *)

module type LEXER =
  sig
    val gmake : unit -> (string * string) Plexing.lexer;;
    val simplest_raw_strings : bool ref;;
    val dollar_for_antiquotation : bool ref;;
    val specific_space_dot : bool ref;;
    val no_quotations : bool ref;;
    val utf8_lexing : bool ref;;
    val force_antiquot_loc : bool ref;;
  end
;;

module Make (_ : sig  end) : LEXER;;
