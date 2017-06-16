(* camlp5r *)
(* stdpp.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Module deprecated since Camlp5 version 5.00. Use now module Ploc.
    Compatibility assumed. *)

type location = Ploc.t;;

(*
exception Exc_located of location and exn;
   Exception removed: replace it with [Ploc.Exc] in your programs.
*)
val raise_with_loc : location -> exn -> 'a;;
   (** Use now [Ploc.raise] *)

val make_lined_loc : int -> int -> int * int -> location;;
   (** Use now [Ploc.make] *)
val make_loc : int * int -> location;;
   (** Use now [Ploc.make_unlined] *)
val dummy_loc : location;;
   (** Use now [Ploc.dummy] *)

val first_pos : location -> int;;
   (** Use now [Ploc.first_pos] *)
val last_pos : location -> int;;
   (** Use now [Ploc.last_pos] *)
val line_nb : location -> int;;
   (** Use now [Ploc.last_pos] *)
val bol_pos : location -> int;;
   (** Use now [Ploc.bol_pos] *)

val encl_loc : location -> location -> location;;
   (** Use now [Ploc.encl] *)
val shift_loc : int -> location -> location;;
   (** Use now [Ploc.shift] *)
val sub_loc : location -> int -> int -> location;;
   (** Use now [Ploc.sub] *)
val after_loc : location -> int -> int -> location;;
   (** Use now [Ploc.after] *)

val loc_name : string ref;;
   (** Use now [Ploc.name] *)
val line_of_loc : string -> location -> string * int * int * int;;
   (** Use now [Ploc.from_file] *)
