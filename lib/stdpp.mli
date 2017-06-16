(* camlp5r *)
(* stdpp.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Module deprecated since Camlp5 version 5.00. Use now module Ploc.
    Compatibility assumed. *)

type location = Ploc.t;

(*
exception Exc_located of location and exn;
   Exception removed: replace it with [Ploc.Exc] in your programs.
*)
value raise_with_loc : location -> exn -> 'a;
   (** Use now [Ploc.raise] *)

value make_lined_loc : int -> int -> (int * int) -> location;
   (** Use now [Ploc.make] *)
value make_loc : (int * int) -> location;
   (** Use now [Ploc.make_unlined] *)
value dummy_loc : location;
   (** Use now [Ploc.dummy] *)

value first_pos : location -> int;
   (** Use now [Ploc.first_pos] *)
value last_pos : location -> int;
   (** Use now [Ploc.last_pos] *)
value line_nb : location -> int;
   (** Use now [Ploc.last_pos] *)
value bol_pos : location -> int;
   (** Use now [Ploc.bol_pos] *)

value encl_loc : location -> location -> location;
   (** Use now [Ploc.encl] *)
value shift_loc : int -> location -> location;
   (** Use now [Ploc.shift] *)
value sub_loc : location -> int -> int -> location;
   (** Use now [Ploc.sub] *)
value after_loc : location -> int -> int -> location;
   (** Use now [Ploc.after] *)

value loc_name : ref string;
   (** Use now [Ploc.name] *)
value line_of_loc : string -> location -> (string * int * int * int);
   (** Use now [Ploc.from_file] *)
