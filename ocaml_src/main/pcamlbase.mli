(* camlp5r *)

val string_of_loc : string -> int -> int -> int -> string;;
   (** [string_of_loc fname line bp ep] returns the location string for
       file [fname] at [line] and between character [bp] and [ep]. *)

val warning : (Ploc.t -> string -> unit) ref;;

type err_ctx =
    Finding
  | Expanding
  | ParsingResult of Ploc.t * string
;;
exception Qerror of string * string * err_ctx * exn;;
