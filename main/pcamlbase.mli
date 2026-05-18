(* camlp5r *)

value string_of_loc : string -> int -> int -> int -> string;
   (** [string_of_loc fname line bp ep] returns the location string for
       file [fname] at [line] and between character [bp] and [ep]. *)

value warning : ref (Ploc.t -> string -> unit);

type err_ctx =
  [ Finding
  | Expanding
  | ParsingResult of Ploc.t and string ]
;
exception Qerror of string and string and err_ctx and exn;
