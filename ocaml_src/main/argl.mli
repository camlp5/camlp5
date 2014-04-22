(* camlp5r *)
(* argl.mli,v *)

val usage :
  (string * Arg.spec * string) list -> (string * Arg.spec * string) list ->
    unit;;

val parse :
  (string * Arg.spec * string) list -> (string -> unit) -> string list ->
    string list;;
