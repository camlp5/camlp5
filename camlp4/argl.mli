(* camlp4r *)
(* $Id$ *)

value usage :
  list (string * Arg.spec * string) -> list (string * Arg.spec * string) ->
    unit;

value parse :
  list (string * Arg.spec * string) -> (string -> unit) -> list string ->
    list string;
