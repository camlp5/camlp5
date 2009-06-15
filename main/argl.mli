(* camlp5r *)
(* $Id: argl.mli,v 1.2 2007/07/11 12:01:39 deraugla Exp $ *)

value usage :
  list (string * Arg.spec * string) -> list (string * Arg.spec * string) ->
    unit;

value parse :
  list (string * Arg.spec * string) -> (string -> unit) -> list string ->
    list string;
