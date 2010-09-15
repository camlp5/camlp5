(* camlp5r *)
(* $Id: argl.mli,v 6.1 2010/09/15 16:00:24 deraugla Exp $ *)

value usage :
  list (string * Arg.spec * string) -> list (string * Arg.spec * string) ->
    unit;

value parse :
  list (string * Arg.spec * string) -> (string -> unit) -> list string ->
    list string;
