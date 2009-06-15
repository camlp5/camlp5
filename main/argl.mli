(* camlp4r *)
(* $Id: argl.mli,v 1.1 2007/07/11 09:46:18 deraugla Exp $ *)

value usage :
  list (string * Arg.spec * string) -> list (string * Arg.spec * string) ->
    unit;

value parse :
  list (string * Arg.spec * string) -> (string -> unit) -> list string ->
    list string;
