(* camlp5r *)
(* $Id: odyl_main.mli,v 1.2 2007/07/11 12:01:39 deraugla Exp $ *)

exception Error of string and string;

value nolib : ref bool;
value initialized : ref bool;
value path : ref (list string);
value loadfile : string -> unit;
value directory : string -> unit;

value go : ref (unit -> unit);
value name : ref string;
