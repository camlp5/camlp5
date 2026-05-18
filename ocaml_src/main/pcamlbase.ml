(* camlp5r *)

open Printf;;

let string_of_loc fname line bp ep =
  match Sys.os_type with
    "MacOS" ->
      sprintf "File \"%s\"; line %d; characters %d to %d\n### " fname line bp
        ep
  | _ -> sprintf "File \"%s\", line %d, characters %d-%d:\n" fname line bp ep
;;

let warning_default_function loc txt =
  let (bp, ep) = Ploc.first_pos loc, Ploc.last_pos loc in
  eprintf "<W> loc %d %d: %s\n" bp ep txt; flush stderr
;;

let warning = ref warning_default_function;;

type err_ctx =
    Finding
  | Expanding
  | ParsingResult of Ploc.t * string
;;
exception Qerror of string * string * err_ctx * exn;;
