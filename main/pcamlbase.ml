(* camlp5r *)

open Printf;

value string_of_loc fname line bp ep =
  match Sys.os_type with
  [ "MacOS" ->
      sprintf "File \"%s\"; line %d; characters %d to %d\n### " fname line
        bp ep
  | _ ->
      sprintf "File \"%s\", line %d, characters %d-%d:\n" fname line bp ep ]
;

value warning_default_function loc txt = do {
  let (bp, ep) = (Ploc.first_pos loc, Ploc.last_pos loc) in
  eprintf "<W> loc %d %d: %s\n" bp ep txt;
  flush stderr
};

value warning = ref warning_default_function;

type err_ctx =
  [ Finding
  | Expanding
  | ParsingResult of Ploc.t and string ]
;
exception Qerror of string and string and err_ctx and exn;
