(* camlp5r *)
(* camlp5_top.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "q_MLast.cmo";

open Parsetree;
open Lexing;
open Versdep;

value highlight_locations lb loc1 loc2 =
  let loc1 = (Ploc.first_pos loc1, Ploc.last_pos loc1) in
  try do {
    let pos0 = -lb.lex_abs_pos in
    if pos0 < 0 then raise Exit else ();
    let pos_at_bol = ref 0 in
    print_string "Toplevel input:\n# ";
    for pos = 0 to lb.lex_buffer_len - pos0 - 1 do {
      let c = string_get lb.lex_buffer (pos+pos0) in
      if c = '\n' then do {
        if pos_at_bol.val <= fst loc1 && snd loc1 <= pos then do {
          print_string "\n  ";
          for i = pos_at_bol.val to fst loc1 - 1 do { print_char ' ' };
          for i = fst loc1 to snd loc1 - 1 do { print_char '^' };
          print_char '\n'
        }
        else if pos_at_bol.val <= fst loc1 && fst loc1 < pos then do {
          print_char '\r';
          print_char (if pos_at_bol.val = 0 then '#' else ' ');
          print_char ' ';
          for i = pos_at_bol.val to fst loc1 - 1 do { print_char '.' };
          print_char '\n'
        }
        else if pos_at_bol.val <= snd loc1 && snd loc1 < pos then do {
          for i = pos - 1 downto snd loc1 do { print_string "\008.\008" };
          print_char '\n'
        }
        else print_char '\n';
        pos_at_bol.val := pos + 1;
        if pos < lb.lex_buffer_len - pos0 - 1 then print_string "  " else ()
      }
      else print_char c;
    };
    flush stdout
  }
  with
  [ Exit -> () ]
;

value print_location lb loc =
  if List.mem Toploop.input_name.val [""; "//toplevel//"] then
    highlight_locations lb loc (-1, -1)
  else
    IFDEF OCAML_VERSION <= OCAML_2_99 THEN
      Toploop.print_location (Ast2pt.mkloc loc)
    ELSE do {
      Format.fprintf Format.err_formatter "%s%!"
        (Pcaml.string_of_loc Toploop.input_name.val (Ploc.line_nb loc)
	   (Ploc.first_pos loc - Ploc.bol_pos loc)
	   (Ploc.last_pos loc - Ploc.bol_pos loc));
    }
    END
;

value wrap f shfn lb =
  let cs =
    let shift = shfn lb in
    Stream.from
      (fun i ->
         if i < shift then Some ' '
         else do {
           while
             lb.lex_curr_pos >= lb.lex_buffer_len &&
             not lb.lex_eof_reached
           do {
             lb.refill_buff lb
           };
           if lb.lex_curr_pos >= lb.lex_buffer_len then None
           else do {
             let c = string_get lb.lex_buffer lb.lex_curr_pos in
             lb.lex_curr_pos := lb.lex_curr_pos + 1;
             Some c
           }
         })
  in
  try f cs with
  [ Ploc.Exc _ (Sys.Break as x) -> raise x
  | End_of_file as x -> raise x
  | x -> do {
      let x =
        match x with
        [ Ploc.Exc loc x -> do { print_location lb loc; x }
        | x -> x ]
      in
      match x with
      [ Stream.Failure | Stream.Error _ -> Pcaml.sync.val cs
      | _ -> () ];
      Format.open_hovbox 0;
      Pcaml.report_error x;
      Format.close_box ();
      Format.print_newline ();
      raise Exit
    } ]
;

value first_phrase = ref True;

value toplevel_phrase cs = do {
  if Sys.interactive.val && first_phrase.val then do {
    first_phrase.val := False;
    Printf.eprintf "\tCamlp5 parsing version %s\n\n" Pcaml.version;
    flush stderr
  }
  else ();
  Pcaml.input_file.val := Toploop.input_name.val;
  match Grammar.Entry.parse Pcaml.top_phrase cs with
  [ Some phr -> Ast2pt.phrase phr
  | None -> raise End_of_file ]
};

Pcaml.add_directive "load"
  (fun
   [ Some <:expr< $str:s$ >> ->
       IFDEF OCAML_VERSION <= OCAML_2_99 THEN Topdirs.dir_load s
       ELSE Topdirs.dir_load Format.std_formatter s END
   | Some _ | None -> raise Not_found ]);

Pcaml.add_directive "directory"
  (fun
   [ Some <:expr< $str:s$ >> -> Topdirs.dir_directory s
   | Some _ | None -> raise Not_found ]);

value use_file cs = do {
  let v = Pcaml.input_file.val in
  Pcaml.input_file.val := Toploop.input_name.val;
  let restore () = Pcaml.input_file.val := v in
  try do {
    let (pl0, eoi) =
      (* directives at beginning of the file are executed at once,
         to allow them to do possible syntax extensions *)
      loop () where rec loop () =
        let (pl, stopped_at_directive) =
          Grammar.Entry.parse Pcaml.use_file cs
        in
        if stopped_at_directive then
          match pl with
          [ [<:str_item< # $s$ $opt:eo$ >>] ->
              let ok =
                try do {
                  let f = Pcaml.find_directive s in
                  f eo;
                  True
                }
                with
                [ Not_found -> False ]
              in
              if ok then loop () else (pl, False)
          | _ -> (pl, False) ]
        else (pl, True)
    in
    let pl =
      if eoi then []
      else
        loop () where rec loop () =
          (* in the middle of the file, directives are treated by ocaml *)
          let (pl, stopped_at_directive) =
            Grammar.Entry.parse Pcaml.use_file cs
          in
          if stopped_at_directive then pl @ loop () else pl
    in
    let r = pl0 @ pl in
    let r = List.map Ast2pt.phrase r in
    restore ();
    r
  }
  with e ->
    do { restore (); raise e }
};

Toploop.parse_toplevel_phrase.val :=
  wrap toplevel_phrase (fun _ -> 0)
;

Toploop.parse_use_file.val :=
  wrap use_file (fun lb -> lb.lex_curr_pos - lb.lex_start_pos)
;

Pcaml.warning.val :=
  fun loc txt ->
    IFDEF OCAML_VERSION <= OCAML_2_00 THEN
      Toploop.print_warning (Ast2pt.mkloc loc) txt
    ELSIFDEF OCAML_VERSION <= OCAML_2_99 THEN
      Toploop.print_warning (Ast2pt.mkloc loc) (Warnings.Other txt)
    ELSE
      Toploop.print_warning (Ast2pt.mkloc loc) Format.err_formatter
        (IFDEF OCAML_VERSION <= OCAML_3_08_4 THEN Warnings.Other txt
         ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Warnings.Camlp4 txt
         ELSE Warnings.Preprocessor txt END)
    END;
