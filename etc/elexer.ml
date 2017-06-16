(* camlp5r *)
(* elexer.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* lexer written with extensible grammars; experimental *)

#load "pa_extend.cmo";

open Versdep;

value lexlex cs = (cs, fun i -> Plexing.make_loc (i, i + 1));

value next_char s i =
  if i = String.length s then invalid_arg "Elexer.next_char"
  else if s.[i] = '\\' then
    if i + 1 = String.length s then ('\\', i + 1)
    else
      match s.[i+1] with
      [ '0'..'9' ->
          if i + 3 < String.length s then
            let c =
              100 * (Char.code s.[i+1] - Char.code '0') +
              10 * (Char.code s.[i+2] - Char.code '0') +
              Char.code s.[i+3] - Char.code '0'
            in
            (Char.chr c, i + 4)
          else ('\\', i + 1)
      | c -> failwith (Printf.sprintf "not impl \\%c\n" c) ]
  else (s.[i], i + 1)
;

type orc =
  [ Chr of char
  | Rng of char and char ]
;

value make_or_chars s =
  loop 0 where rec loop i =
    if i = String.length s then []
    else
      let (c, i) = next_char s i in
      let (p, i) =
        if i < String.length s - 2 && s.[i] = '.' && s.[i+1] = '.' then
          let (c2, i) = next_char s (i + 2) in
          (Rng c c2, i)
        else
          (Chr c, i)
      in
      [p :: loop i]
;

value tok_match =
  fun
  [ ("", prm) ->
      match String.length prm with
      [ 0 -> fun c -> String.make 1 c
      | 1 ->
          let d = prm.[0] in
          fun c -> if c = d then prm else raise Stream.Failure
      | n ->
          let orc = make_or_chars prm in
          fun c ->
            loop orc where rec loop =
              fun
              [ [] -> raise Stream.Failure
              | [Chr d :: orc] ->
                  if c = d then String.make 1 c
                  else loop orc
              | [Rng d e :: orc] ->
                  if c >= d && c <= e then String.make 1 c
                  else loop orc ] ]
  | ("ANY", "") -> fun c -> String.make 1 c
  | _ -> failwith "tok_match 3" ]
;

value lexlex_text (con, prm) =
  if con = "" then "'" ^ String.escaped prm ^ "'"
  else if prm = "" then con
  else con ^ " '" ^ String.escaped prm ^ "'"
;

value glexlex =
  {Plexing.tok_func = lexlex;
   Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
   Plexing.tok_match = tok_match;
   Plexing.tok_text = lexlex_text;
   Plexing.tok_comm = None}
;

module Gram =
  Grammar.GMake (struct type te = char; value lexer = glexlex; end)
;

value gkwd_table = ref (Hashtbl.create 1);
value keyword_or_lident id =
  try ("", Hashtbl.find gkwd_table.val id) with
  [ Not_found -> ("LIDENT", id) ]
;
value keyword_or_uident id =
  try ("", Hashtbl.find gkwd_table.val id) with
  [ Not_found -> ("UIDENT", id) ]
;

value implode l =
  let s = string_create (List.length l) in
  loop 0 l where rec loop i =
    fun
    [ [c :: l] -> do { String.unsafe_set s i c; loop (i + 1) l }
    | [] -> s ]
;

value check_char =
  Gram.Entry.of_parser "check_char"
    (fun strm__ ->
       match Stream.npeek 2 strm__ with
       [ [_; '''] -> ()
       | _ -> raise Stream.Failure ])
;

value invalid_char c =
  raise (Stream.Error ("invalid character: " ^ String.escaped c))
;

value next_token = Gram.Entry.create "lex";

GEXTEND Gram
  GLOBAL: next_token;
  next_token:
    [ [ "\n\r\t "; t = SELF -> t
      | "("; "*"; _ = comment; t = SELF -> t
      | "(" -> (("", "("), loc)
      | t = next_token_after_spaces -> (t, loc)
      | c = ANY -> invalid_char c
      | -> (("EOI", ""), loc) ] ]
  ;
  comment:
    [ [ "*"; ")" -> ()
      | "("; "*"; SELF; SELF -> ()
      | ANY; SELF -> () ] ]
  ;
  next_token_after_spaces:
    [ [ c = "A..Z"; s = ident -> keyword_or_uident (implode [c.[0] :: s])
      | c = "a..z_"; s = ident -> keyword_or_lident (implode [c.[0] :: s])
      | c = "0..9"; (con, cl) = number -> (con, implode [c.[0] :: cl])
      | "\""; s = string -> ("STRING", implode s)
      | "'"; "\\"; c = ANY; s = char -> ("CHAR", implode ['\\'; c.[0] :: s])
      | "'"; _ = check_char; c = ANY; "'" -> ("CHAR", c)
      | "'" -> ("", "'")
      | "`" -> ("", "`")
      | ";" -> ("", ";")
      | "#" -> ("", "#")
      | ")" -> ("", ")")
      | "[" -> ("", "[")
      | "["; ":" -> ("", "[:")
      | ":" -> ("", ":")
      | ":"; ":" -> ("", "::")
      | ":"; "=" -> ("", ":=")
      | ":"; "]" -> ("", ":]")
      | "]" -> ("", "]")
      | "{" -> ("", "{")
      | "}" -> ("", "}")
      | "|" -> ("", "|")
      | "|"; "|" -> ("", "||")
      | "&"; "&" -> ("", "&&")
      | "^" -> ("", "^")
      | "@" -> ("", "@")
      | "+" -> ("", "+")
      | "-" -> ("", "-")
      | "-"; ">" -> ("", "->")
      | "*" -> ("", "*")
      | "/" -> ("", "/")
      | "=" -> ("", "=")
      | "="; "=" -> ("", "==")
      | "<"; t = less -> t
      | "<"; ">" -> ("", "<>")
      | "<"; "=" -> ("", "<=")
      | ">" -> ("", ">")
      | ">"; "=" -> ("", ">=")
      | "$" -> ("", "$")
      | "!" -> ("", "!")
      | "!"; "=" -> ("", "!=")
      | "?" -> ("", "?")
      | "?"; "=" -> ("", "?=")
      | "," -> ("", ",")
      | "." -> ("", ".")
      | "."; "." -> ("", "..")
      | "\\"; i = ident3 -> ("LIDENT", implode i) ] ]
  ;
  ident:
    [ [ c = "A..Za..z0..9_'\128..\255"; s = SELF -> [c.[0] :: s]
      | -> [] ] ]
  ;
  ident3:
    [ [ c = "0..9A..Za..z_!%&*+-./:<=>?@^|~'$\128..\255"; s = SELF ->
          [c.[0] :: s]
      | -> [] ] ]
  ;
  string:
    [ [ "\"" -> []
      | "\\"; c = ANY; s = SELF -> ['\\'; c.[0] :: s]
      | c = ANY; s = SELF -> [c.[0] :: s] ] ]
  ;
  char:
    [ [ "\'" -> []
      | c = ANY; s = SELF -> [c.[0] :: s] ] ]
  ;
  number:
    [ [ -> ("INT", [])
      | c = "0..9"; (con, cl) = SELF -> (con, [c.[0] :: cl])
      | "."; d = decimal_part -> ("FLOAT", ['.' :: d]) ] ]
  ;
  decimal_part:
    [ [ -> []
      | c = "0..9"; s = SELF -> [c.[0] :: s] ] ]
  ;
  less:
    [ [ ":"; s = ident; "<"; q = quotation ->
          ("QUOTATION", implode (s @ [':' :: q]))
      | -> ("", "<") ] ]
  ;
  quotation:
    [ [ ">"; ">" -> []
      | c = ANY; s = SELF -> [c.[0] :: s] ] ]
  ;
END;

value locerr () = invalid_arg "Lexer: location function";
value loct_create () = (ref (Array.create 1024 None), ref False);
value loct_func (loct, ov) i =
  match
    if i < 0 || i >= Array.length loct.val then
      if ov.val then Some Ploc.dummy else None
    else Array.unsafe_get loct.val i
  with
  [ Some loc -> loc
  | _ -> locerr () ]
;
value loct_add (loct, ov) i loc =
  if i >= Array.length loct.val then
    let new_tmax = Array.length loct.val * 2 in
    if new_tmax < Sys.max_array_length then do {
      let new_loct = Array.create new_tmax None in
      Array.blit loct.val 0 new_loct 0 (Array.length loct.val);
      loct.val := new_loct;
      loct.val.(i) := Some loc
    }
    else ov.val := True
  else loct.val.(i) := Some loc
;

value next_token_loc kwd_table (cs, pb) =
  Ploc.call_with gkwd_table kwd_table (Gram.Entry.parse next_token) pb
;

value func kwd_table cs =
  let loct = loct_create () in
  let pb = Gram.parsable cs in
  let ts =
    Stream.from
      (fun i -> do {
         let (tok, loc) = next_token_loc kwd_table (cs, pb) in
         loct_add loct i loc;
         Some tok
       })
  in
  (ts, loct_func loct)
;

value using_token kwd_table (p_con, p_prm) =
  match p_con with
  [ "" ->
      if not (Hashtbl.mem kwd_table p_prm) then
        Hashtbl.add kwd_table p_prm p_prm
      else ()
  | _ -> () ]
;

value gmake () =
  let kwd_table = Hashtbl.create 301 in
  {tok_func = func kwd_table;
   tok_using = using_token kwd_table;
   tok_removing _ = ();
   Plexing.tok_match = Plexing.default_match;
   Plexing.tok_text = Plexing.lexer_text; tok_comm = None}
;
