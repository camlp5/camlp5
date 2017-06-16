(* camlp5r *)
(* plexer.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_lexer.cmo";

open Versdep;

value no_quotations = ref False;
value error_on_unknown_keywords = ref False;

value dollar_for_antiquotation = ref True;
value specific_space_dot = ref False;
value dot_newline_is = ref ".";

value force_antiquot_loc = ref False;

type context =
  { after_space : mutable bool;
    dollar_for_antiquotation : bool;
    specific_space_dot : bool;
    dot_newline_is : string;
    find_kwd : string -> string;
    line_cnt : int -> char -> unit;
    set_line_nb : unit -> unit;
    make_lined_loc : (int * int) -> string -> Ploc.t }
;

value err ctx loc msg =
  Ploc.raise (ctx.make_lined_loc loc "") (Plexing.Error msg)
;

value keyword_or_error ctx loc s =
  try ("", ctx.find_kwd s) with
  [ Not_found ->
      if error_on_unknown_keywords.val then
        err ctx loc ("illegal token: " ^ s)
      else ("", s) ]
;

value rev_implode l =
  let s = string_create (List.length l) in
  bytes_to_string (loop (string_length s - 1) l) where rec loop i =
    fun
    [ [c :: l] -> do { string_unsafe_set s i c; loop (i - 1) l }
    | [] -> s ]
;

value implode l = rev_implode (List.rev l);

value stream_peek_nth n strm =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some x else None
    | [_ :: l] -> loop (n - 1) l ]
;

value utf8_lexing = ref False;

value greek_tab =
  ["α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ";
   "ο"; "π"; "ρ"; "σ"; "τ"; "υ"; "φ"; "χ"; "ψ"; "ω"]
;

value greek_letter buf strm =
  if utf8_lexing.val then
    match Stream.peek strm with
    [ Some c ->
        if Char.code c >= 128 then
          let x = implode (Stream.npeek 2 strm) in
          if List.mem x greek_tab then do { Stream.junk strm; $add c }
          else raise Stream.Failure
        else raise Stream.Failure
    | None -> raise Stream.Failure ]
  else
    raise Stream.Failure
;

value misc_letter buf strm =
  if utf8_lexing.val then
    match Stream.peek strm with
    [ Some c ->
        if Char.code c >= 128 then
          match implode (Stream.npeek 3 strm) with
          [ "→" | "≤" | "≥" -> raise Stream.Failure
          | _ -> do { Stream.junk strm; $add c } ]
        else raise Stream.Failure
    | None -> raise Stream.Failure ]
  else
    match strm with lexer [ '\128'-'\225' | '\227'-'\255' ]
;

value misc_punct buf strm =
  if utf8_lexing.val then
    match strm with lexer [ '\226' _ _ ]
  else
    match strm with parser []
;

value utf8_equiv ctx bp buf strm =
  if utf8_lexing.val then
    match strm with lexer
    [ "→" -> keyword_or_error ctx (bp, $pos) "->"
    | "≤" -> keyword_or_error ctx (bp, $pos) "<="
    | "≥" -> keyword_or_error ctx (bp, $pos) ">=" ]
  else
    match strm with parser []
;

value rec ident =
  lexer
  [ [ 'A'-'Z' | 'a'-'z' | '0'-'9' | '_' | ''' | misc_letter ] ident! | ]
;

value rec ident2 =
  lexer
  [ [ '!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
      '%' | '.' | ':' | '<' | '>' | '|' | '$' | misc_punct ]
      ident2!
  | ]
;

value rec ident3 =
  lexer
  [ [ '0'-'9' | 'A'-'Z' | 'a'-'z' | '_' | '!' | '%' | '&' | '*' | '+' | '-' |
      '.' | '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '|' | '~' | ''' |
      '$' | '\128'-'\255' ] ident3!
  | ]
;

value binary = lexer [ '0' | '1' ];
value octal = lexer [ '0'-'7' ];
value decimal = lexer [ '0'-'9' ];
value hexa = lexer [ '0'-'9' | 'a'-'f' | 'A'-'F' ];

value end_integer =
  lexer
  [ "l"/ -> ("INT_l", $buf)
  | "L"/ -> ("INT_L", $buf)
  | "n"/ -> ("INT_n", $buf)
  | -> ("INT", $buf) ]
;

value rec digits_under kind =
  lexer
  [ kind (digits_under kind)!
  | "_" (digits_under kind)!
  | end_integer ]
;

value digits kind =
  lexer
  [ kind (digits_under kind)!
  | -> raise (Stream.Error "ill-formed integer constant") ]
;

value rec decimal_digits_under =
  lexer [ [ '0'-'9' | '_' ] decimal_digits_under! | ]
;

value exponent_part =
  lexer
  [ [ 'e' | 'E' ] [ '+' | '-' | ]
    '0'-'9' ? "ill-formed floating-point constant"
    decimal_digits_under! ]
;

value number =
  lexer
  [ decimal_digits_under "." decimal_digits_under! exponent_part ->
      ("FLOAT", $buf)
  | decimal_digits_under "." decimal_digits_under! -> ("FLOAT", $buf)
  | decimal_digits_under exponent_part -> ("FLOAT", $buf)
  | decimal_digits_under end_integer! ]
;

value char_after_bslash =
  lexer
  [ "'"/
  | _ [ "'"/ | _ [ "'"/ | ] ] ]
;

value char ctx bp =
  lexer
  [ "\\" _ char_after_bslash!
  | "\\" -> err ctx (bp, $pos) "char not terminated"
  | ?= [ _ '''] _! "'"/ ]
;

value any ctx buf =
  parser bp [: `c :] -> do { ctx.line_cnt bp c; $add c }
;

value rec string ctx bp =
  lexer
  [ "\""/
  | "\\" (any ctx) (string ctx bp)!
  | (any ctx) (string ctx bp)!
  | -> err ctx (bp, $pos) "string not terminated" ]
;

value comment ctx bp =
  comment where rec comment =
    lexer
    [ "*)"
    | "*" comment!
    | "(*" comment! comment!
    | "(" comment!
    | "\"" (string ctx bp)! [ -> $add "\"" ] comment!
    | "'*)"
    | "'*" comment!
    | "'" (any ctx) comment!
    | (any ctx) comment!
    | -> err ctx (bp, $pos) "comment not terminated" ]
;

value rec quotation ctx bp =
  lexer
  [ ">>"/
  | ">" (quotation ctx bp)!
  | "<<" (quotation ctx bp)! [ -> $add ">>" ]! (quotation ctx bp)!
  | "<:" ident! "<" (quotation ctx bp)! [ -> $add ">>" ]! (quotation ctx bp)!
  | "<:" ident! (quotation ctx bp)!
  | "<" (quotation ctx bp)!
  | "\\"/ [ '>' | '<' | '\\' ] (quotation ctx bp)!
  | "\\" (quotation ctx bp)!
  | (any ctx) (quotation ctx bp)!
  | -> err ctx (bp, $pos) "quotation not terminated" ]
;

value less_expected = "character '<' expected";

value less ctx bp buf strm =
  if no_quotations.val then
    match strm with lexer
    [ [ -> $add "<" ] ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
  else
    match strm with lexer
    [ "<"/ (quotation ctx bp) -> ("QUOTATION", ":" ^ $buf)
    | ":"/ ident! "<"/ ? less_expected [ -> $add ":" ]! (quotation ctx bp) ->
        ("QUOTATION", $buf)
    | ":"/ ident! ":<"/ ? less_expected [ -> $add "@" ]! (quotation ctx bp) ->
        ("QUOTATION", $buf)
    | [ -> $add "<" ] ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
;

value rec antiquot_rest ctx bp =
  lexer
  [ "$"/
  | "\\"/ (any ctx) (antiquot_rest ctx bp)!
  | (any ctx) (antiquot_rest ctx bp)!
  | -> err ctx (bp, $pos) "antiquotation not terminated" ]
;

value rec antiquot ctx bp =
  lexer
  [ "$"/ -> ":" ^ $buf
  | [ 'a'-'z' | 'A'-'Z' | '0'-'9' | '!' | '_' ] (antiquot ctx bp)!
  | ":" (antiquot_rest ctx bp)! -> $buf
  | "\\"/ (any ctx) (antiquot_rest ctx bp)! -> ":" ^ $buf
  | (any ctx) (antiquot_rest ctx bp)! -> ":" ^ $buf
  | -> err ctx (bp, $pos) "antiquotation not terminated" ]
;

value antiloc bp ep s = Printf.sprintf "%d,%d:%s" bp ep s;

value rec antiquot_loc ctx bp =
  lexer
  [ "$"/ -> antiloc bp $pos (":" ^ $buf)
  | [ 'a'-'z' | 'A'-'Z' | '0'-'9' | '!' | '_' ] (antiquot_loc ctx bp)!
  | ":" (antiquot_rest ctx bp)! -> antiloc bp $pos $buf
  | "\\"/ (any ctx) (antiquot_rest ctx bp)! -> antiloc bp $pos (":" ^ $buf)
  | (any ctx) (antiquot_rest ctx bp)! -> antiloc bp $pos (":" ^ $buf)
  | -> err ctx (bp, $pos) "antiquotation not terminated" ]
;

value dollar ctx bp buf strm =
  if not no_quotations.val && ctx.dollar_for_antiquotation then
    ("ANTIQUOT", antiquot ctx bp buf strm)
  else if force_antiquot_loc.val then
    ("ANTIQUOT_LOC", antiquot_loc ctx bp buf strm)
  else
    match strm with lexer
    [ [ -> $add "$" ] ident2! -> ("", $buf) ]
;

(* ANTIQUOT - specific case for QUESTIONIDENT and QUESTIONIDENTCOLON
    input         expr        patt
    -----         ----        ----
    ?$abc:d$      ?abc:d      ?abc
    ?$abc:d$:     ?abc:d:     ?abc:
    ?$d$          ?:d         ?
    ?$d$:         ?:d:        ?:
*)

(* ANTIQUOT_LOC - specific case for QUESTIONIDENT and QUESTIONIDENTCOLON
    input         expr             patt
    -----         ----             ----
    ?$abc:d$      ?8,13:abc:d      ?abc
    ?$abc:d$:     ?8,13:abc:d:     ?abc:
    ?$d$          ?8,9::d          ?
    ?$d$:         ?8,9::d:         ?:
*)

value question ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    match strm with parser
    [ [: `'$'; s = antiquot ctx bp $empty; `':' :] ->
        ("ANTIQUOT", "?" ^ s ^ ":")
    | [: `'$'; s = antiquot ctx bp $empty :] ->
        ("ANTIQUOT", "?" ^ s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else if force_antiquot_loc.val then
    match strm with parser
    [ [: `'$'; s = antiquot_loc ctx bp $empty; `':' :] ->
        ("ANTIQUOT_LOC", "?" ^ s ^ ":")
    | [: `'$'; s = antiquot_loc ctx bp $empty :] ->
        ("ANTIQUOT_LOC", "?" ^ s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else
    match strm with lexer
    [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
;

value tilde ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    match strm with parser
    [ [: `'$'; s = antiquot ctx bp $empty; `':' :] ->
        ("ANTIQUOT", "~" ^ s ^ ":")
    | [: `'$'; s = antiquot ctx bp $empty :] ->
        ("ANTIQUOT", "~" ^ s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else if force_antiquot_loc.val then
    match strm with parser
    [ [: `'$'; s = antiquot_loc ctx bp $empty; `':' :] ->
        ("ANTIQUOT_LOC", "~" ^ s ^ ":")
    | [: `'$'; s = antiquot_loc ctx bp $empty :] ->
        ("ANTIQUOT_LOC", "~" ^ s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else
    match strm with lexer
    [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
;

value tildeident =
  lexer
  [ ":"/ -> ("TILDEIDENTCOLON", $buf)
  | -> ("TILDEIDENT", $buf) ]
;

value questionident =
  lexer
  [ ":"/ -> ("QUESTIONIDENTCOLON", $buf)
  | -> ("QUESTIONIDENT", $buf) ]
;

value rec linedir n s =
  match stream_peek_nth n s with
  [ Some (' ' | '\t') -> linedir (n + 1) s
  | Some ('0'..'9') -> linedir_digits (n + 1) s
  | _ -> False ]
and linedir_digits n s =
  match stream_peek_nth n s with
  [ Some ('0'..'9') -> linedir_digits (n + 1) s
  | _ -> linedir_quote n s ]
and linedir_quote n s =
  match stream_peek_nth n s with
  [ Some (' ' | '\t') -> linedir_quote (n + 1) s
  | Some '"' -> True
  | _ -> False ]
;

value rec any_to_nl =
  lexer
  [ "\r" | "\n"
  | _ any_to_nl!
  | ]
;

value next_token_after_spaces ctx bp =
  lexer
  [ 'A'-'Z' ident! ->
      let id = $buf in
      try ("", ctx.find_kwd id) with [ Not_found -> ("UIDENT", id) ]
  | greek_letter ident! -> ("GIDENT", $buf)
  | [ 'a'-'z' | '_' | misc_letter ] ident! ->
      let id = $buf in
      try ("", ctx.find_kwd id) with [ Not_found -> ("LIDENT", id) ]
  | '1'-'9' number!
  | "0" [ 'o' | 'O' ] (digits octal)!
  | "0" [ 'x' | 'X' ] (digits hexa)!
  | "0" [ 'b' | 'B' ] (digits binary)!
  | "0" number!
  | "'"/ ?= [ '\\' 'a'-'z' 'a'-'z' ] -> keyword_or_error ctx (bp, $pos) "'"
  | "'"/ (char ctx bp) -> ("CHAR", $buf)
  | "'" -> keyword_or_error ctx (bp, $pos) "'"
  | "\""/ (string ctx bp)! -> ("STRING", $buf)
  | "$"/ (dollar ctx bp)!
  | [ '!' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' | '%' ] ident2! ->
      keyword_or_error ctx (bp, $pos) $buf
  | "~"/ 'a'-'z' ident! tildeident!
  | "~"/ '_' ident! tildeident!
  | "~" (tilde ctx bp)
  | "?"/ 'a'-'z' ident! questionident!
  | "?" (question ctx bp)!
  | "<"/ (less ctx bp)!
  | ":]" -> keyword_or_error ctx (bp, $pos) $buf
  | "::" -> keyword_or_error ctx (bp, $pos) $buf
  | ":=" -> keyword_or_error ctx (bp, $pos) $buf
  | ":>" -> keyword_or_error ctx (bp, $pos) $buf
  | ":" -> keyword_or_error ctx (bp, $pos) $buf
  | ">]" -> keyword_or_error ctx (bp, $pos) $buf
  | ">}" -> keyword_or_error ctx (bp, $pos) $buf
  | ">" ident2! -> keyword_or_error ctx (bp, $pos) $buf
  | "|]" -> keyword_or_error ctx (bp, $pos) $buf
  | "|}" -> keyword_or_error ctx (bp, $pos) $buf
  | "|" ident2! -> keyword_or_error ctx (bp, $pos) $buf
  | "[" ?= [ "<<" | "<:" ] -> keyword_or_error ctx (bp, $pos) $buf
  | "[|" -> keyword_or_error ctx (bp, $pos) $buf
  | "[<" -> keyword_or_error ctx (bp, $pos) $buf
  | "[:" -> keyword_or_error ctx (bp, $pos) $buf
  | "[" -> keyword_or_error ctx (bp, $pos) $buf
  | "{" ?= [ "<<" | "<:" ] -> keyword_or_error ctx (bp, $pos) $buf
  | "{|" -> keyword_or_error ctx (bp, $pos) $buf
  | "{<" -> keyword_or_error ctx (bp, $pos) $buf
  | "{:" -> keyword_or_error ctx (bp, $pos) $buf
  | "{" -> keyword_or_error ctx (bp, $pos) $buf
  | ".." -> keyword_or_error ctx (bp, $pos) ".."
  | "." ?= [ "\n" ] -> keyword_or_error ctx (bp, bp + 1) ctx.dot_newline_is
  | "." ->
      let id =
        if ctx.specific_space_dot && ctx.after_space then " ." else "."
      in
      keyword_or_error ctx (bp, $pos) id
  | ";;" -> keyword_or_error ctx (bp, $pos) ";;"
  | ";" -> keyword_or_error ctx (bp, $pos) ";"
  | (utf8_equiv ctx bp)
  | misc_punct ident2! -> keyword_or_error ctx (bp, $pos) $buf
  | "\\"/ ident3! -> ("LIDENT", $buf)
  | (any ctx) -> keyword_or_error ctx (bp, $pos) $buf ]
;

value get_comment buf strm = $buf;

value rec next_token ctx buf =
  parser bp
  [ [: `('\n' | '\r' as c); s :] ep -> do {
      if c = '\n' then incr Plexing.line_nb.val else ();
      Plexing.bol_pos.val.val := ep;
      ctx.set_line_nb ();
      ctx.after_space := True;
      next_token ctx ($add c) s
    }
  | [: `(' ' | '\t' | '\026' | '\012' as c); s :] -> do {
      ctx.after_space := True;
      next_token ctx ($add c) s
    }
  | [: `'#' when bp = Plexing.bol_pos.val.val; s :] ->
      let comm = get_comment buf () in
      if linedir 1 s then do {
        let buf = any_to_nl ($add '#') s in
        incr Plexing.line_nb.val;
        Plexing.bol_pos.val.val := Stream.count s;
        ctx.set_line_nb ();
        ctx.after_space := True;
        next_token ctx buf s
      }
      else
        let loc = ctx.make_lined_loc (bp, bp + 1) comm in
        (keyword_or_error ctx (bp, bp + 1) "#", loc)
  | [: `'(';
       a =
         parser
         [ [: `'*'; buf = comment ctx bp ($add "(*") !; s :] -> do {
             ctx.set_line_nb ();
             ctx.after_space := True;
             next_token ctx buf s
           }
         | [: :] ep ->
             let loc = ctx.make_lined_loc (bp, ep) $buf in
             (keyword_or_error ctx (bp, ep) "(", loc) ] ! :] -> a
  | [: comm = get_comment buf;
       tok = next_token_after_spaces ctx bp $empty :] ep ->
      let loc = ctx.make_lined_loc (bp, max (bp + 1) ep) comm in
      (tok, loc)
  | [: comm = get_comment buf; _ = Stream.empty :] ->
      let loc = ctx.make_lined_loc (bp, bp + 1) comm in
      (("EOI", ""), loc) ]
;

value next_token_fun ctx glexr (cstrm, s_line_nb, s_bol_pos) =
  try do {
    match Plexing.restore_lexing_info.val with
    [ Some (line_nb, bol_pos) -> do {
        s_line_nb.val := line_nb;
        s_bol_pos.val := bol_pos;
        Plexing.restore_lexing_info.val := None;
      }
    | None -> () ];
    Plexing.line_nb.val := s_line_nb;
    Plexing.bol_pos.val := s_bol_pos;
    let comm_bp = Stream.count cstrm in
    ctx.set_line_nb ();
    ctx.after_space := False;
    let (r, loc) = next_token ctx $empty cstrm in
    match glexr.val.Plexing.tok_comm with
    [ Some list ->
        if Ploc.first_pos loc > comm_bp then
          let comm_loc = Ploc.make_unlined (comm_bp, Ploc.last_pos loc) in
          glexr.val.Plexing.tok_comm := Some [comm_loc :: list]
        else ()
    | None -> () ];
    (r, loc)
  }
  with
  [ Stream.Error str ->
      err ctx (Stream.count cstrm, Stream.count cstrm + 1) str ]
;

value func kwd_table glexr =
  let ctx =
    let line_nb = ref 0 in
    let bol_pos = ref 0 in
    {after_space = False;
     dollar_for_antiquotation = dollar_for_antiquotation.val;
     specific_space_dot = specific_space_dot.val;
     dot_newline_is = dot_newline_is.val;
     find_kwd = Hashtbl.find kwd_table;
     line_cnt bp1 c =
       match c with
       [ '\n' | '\r' -> do {
           if c = '\n' then incr Plexing.line_nb.val else ();
           Plexing.bol_pos.val.val := bp1 + 1;
         }
       | c -> () ];
     set_line_nb () = do {
       line_nb.val := Plexing.line_nb.val.val;
       bol_pos.val := Plexing.bol_pos.val.val;
     };
     make_lined_loc loc comm =
       Ploc.make_loc Plexing.input_file.val line_nb.val bol_pos.val loc comm}
  in
  Plexing.lexer_func_of_parser (next_token_fun ctx glexr)
;

value rec check_keyword_stream =
  parser [: _ = check $empty; _ = Stream.empty :] -> True
and check =
  lexer
  [ [ 'A'-'Z' | 'a'-'z' | misc_letter ] check_ident!
  | [ '!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' | '%' |
      '.' ]
      check_ident2!
  | "$" check_ident2!
  | "<" ?= [ ":" | "<" ]
  | "<" check_ident2!
  | ":]"
  | "::"
  | ":="
  | ":>"
  | ":"
  | ">]"
  | ">}"
  | ">" check_ident2!
  | "|]"
  | "|}"
  | "|" check_ident2!
  | "[" ?= [ "<<" | "<:" ]
  | "[|"
  | "[<"
  | "[:"
  | "["
  | "{" ?= [ "<<" | "<:" ]
  | "{|"
  | "{<"
  | "{:"
  | "{"
  | ";;"
  | ";"
  | misc_punct check_ident2!
  | _ ]
and check_ident =
  lexer
  [ [ 'A'-'Z' | 'a'-'z' | '0'-'9' | '_' | ''' | misc_letter ]
    check_ident! | ]
and check_ident2 =
  lexer
  [ [ '!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' | '%' |
      '.' | ':' | '<' | '>' | '|' | misc_punct ]
    check_ident2! | ]
;

value check_keyword s =
  try check_keyword_stream (Stream.of_string s) with _ -> False
;

value error_no_respect_rules p_con p_prm =
  raise
    (Plexing.Error
       ("the token " ^
          (if p_con = "" then "\"" ^ p_prm ^ "\""
           else if p_prm = "" then p_con
           else p_con ^ " \"" ^ p_prm ^ "\"") ^
          " does not respect Plexer rules"))
;

value using_token kwd_table (p_con, p_prm) =
  match p_con with
  [ "" ->
      if not (hashtbl_mem kwd_table p_prm) then
        if check_keyword p_prm then Hashtbl.add kwd_table p_prm p_prm
        else error_no_respect_rules p_con p_prm
      else ()
  | "LIDENT" ->
      if p_prm = "" then ()
      else
        match p_prm.[0] with
        [ 'A'..'Z' -> error_no_respect_rules p_con p_prm
        | _ -> () ]
  | "UIDENT" ->
      if p_prm = "" then ()
      else
        match p_prm.[0] with
        [ 'a'..'z' -> error_no_respect_rules p_con p_prm
        | _ -> () ]
  | "TILDEIDENT" | "TILDEIDENTCOLON" | "QUESTIONIDENT" |
    "QUESTIONIDENTCOLON" | "INT" | "INT_l" | "INT_L" | "INT_n" | "FLOAT" |
    "CHAR" | "STRING" | "QUOTATION" | "GIDENT" |
    "ANTIQUOT" | "ANTIQUOT_LOC" | "EOI" ->
      ()
  | _ ->
      raise
        (Plexing.Error
           ("the constructor \"" ^ p_con ^
              "\" is not recognized by Plexer")) ]
;

value removing_token kwd_table (p_con, p_prm) =
  match p_con with
  [ "" -> Hashtbl.remove kwd_table p_prm
  | _ -> () ]
;

value text =
  fun
  [ ("", t) -> "'" ^ t ^ "'"
  | ("LIDENT", "") -> "lowercase identifier"
  | ("LIDENT", t) -> "'" ^ t ^ "'"
  | ("UIDENT", "") -> "uppercase identifier"
  | ("UIDENT", t) -> "'" ^ t ^ "'"
  | ("INT", "") -> "integer"
  | ("INT", s) -> "'" ^ s ^ "'"
  | ("FLOAT", "") -> "float"
  | ("STRING", "") -> "string"
  | ("CHAR", "") -> "char"
  | ("QUOTATION", "") -> "quotation"
  | ("ANTIQUOT", k) -> "antiquot \"" ^ k ^ "\""
  | ("EOI", "") -> "end of input"
  | (con, "") -> con
  | (con, prm) -> con ^ " \"" ^ prm ^ "\"" ]
;

value eq_before_colon p e =
  loop 0 where rec loop i =
    if i == String.length e then
      failwith "Internal error in Plexer: incorrect ANTIQUOT"
    else if i == String.length p then e.[i] == ':'
    else if p.[i] == e.[i] then loop (i + 1)
    else False
;

value after_colon e =
  try
    let i = String.index e ':' in
    String.sub e (i + 1) (String.length e - i - 1)
  with
  [ Not_found -> "" ]
;

value after_colon_except_last e =
  try
    let i = String.index e ':' in
    String.sub e (i + 1) (String.length e - i - 2)
  with
  [ Not_found -> "" ]
;

value tok_match =
  fun
  [ ("ANTIQUOT", p_prm) ->
      if p_prm <> "" && (p_prm.[0] = '~' || p_prm.[0] = '?') then
        if p_prm.[String.length p_prm - 1] = ':' then
          let p_prm = String.sub p_prm 0 (String.length p_prm - 1) in
          fun
          [ ("ANTIQUOT", prm) ->
              if prm <> "" && prm.[String.length prm - 1] = ':' then
                if eq_before_colon p_prm prm then after_colon_except_last prm
                else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
        else
          fun
          [ ("ANTIQUOT", prm) ->
              if prm <> "" && prm.[String.length prm - 1] = ':' then
                raise Stream.Failure
              else if eq_before_colon p_prm prm then after_colon prm
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
      else
        fun
        [ ("ANTIQUOT", prm) when eq_before_colon p_prm prm -> after_colon prm
        | _ -> raise Stream.Failure ]
  | ("LIDENT", p_prm) ->
      (* also treats the case when a LIDENT is also a keyword *)
      fun (con, prm) ->
        if con = "LIDENT" then
          if p_prm = "" || prm = p_prm then prm else raise Stream.Failure
        else
          if con = "" && prm = p_prm then prm else raise Stream.Failure
  | ("UIDENT", p_prm) ->
      (* also treats the case when a UIDENT is also a keyword *)
      fun (con, prm) ->
        if con = "UIDENT" then
          if p_prm = "" || prm = p_prm then prm else raise Stream.Failure
        else
          if con = "" && prm = p_prm then prm else raise Stream.Failure
  | tok -> Plexing.default_match tok ]
;

value gmake () =
  let kwd_table = Hashtbl.create 301 in
  let glexr =
    ref
     {Plexing.tok_func = fun []; tok_using = fun []; tok_removing = fun [];
      tok_match = fun []; tok_text = fun []; tok_comm = None}
  in
  let glex =
    {Plexing.tok_func = func kwd_table glexr;
     tok_using = using_token kwd_table;
     tok_removing = removing_token kwd_table;
     tok_match = tok_match; tok_text = text; tok_comm = None}
  in
  do { glexr.val := glex; glex }
;
