(* camlp4r pa_lex.cmo *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: plexer.ml,v 1.57 2007/01/25 18:02:47 deraugla Exp $ *)

open Token;

value no_quotations = ref False;
value error_on_unknown_keywords = ref False;

value dollar_for_antiquotation = ref True;
value specific_space_dot = ref False;

(* The string buffering machinery *)

module B :
  sig
    type t = 'abstract;
    value empty : t;
    value char : char -> t;
    value string : string -> t;
    value is_empty : t -> bool;
    value add : t -> char -> t;
    value add_str : t -> string -> t;
    value get : t -> string;
  end =
  struct
    type t = list char;
    value empty = [];
    value is_empty l = l = [];
    value add l c = [c :: l];
    value add_str l s =
      loop l 0 where rec loop l i =
        if i = String.length s then l
        else loop [String.unsafe_get s i :: l] (i + 1)
    ;
    value char c = [c];
    value string = add_str [];
    value get l =
      let s = String.create (List.length l) in
      loop (String.length s - 1) l where rec loop i =
        fun
        [ [c :: l] -> do { String.unsafe_set s i c; loop (i - 1) l }
        | [] -> s ]
    ;
  end
;

(* The lexer *)

type context =
  { after_space : mutable bool;
    dollar_for_antiquotation : bool;
    specific_space_dot : bool;
    find_kwd : string -> string;
    line_cnt : int -> char -> char;
    set_line_nb : unit -> unit;
    make_lined_loc : (int * int) -> Stdpp.location }
;

value err ctx loc msg =
  Stdpp.raise_with_loc (ctx.make_lined_loc loc) (Token.Error msg)
;

value keyword_or_error ctx loc s =
  try ("", ctx.find_kwd s) with
  [ Not_found ->
      if error_on_unknown_keywords.val then
        err ctx loc ("illegal token: " ^ s)
      else ("", s) ]
;

value stream_peek_nth n strm =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some x else None
    | [_ :: l] -> loop (n - 1) l ]
;

value rec decimal_digits_under =
  lexer [ [ '0'..'9' | '_' ] decimal_digits_under! | ]
;

value rec ident =
  lexer
  [ [ 'A'..'Z' | 'a'..'z' | '\192'..'\214' | '\216'..'\246' |
      '\248'..'\255' | '0'..'9' | '_' | ''' ] ident!
  | ]
and ident2 =
  lexer
  [ [ '!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
      '%' | '.' | ':' | '<' | '>' | '|' | '$' ] ident2!
  | ]
and ident3 =
  lexer
  [ [ '0'..'9' | 'A'..'Z' | 'a'..'z' | '\192'..'\214' | '\216'..'\246' |
      '\248'..'\255' | '_' | '!' | '%' | '&' | '*' | '+' | '-' | '.' |
      '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '|' | '~' | ''' | '$' ]
    ident3!
  | ]
;

value rec digits kind =
  lexer
  [ kind (digits_under kind)!
  | -> raise (Stream.Error "ill-formed integer constant") ]
and digits_under kind =
  lexer
  [ kind (digits_under kind)!
  | '_' (digits_under kind)!
  | 'l'/ -> ("INT_l", $buf)
  | 'L'/ -> ("INT_L", $buf)
  | 'n'/ -> ("INT_n", $buf)
  | -> ("INT", $buf) ]
and octal = lexer [ '0'..'7' ]
and hexa = lexer [ '0'..'9' | 'a'..'f' | 'A'..'F' ]
and binary = lexer [ '0'..'1' ];

value exponent_part =
  lexer
  [ [ 'e' | 'E' ] [ '+' | '-' | ]
    '0'..'9' ? "ill-formed floating-point constant"
    decimal_digits_under! ]
;

value number =
  lexer
  [ decimal_digits_under
    [ '.' decimal_digits_under! [ exponent_part | ] -> ("FLOAT", $buf)
    | exponent_part -> ("FLOAT", $buf)
    | 'l'/ -> ("INT_l", $buf)
    | 'L'/ -> ("INT_L", $buf)
    | 'n'/ -> ("INT_n", $buf)
    | -> ("INT", $buf) ] ]
;

value rec char_aux ctx bp =
  lexer
  [ '''/
  | '\\' _ (char_aux ctx bp)!
  | _ (char_aux ctx bp)!
  | -> err ctx (bp, $pos) "char not terminated" ]
;

value char ctx bp =
  lexer [ ''' (char_aux ctx bp) | (char_aux ctx bp) ]
;

value any ctx buf =
  parser bp
  [ [: `c :] -> B.add buf (ctx.line_cnt bp c) ]
;

value rec string ctx bp =
  lexer
  [ '"'/
  | '\\' (any ctx) (string ctx bp)!
  | (any ctx) (string ctx bp)!
  | -> err ctx (bp, $pos) "string not terminated" ]
;

value comment ctx bp =
  comment where rec comment =
    lexer
    [ '*' [ ')' | comment ]!
    | '(' [ '*' comment! | ] comment!
    | '"' (string ctx bp) comment!
    | ''' [ ?= [ _ ''' | '\\' _ ] (char ctx bp)! | ] comment!
    | (any ctx) comment!
    | -> err ctx (bp, $pos) "comment not terminated" ]
;

value add c buf = parser [: :] -> B.add buf c;

value rec quotation ctx bp =
  lexer
  [ '>'/ [ '>'/ | (add '>') (quotation ctx bp)! ]!
  | '<'
    [ '<' (quotation ctx bp)! (add '>')! (add '>')!
    | ':' ident! [ '<' (quotation ctx bp)! (add '>')! (add '>')! | ]
    | ]
    (quotation ctx bp)!
  | '\\'/ [ '>' | '<' | '\\' | (add '\\') ]! (quotation ctx bp)!
  | (any ctx) (quotation ctx bp)!
  | -> err ctx (bp, $pos) "quotation not terminated" ]
;

value less ctx bp strm =
  if no_quotations.val then
    let buf = B.char '<' in
    match strm with lexer
    [ ident2 -> keyword_or_error ctx (bp, $pos) $buf ]
  else
    let buf = B.empty in
    match strm with lexer
    [ '<'/ (quotation ctx bp) -> ("QUOTATION", ":" ^ $buf)
    | ':'/ ident! (add ':')! '<'/ ? "character '<' expected"
      (quotation ctx bp) ->
        ("QUOTATION", $buf)
    | (add '<') ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
;

value rec antiquot ctx bp buf =
  parser
  [ [: `'$' :] -> ("ANTIQUOT", ":" ^ B.get buf)
  | [: `('a'..'z' | 'A'..'Z' | '0'..'9' as c);
       a = antiquot ctx bp (B.add buf c) ! :] ->
      a
  | [: `':'; s :] ->
      let k = B.get buf in
      ("ANTIQUOT", k ^ ":" ^ locate_or_antiquot_rest ctx bp B.empty s)
  | [: `'\\'; `c; s :] ->
      ("ANTIQUOT", ":" ^ locate_or_antiquot_rest ctx bp (B.add buf c) s)
  | [: `c; s :] ->
      ("ANTIQUOT", ":" ^ locate_or_antiquot_rest ctx bp (B.add buf c) s)
  | [: :] ep -> err ctx (bp, ep) "antiquotation not terminated" ]
and locate_or_antiquot_rest ctx bp buf =
  parser
  [ [: `'$' :] -> B.get buf
  | [: `'\\'; `c; a = locate_or_antiquot_rest ctx bp (B.add buf c) ! :] -> a
  | [: `c; a = locate_or_antiquot_rest ctx bp (B.add buf c) ! :] -> a
  | [: :] ep -> err ctx (bp, ep) "antiquotation not terminated" ]
;

value rec maybe_locate ctx bp buf =
  parser
  [ [: `'$' :] -> ("ANTIQUOT", ":" ^ B.get buf)
  | [: `('0'..'9' as c); a = maybe_locate ctx bp (B.add buf c) ! :] -> a
  | [: `':'; s :] ->
      ("LOCATE", B.get buf ^ ":" ^ locate_or_antiquot_rest ctx bp B.empty s)
  | [: `'\\'; `c; s :] ->
      ("ANTIQUOT", ":" ^ locate_or_antiquot_rest ctx bp (B.add buf c) s)
  | [: `c; s :] ->
      ("ANTIQUOT", ":" ^ locate_or_antiquot_rest ctx bp (B.add buf c) s)
  | [: :] ep -> err ctx (bp, ep) "antiquotation not terminated" ]
;

value dollar_for_anti ctx bp buf =
  parser
  [ [: `'$' :] -> ("ANTIQUOT", ":" ^ B.get buf)
  | [: `('a'..'z' | 'A'..'Z' as c); a = antiquot ctx bp (B.add buf c) ! :] ->
      a
  | [: `('0'..'9' as c); a = maybe_locate ctx bp (B.add buf c) ! :] -> a
  | [: `':'; s :] ->
      let k = B.get buf in
      ("ANTIQUOT", k ^ ":" ^ locate_or_antiquot_rest ctx bp B.empty s)
  | [: `'\\'; `c; s :] ->
      ("ANTIQUOT", ":" ^ locate_or_antiquot_rest ctx bp (B.add buf c) s)
  | [: `c; s :] ->
      ("ANTIQUOT", ":" ^ locate_or_antiquot_rest ctx bp (B.add buf c) s)
  | [: :] ep -> err ctx (bp, ep) "antiquotation not terminated" ]
;

value dollar ctx bp buf strm =
  if ctx.dollar_for_antiquotation then dollar_for_anti ctx bp buf strm
  else ("", B.get (ident2 (B.char '$') strm))
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
  parser
  [ [: `'\r' | '\n' :] ep -> do {
      incr Token.line_nb.val;
      Token.bol_pos.val.val := ep;
    }
  | [: `_; s :] -> any_to_nl s
  | [: :] -> () ]
;

value rec next_token ctx =
  parser bp
  [ [: `'\n' | '\r'; s :] ep -> do {
      incr Token.line_nb.val;
      Token.bol_pos.val.val := ep;
      ctx.set_line_nb ();
      ctx.after_space := True;
      next_token ctx s
    }
  | [: `' ' | '\t' | '\026' | '\012'; s :] -> do {
      ctx.after_space := True;
      next_token ctx s
    }
  | [: `'#' when bp = Token.bol_pos.val.val; s :] ->
      if linedir 1 s then do {
        any_to_nl s;
        ctx.set_line_nb ();
        ctx.after_space := True;
        next_token ctx s
      }
      else
        let loc = ctx.make_lined_loc (bp, bp + 1) in
        (keyword_or_error ctx (bp, bp + 1) "#", loc)
  | [: `'(';
       a =
         parser
         [ [: `'*'; _ = comment ctx bp B.empty !; s :] -> do {
             ctx.set_line_nb ();
             ctx.after_space := True;
             next_token ctx s
           }
         | [: :] ep ->
             let loc = ctx.make_lined_loc (bp, ep) in
             (keyword_or_error ctx (bp, ep) "(", loc) ] ! :] -> a
  | [: tok = next_token_kont ctx :] ep ->
      let loc = ctx.make_lined_loc (bp, max (bp + 1) ep) in
      (tok, loc) ]

and next_token_kont ctx =
  parser bp
  [ [: `('A'..'Z' | '\192'..'\214' | '\216'..'\222' as c);
       buf = ident (B.char c) ! :] ->
      let id = B.get buf in
      try ("", ctx.find_kwd id) with [ Not_found -> ("UIDENT", id) ]
  | [: `('a'..'z' | '\223'..'\246' | '\248'..'\255' | '_' as c);
       buf = ident (B.char c) ! :] ->
      let id = B.get buf in
      try ("", ctx.find_kwd id) with [ Not_found -> ("LIDENT", id) ]
  | [: `('1'..'9' as c); tok = number (B.char c) ! :] -> tok
  | [: `'0';
       tok =
         parser
         [ [: `'o' | 'O'; tok = digits octal (B.string "0o") ! :] -> tok
         | [: `'x' | 'X'; tok = digits hexa (B.string "0x") ! :] -> tok
         | [: `'b' | 'B'; tok = digits binary (B.string "0b") ! :] -> tok
         | [: tok = number (B.char '0') :] -> tok ] ! :] ->
      tok
  | [: `''';
       tok =
         parser
         [ [: ?= [_; '''] | ['\\'; _]; buf = char ctx bp B.empty ! :] ->
             ("CHAR", B.get buf)
         | [: :] ep -> keyword_or_error ctx (bp, ep) "'" ] ! :] ->
      tok
  | [: `'"'; buf = string ctx bp B.empty ! :] -> ("STRING", B.get buf)
  | [: `'$'; tok = dollar ctx bp B.empty ! :] -> tok
  | [: `('!' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' | '%' as c);
       buf = ident2 (B.char c) ! :] ep ->
      keyword_or_error ctx (bp, ep) (B.get buf)
  | [: `('~' as c);
       a =
         parser
         [ [: `('a'..'z' as c); buf = ident (B.char c) ! :] ->
             ("TILDEIDENT", B.get buf)
         | [: buf = ident2 (B.char c) :] ep ->
             keyword_or_error ctx (bp, ep) (B.get buf) ] ! :] ->
      a
  | [: `('?' as c);
       a =
         parser
         [ [: `('a'..'z' as c); buf = ident (B.char c) ! :] ->
             ("QUESTIONIDENT", B.get buf)
         | [: buf = ident2 (B.char c) :] ep ->
             keyword_or_error ctx (bp, ep) (B.get buf) ] ! :] ->
      a
  | [: `'<'; tok = less ctx bp ! :] -> tok
  | [: `(':' as c1);
       buf =
         parser
         [ [: `(']' | ':' | '=' | '>' as c2) :] -> B.add (B.char c1) c2
         | [: :] -> B.char c1 ] ! :] ep ->
      keyword_or_error ctx (bp, ep) (B.get buf)
  | [: `('>' | '|' as c1);
       buf =
         parser
         [ [: `(']' | '}' as c2) :] -> B.add (B.char c1) c2
         | [: a = ident2 (B.char c1) :] -> a ] ! :] ep ->
      keyword_or_error ctx (bp, ep) (B.get buf)
  | [: `('[' | '{' as c1);
       buf =
         parser
         [ [: ?= ['<'; '<' | ':'] :] -> B.char c1
         | [: `('|' | '<' | ':' as c2) :] -> B.add (B.char c1) c2
         | [: :] -> B.char c1 ] ! :] ep ->
      keyword_or_error ctx (bp, ep) (B.get buf)
  | [: `'.';
       id =
         parser
         [ [: `'.' :] -> ".."
         | [: :] ->
             if ctx.specific_space_dot && ctx.after_space then " ."
             else "." ] ! :] ep ->
      keyword_or_error ctx (bp, ep) id
  | [: `';';
       id =
         parser
         [ [: `';' :] -> ";;"
         | [: :] -> ";" ] ! :] ep ->
      keyword_or_error ctx (bp, ep) id
  | [: `'\\'; buf = ident3 B.empty ! :] -> ("LIDENT", B.get buf)
  | [: `c :] ep -> keyword_or_error ctx (bp, ep) (String.make 1 c)
  | [: _ = Stream.empty :] -> ("EOI", "") ]
;

value next_token_fun ctx glexr (cstrm, s_line_nb, s_bol_pos) =
  try do {
    match Token.restore_lexing_info.val with
    [ Some (line_nb, bol_pos) -> do {
        s_line_nb.val := line_nb;
        s_bol_pos.val := bol_pos;
        Token.restore_lexing_info.val := None
      }
    | None -> () ];
    Token.line_nb.val := s_line_nb;
    Token.bol_pos.val := s_bol_pos;
    let comm_bp = Stream.count cstrm in
    ctx.set_line_nb ();
    ctx.after_space := False;
    let (r, loc) = next_token ctx cstrm in
    match glexr.val.tok_comm with
    [ Some list ->
        if Stdpp.first_pos loc > comm_bp then
          let comm_loc = Stdpp.make_loc (comm_bp, Stdpp.last_pos loc) in
          glexr.val.tok_comm := Some [comm_loc :: list]
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
     find_kwd = Hashtbl.find kwd_table;
     line_cnt bp1 c =
       match c with
       [ '\n' | '\r' -> do {
           incr Token.line_nb.val;
           Token.bol_pos.val.val := bp1 + 1;
           c
         }
       | c -> c ];
     set_line_nb () = do {
       line_nb.val := Token.line_nb.val.val;
       bol_pos.val := Token.bol_pos.val.val;
     };
     make_lined_loc loc = Stdpp.make_lined_loc line_nb.val bol_pos.val loc}
  in
  Token.lexer_func_of_parser (next_token_fun ctx glexr)
;

value rec check_keyword_stream =
  parser [: _ = check; _ = Stream.empty :] -> True
and check =
  parser
  [ [: `'A'..'Z' | 'a'..'z' | '\192'..'\214' | '\216'..'\246' |
        '\248'..'\255'; s :] ->
      check_ident s
  | [: `'!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
        '%' | '.'; s :] ->
      check_ident2 s
  | [: `'<';
       a =
         parser
         [ [: ?= [':' | '<'] :] -> ()
         | [: a = check_ident2 :] -> a ] ! :] -> a
  | [: `':';
       a =
         parser
         [ [: `']' | ':' | '=' | '>' :] -> ()
         | [: :] -> () ] :] ->
      a
  | [: `'>' | '|';
       a =
         parser
         [ [: `']' | '}' :] -> ()
         | [: a = check_ident2 :] -> a ] :] ->
      a
  | [: `'[' | '{';
       a =
         parser
         [ [: ?= ['<'; '<' | ':'] :] -> ()
         | [: `'|' | '<' | ':' :] -> ()
         | [: :] -> () ] ! :] ->
      a
  | [: `';';
       a =
         parser
         [ [: `';' :] -> ()
         | [: :] -> () ] :] ->
      a
  | [: `_ :] -> () ]
and check_ident =
  parser
  [ [: `'A'..'Z' | 'a'..'z' | '\192'..'\214' | '\216'..'\246' |
        '\248'..'\255' | '0'..'9' | '_' | '''
        ;
       s :] ->
      check_ident s
  | [: :] -> () ]
and check_ident2 =
  parser
  [ [: `'!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
        '%' | '.' | ':' | '<' | '>' | '|'
        ;
       s :] ->
      check_ident2 s
  | [: :] -> () ]
;

value check_keyword s =
  try check_keyword_stream (Stream.of_string s) with _ -> False
;

value error_no_respect_rules p_con p_prm =
  raise
    (Token.Error
       ("the token " ^
          (if p_con = "" then "\"" ^ p_prm ^ "\""
           else if p_prm = "" then p_con
           else p_con ^ " \"" ^ p_prm ^ "\"") ^
          " does not respect Plexer rules"))
;

value error_ident_and_keyword p_con p_prm =
  raise
    (Token.Error
       ("the token \"" ^ p_prm ^ "\" is used as " ^ p_con ^
          " and as keyword"))
;

value using_token kwd_table ident_table (p_con, p_prm) =
  match p_con with
  [ "" ->
      if not (Hashtbl.mem kwd_table p_prm) then
        if check_keyword p_prm then
          if Hashtbl.mem ident_table p_prm then
            error_ident_and_keyword (Hashtbl.find ident_table p_prm) p_prm
          else Hashtbl.add kwd_table p_prm p_prm
        else error_no_respect_rules p_con p_prm
      else ()
  | "LIDENT" ->
      if p_prm = "" then ()
      else
        match p_prm.[0] with
        [ 'A'..'Z' -> error_no_respect_rules p_con p_prm
        | _ ->
            if Hashtbl.mem kwd_table p_prm then
              error_ident_and_keyword p_con p_prm
            else Hashtbl.add ident_table p_prm p_con ]
  | "UIDENT" ->
      if p_prm = "" then ()
      else
        match p_prm.[0] with
        [ 'a'..'z' -> error_no_respect_rules p_con p_prm
        | _ ->
            if Hashtbl.mem kwd_table p_prm then
              error_ident_and_keyword p_con p_prm
            else Hashtbl.add ident_table p_prm p_con ]
  | "TILDEIDENT" | "QUESTIONIDENT" | "INT" | "INT_l" | "INT_L" | "INT_n" |
    "FLOAT" | "CHAR" | "STRING" |
    "QUOTATION" | "ANTIQUOT" | "LOCATE" | "EOI" ->
      ()
  | _ ->
      raise
        (Token.Error
           ("the constructor \"" ^ p_con ^
              "\" is not recognized by Plexer")) ]
;

value removing_token kwd_table ident_table (p_con, p_prm) =
  match p_con with
  [ "" -> Hashtbl.remove kwd_table p_prm
  | "LIDENT" | "UIDENT" ->
      if p_prm <> "" then Hashtbl.remove ident_table p_prm else ()
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
  | ("LOCATE", "") -> "locate"
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

value tok_match =
  fun
  [ ("ANTIQUOT", p_prm) ->
      fun
      [ ("ANTIQUOT", prm) when eq_before_colon p_prm prm -> after_colon prm
      | _ -> raise Stream.Failure ]
  | tok -> Token.default_match tok ]
;

value gmake () =
  let kwd_table = Hashtbl.create 301 in
  let id_table = Hashtbl.create 301 in
  let glexr =
    ref
     {tok_func = fun []; tok_using = fun []; tok_removing = fun [];
      tok_match = fun []; tok_text = fun []; tok_comm = None}
  in
  let glex =
    {tok_func = func kwd_table glexr;
     tok_using = using_token kwd_table id_table;
     tok_removing = removing_token kwd_table id_table; tok_match = tok_match;
     tok_text = text; tok_comm = None}
  in
  do { glexr.val := glex; glex }
;
