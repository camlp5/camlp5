(* camlp4r *)
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

(* $Id: plexer.ml,v 1.28 2007/01/04 17:04:10 deraugla Exp $ *)

open Stdpp;
open Token;

value no_quotations = ref False;

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

value stream_peek_nth n strm =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some x else None
    | [_ :: l] -> loop (n - 1) l ]
;

value p_opt f buf =
  parser
  [ [: c = f buf :] -> buf
  | [: :] -> buf ]
;

value rec decimal_digits_under buf =
  parser
  [ [: `('0'..'9' | '_' as c);
       buf = decimal_digits_under (B.add buf c) ! :] ->
      buf
  | [: :] -> buf ]
;

value rec ident buf =
  parser
  [ [: `('A'..'Z' | 'a'..'z' | '\192'..'\214' | '\216'..'\246' |
         '\248'..'\255' | '0'..'9' | '_' | ''' as c);
       buf = ident (B.add buf c) ! :] -> buf
  | [: :] -> buf ]
and ident2 buf =
  parser
  [ [: `('!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
         '%' | '.' | ':' | '<' | '>' | '|' | '$' as c);
       buf = ident2 (B.add buf c) ! :] -> buf
  | [: :] -> buf ]
and ident3 buf =
  parser
  [ [: `('0'..'9' | 'A'..'Z' | 'a'..'z' | '\192'..'\214' | '\216'..'\246' |
         '\248'..'\255' | '_' | '!' | '%' | '&' | '*' | '+' | '-' | '.' |
         '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '|' | '~' | ''' |
         '$' as c);
       buf = ident3 (B.add buf c) ! :] -> buf
  | [: :] -> buf ]
and digits kind buf =
  parser
  [ [: d = kind; tok = digits_under kind (B.add buf d) ! :] -> tok
  | [: :] -> raise (Stream.Error "ill-formed integer constant") ]
and digits_under kind buf =
  parser
  [ [: d = kind; s :] -> digits_under kind (B.add buf d) s
  | [: `'_'; s :] -> digits_under kind buf s
  | [: `'l' :] -> ("INT_l", B.get buf)
  | [: `'L' :] -> ("INT_L", B.get buf)
  | [: `'n' :] -> ("INT_n", B.get buf)
  | [: :] -> ("INT", B.get buf) ]
and octal = parser [: `('0'..'7' as d) :] -> d
and hexa = parser [: `('0'..'9' | 'a'..'f' | 'A'..'F' as d) :] -> d
and binary = parser [: `('0'..'1' as d) :] -> d;

value exponant_part buf =
  parser
  [ [: `('e' | 'E' as c);
       buf =
         p_opt (fun buf -> parser [: `('+' | '-' as c) :] -> B.add buf c)
           (B.add buf c) !;
       buf =
         parser
         [ [: `('0'..'9' as c);
              buf = decimal_digits_under (B.add buf c) ! :] -> buf ] ?
         "ill-formed floating-point constant" :] -> buf ]
;

value number buf =
  parser
  [ [: buf = decimal_digits_under buf;
       tok =
         parser
         [ [: `'.'; buf = decimal_digits_under (B.add buf '.') !;
              buf = p_opt exponant_part buf ! :] -> ("FLOAT", B.get buf)
         | [: buf = exponant_part buf :] -> ("FLOAT", B.get buf)
         | [: `'l' :] -> ("INT_l", B.get buf)
         | [: `'L' :] -> ("INT_L", B.get buf)
         | [: `'n' :] -> ("INT_n", B.get buf)
         | [: :] -> ("INT", B.get buf) ] ! :] -> tok ]
;

value error_on_unknown_keywords = ref False;

value bol_pos = Token.bol_pos;
value line_nb = Token.line_nb;

value next_token_fun dfa ssd find_kwd glexr =
  let t_line_nb = ref 0 in
  let t_bol_pos = ref 0 in
  let err loc msg =
    Stdpp.raise_with_loc
      (Stdpp.make_lined_loc t_line_nb.val t_bol_pos.val loc) (Token.Error msg)
  in
  let keyword_or_error loc s =
    try (("", find_kwd s), loc) with
    [ Not_found ->
        if error_on_unknown_keywords.val then err loc ("illegal token: " ^ s)
        else (("", s), loc) ]
  in
  let line_cnt bp1 c =
    match c with
    [ '\n' | '\r' -> do { incr line_nb.val; bol_pos.val.val := bp1 + 1; c }
    | c -> c ]
  in
  let rec next_token after_space strm = do {
    t_line_nb.val := line_nb.val.val;
    t_bol_pos.val := bol_pos.val.val;
    match strm with parser bp
    [ [: `'\n' | '\r'; s :] ep ->
        do { bol_pos.val.val := ep; incr line_nb.val; next_token True s }
    | [: `' ' | '\t' | '\026' | '\012'; s :] -> next_token True s
    | [: `'#' when bp = bol_pos.val.val; s :] ->
        if linedir 1 s then do { any_to_nl s; next_token True s }
        else (keyword_or_error (bp, bp + 1) "#", t_line_nb.val, t_bol_pos.val)
    | [: `'('; s :] -> left_paren bp s
    | [: s :] ->
        (next_token_kont after_space s, t_line_nb.val, t_bol_pos.val) ]
  }
  and next_token_kont after_space =
    parser bp
    [ [: `('A'..'Z' | '\192'..'\214' | '\216'..'\222' as c);
         buf = ident (B.char c) ! :] ep ->
        let id = B.get buf in
        let tok =
          try ("", find_kwd id) with [ Not_found -> ("UIDENT", id) ]
        in
        (tok, (bp, ep))
    | [: `('a'..'z' | '\223'..'\246' | '\248'..'\255' | '_' as c);
         buf = ident (B.char c) ! :] ep ->
        let id = B.get buf in
        let tok =
          try ("", find_kwd id) with [ Not_found -> ("LIDENT", id) ]
        in
        (tok, (bp, ep))
    | [: `('1'..'9' as c); tok = number (B.char c) ! :] ep -> (tok, (bp, ep))
    | [: `'0';
         tok =
           parser
           [ [: `'o' | 'O'; tok = digits octal (B.string "0o") ! :] -> tok
           | [: `'x' | 'X'; tok = digits hexa (B.string "0x") ! :] -> tok
           | [: `'b' | 'B'; tok = digits binary (B.string "0b") ! :] -> tok
           | [: tok = number (B.char '0') :] -> tok ] ! :] ep ->
        (tok, (bp, ep))
    | [: `'''; s :] ->
        match Stream.npeek 2 s with
        [ [_; '''] | ['\\'; _] ->
            let tok = ("CHAR", B.get (char bp B.empty s)) in
            let loc = (bp, Stream.count s) in
            (tok, loc)
        | _ -> keyword_or_error (bp, Stream.count s) "'" ]
    | [: `'"'; buf = string bp B.empty ! :] ep ->
        let tok = ("STRING", B.get buf) in
        (tok, (bp, ep))
    | [: `'$'; tok = dollar bp B.empty ! :] ep ->
        (tok, (bp, ep))
    | [: `('!' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' | '%' as c);
         buf = ident2 (B.char c) ! :] ep ->
        keyword_or_error (bp, ep) (B.get buf)
    | [: `('~' as c);
         a =
           parser
           [ [: `('a'..'z' as c); buf = ident (B.char c) ! :] ep ->
               (("TILDEIDENT", B.get buf), (bp, ep))
           | [: buf = ident2 (B.char c) :] ep ->
               keyword_or_error (bp, ep) (B.get buf) ] ! :] ->
        a
    | [: `('?' as c);
         a =
           parser
           [ [: `('a'..'z' as c); buf = ident (B.char c) ! :] ep ->
               (("QUESTIONIDENT", B.get buf), (bp, ep))
           | [: buf = ident2 (B.char c) :] ep ->
               keyword_or_error (bp, ep) (B.get buf) ] ! :] ->
        a
    | [: `'<'; r = less bp ! :] -> r
    | [: `(':' as c1);
         buf =
           parser
           [ [: `(']' | ':' | '=' | '>' as c2) :] -> B.add (B.char c1) c2
           | [: :] -> B.char c1 ] ! :] ep ->
        keyword_or_error (bp, ep) (B.get buf)
    | [: `('>' | '|' as c1);
         buf =
           parser
           [ [: `(']' | '}' as c2) :] -> B.add (B.char c1) c2
           | [: a = ident2 (B.char c1) :] -> a ] ! :] ep ->
        keyword_or_error (bp, ep) (B.get buf)
    | [: `('[' | '{' as c1); s :] ->
        let buf =
          match Stream.npeek 2 s with
          [ ['<'; '<' | ':'] -> B.char c1
          | _ ->
              match s with parser
              [ [: `('|' | '<' | ':' as c2) :] -> B.add (B.char c1) c2
              | [: :] -> B.char c1 ] ]
        in
        let ep = Stream.count s in
        let id = B.get buf in
        keyword_or_error (bp, ep) id
    | [: `'.';
         id =
           parser
           [ [: `'.' :] -> ".."
           | [: :] -> if ssd && after_space then " ." else "." ] ! :] ep ->
        keyword_or_error (bp, ep) id
    | [: `';';
         id =
           parser
           [ [: `';' :] -> ";;"
           | [: :] -> ";" ] ! :] ep ->
        keyword_or_error (bp, ep) id
    | [: `'\\'; buf = ident3 B.empty ! :] ep ->
        (("LIDENT", B.get buf), (bp, ep))
    | [: `c :] ep -> keyword_or_error (bp, ep) (String.make 1 c)
    | [: _ = Stream.empty :] -> (("EOI", ""), (bp, succ bp)) ]
  and less bp strm =
    if no_quotations.val then
      match strm with parser
      [ [: buf = ident2 (B.char '<') :] ep ->
          keyword_or_error (bp, ep) (B.get buf) ]
    else
      match strm with parser
      [ [: `'<'; buf = quotation bp B.empty :] ep ->
          (("QUOTATION", ":" ^ B.get buf), (bp, ep))
      | [: `':'; i = parser [: buf = ident B.empty :] -> B.get buf;
           `'<' ? "character '<' expected";
           buf = quotation bp B.empty :] ep ->
          (("QUOTATION", i ^ ":" ^ B.get buf), (bp, ep))
      | [: buf = ident2 (B.char '<') :] ep ->
          keyword_or_error (bp, ep) (B.get buf) ]
  and string bp buf =
    parser bp1
    [ [: `'"' :] -> buf
    | [: `'\\'; `c;
         a = string bp (B.add (B.add buf '\\') (line_cnt (bp1 + 1) c)) ! :] ->
        a
    | [: `c; a = string bp (B.add buf (line_cnt bp1 c)) ! :] -> a
    | [: :] ep -> err (bp, ep) "string not terminated" ]
  and char bp buf =
    parser
    [ [: `'''; s :] ->
        if B.is_empty buf then char bp (B.add buf ''') s else buf
    | [: `'\\'; `c; a = char bp (B.add (B.add buf '\\') c) ! :] -> a
    | [: `c; a = char bp (B.add buf c) ! :] -> a
    | [: :] ep -> err (bp, ep) "char not terminated" ]
  and dollar bp buf =
    parser
    [ [: `'$' :] -> ("ANTIQUOT", ":" ^ B.get buf)
    | [: `('a'..'z' | 'A'..'Z' as c); a = antiquot bp (B.add buf c) ! :] -> a
    | [: `('0'..'9' as c); a = maybe_locate bp (B.add buf c) ! :] -> a
    | [: `':'; s :] ->
        let k = B.get buf in
        ("ANTIQUOT", k ^ ":" ^ locate_or_antiquot_rest bp B.empty s)
    | [: `'\\'; `c; s :] ->
        ("ANTIQUOT", ":" ^ locate_or_antiquot_rest bp (B.add buf c) s)
    | [: s :] ->
        if dfa then
          match s with parser
          [ [: `c :] ->
              ("ANTIQUOT", ":" ^ locate_or_antiquot_rest bp (B.add buf c) s)
          | [: :] ep -> err (bp, ep) "antiquotation not terminated" ]
        else ("", B.get (ident2 (B.char '$') s)) ]
  and maybe_locate bp buf =
    parser
    [ [: `'$' :] -> ("ANTIQUOT", ":" ^ B.get buf)
    | [: `('0'..'9' as c); a = maybe_locate bp (B.add buf c) ! :] -> a
    | [: `':'; s :] ->
        ("LOCATE", B.get buf ^ ":" ^ locate_or_antiquot_rest bp B.empty s)
    | [: `'\\'; `c; s :] ->
        ("ANTIQUOT", ":" ^ locate_or_antiquot_rest bp (B.add buf c) s)
    | [: `c; s :] ->
        ("ANTIQUOT", ":" ^ locate_or_antiquot_rest bp (B.add buf c) s)
    | [: :] ep -> err (bp, ep) "antiquotation not terminated" ]
  and antiquot bp buf =
    parser
    [ [: `'$' :] -> ("ANTIQUOT", ":" ^ B.get buf)
    | [: `('a'..'z' | 'A'..'Z' | '0'..'9' as c);
         a = antiquot bp (B.add buf c) ! :] ->
        a
    | [: `':'; s :] ->
        let k = B.get buf in
        ("ANTIQUOT", k ^ ":" ^ locate_or_antiquot_rest bp B.empty s)
    | [: `'\\'; `c; s :] ->
        ("ANTIQUOT", ":" ^ locate_or_antiquot_rest bp (B.add buf c) s)
    | [: `c; s :] ->
        ("ANTIQUOT", ":" ^ locate_or_antiquot_rest bp (B.add buf c) s)
    | [: :] ep -> err (bp, ep) "antiquotation not terminated" ]
  and locate_or_antiquot_rest bp buf =
    parser
    [ [: `'$' :] -> B.get buf
    | [: `'\\'; `c; a = locate_or_antiquot_rest bp (B.add buf c) ! :] -> a
    | [: `c; a = locate_or_antiquot_rest bp (B.add buf c) ! :] -> a
    | [: :] ep -> err (bp, ep) "antiquotation not terminated" ]
  and quotation bp buf =
    parser bp1
    [ [: `'>'; a = maybe_end_quotation bp buf ! :] -> a
    | [: `'<'; buf = maybe_nested_quotation bp (B.add buf '<') ! ;
         a = quotation bp buf ! :] -> a
    | [: `'\\';
         buf =
           parser
           [ [: `('>' | '<' | '\\' as c) :] -> B.add buf c
           | [: :] -> B.add buf '\\' ] ! ;
         a = quotation bp buf ! :] ->
        a
    | [: `c; a = quotation bp (B.add buf (line_cnt bp1 c)) ! :] -> a
    | [: :] ep -> err (bp, ep) "quotation not terminated" ]
  and maybe_nested_quotation bp buf =
    parser
    [ [: `'<'; buf = quotation bp (B.add buf '<') ! :] -> B.add_str buf ">>"
    | [: `':'; buf = ident (B.add buf ':') !;
         a =
           parser
           [ [: `'<'; buf = quotation bp (B.add buf '<') ! :] ->
               B.add_str buf ">>"
           | [: :] -> buf ] :] ->
        a
    | [: :] -> buf ]
  and maybe_end_quotation bp buf =
    parser
    [ [: `'>' :] -> buf
    | [: a = quotation bp (B.add buf '>') :] -> a ]
  and left_paren bp =
    parser
    [ [: `'*'; _ = comment bp; a = next_token True :] -> a
    | [: :] ep ->
        (keyword_or_error (bp, ep) "(", line_nb.val.val, bol_pos.val.val) ]
  and comment bp =
    parser
    [ [: `'('; a = left_paren_in_comment bp ! :] -> a
    | [: `'*'; a = star_in_comment bp ! :] -> a
    | [: `'"'; _ = string bp B.empty; a = comment bp ! :] -> a
    | [: `'''; a = quote_in_comment bp ! :] -> a
    | [: `'\n' | '\r'; s :] -> do { incr line_nb.val; comment bp s }
    | [: `c; a = comment bp ! :] -> a
    | [: :] ep -> err (bp, ep) "comment not terminated" ]
  and quote_in_comment bp =
    parser
    [ [: `'''; a = comment bp ! :] -> a
    | [: `'\\'; a = quote_antislash_in_comment bp 0 ! :] -> a
    | [: s :] ->
        do {
          match Stream.npeek 2 s with
          [ [_; '''] -> do { Stream.junk s; Stream.junk s }
          | _ -> () ];
          comment bp s
        } ]
  and quote_any_in_comment bp =
    parser
    [ [: `'''; a = comment bp ! :] -> a
    | [: a = comment bp :] -> a ]
  and quote_antislash_in_comment bp buf =
    parser
    [ [: `'''; a = comment bp ! :] -> a
    | [: `'\\' | '"' | 'n' | 't' | 'b' | 'r';
         a = quote_any_in_comment bp ! :] ->
        a
    | [: `'0'..'9'; a = quote_antislash_digit_in_comment bp ! :] -> a
    | [: a = comment bp :] -> a ]
  and quote_antislash_digit_in_comment bp =
    parser
    [ [: `'0'..'9'; s :] -> quote_antislash_digit2_in_comment bp s
    | [: a = comment bp :] -> a ]
  and quote_antislash_digit2_in_comment bp =
    parser
    [ [: `'0'..'9'; a = quote_any_in_comment bp ! :] -> a
    | [: a = comment bp :] -> a ]
  and left_paren_in_comment bp =
    parser
    [ [: `'*'; _ = comment bp !; a = comment bp ! :] -> a
    | [: a = comment bp :] -> a ]
  and star_in_comment bp =
    parser
    [ [: `')' :] -> ()
    | [: a = comment bp :] -> a ]
  and linedir n s =
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
  and any_to_nl =
    parser
    [ [: `'\r' | '\n' :] ep -> bol_pos.val.val := ep
    | [: `_; s :] -> any_to_nl s
    | [: :] -> () ]
  in
  fun (cstrm, s_line_nb, s_bol_pos) ->
    try do {
      match Token.restore_lexing_info.val with
      [ Some (line_nb, bol_pos) -> do {
          s_line_nb.val := line_nb;
          s_bol_pos.val := bol_pos;
          Token.restore_lexing_info.val := None
        }
      | None -> () ];
      line_nb.val := s_line_nb;
      bol_pos.val := s_bol_pos;
      let glex = glexr.val in
      let comm_bp = Stream.count cstrm in
      let ((r, loc), t_line_nb, t_bol_pos) = next_token False cstrm in
      match glex.tok_comm with
      [ Some list ->
          if fst loc > comm_bp then
            let comm_loc = Stdpp.make_loc (comm_bp, fst loc) in
            glex.tok_comm := Some [comm_loc :: list]
          else ()
      | None -> () ];
      (r, make_lined_loc t_line_nb t_bol_pos loc)
    }
  with
  [ Stream.Error str ->
      err (Stream.count cstrm, Stream.count cstrm + 1) str ]
;

value dollar_for_antiquotation = ref True;
value specific_space_dot = ref False;

value func kwd_table glexr =
  let find = Hashtbl.find kwd_table in
  let dfa = dollar_for_antiquotation.val in
  let ssd = specific_space_dot.val in
  Token.lexer_func_of_parser (next_token_fun dfa ssd find glexr)
;

value rec check_keyword_stream =
  parser [: _ = check; _ = Stream.empty :] -> True
and check =
  parser
  [ [: `'A'..'Z' | 'a'..'z' | '\192'..'\214' | '\216'..'\246' | '\248'..'\255'
        ;
       s :] ->
      check_ident s
  | [: `'!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
        '%' | '.'
        ;
       s :] ->
      check_ident2 s
  | [: `'<'; s :] ->
      match Stream.npeek 1 s with
      [ [':' | '<'] -> ()
      | _ -> check_ident2 s ]
  | [: `':';
       _ =
         parser
         [ [: `']' | ':' | '=' | '>' :] -> ()
         | [: :] -> () ] :] ->
      ()
  | [: `'>' | '|';
       _ =
         parser
         [ [: `']' | '}' :] -> ()
         | [: a = check_ident2 :] -> a ] :] ->
      ()
  | [: `'[' | '{'; s :] ->
      match Stream.npeek 2 s with
      [ ['<'; '<' | ':'] -> ()
      | _ ->
          match s with parser
          [ [: `'|' | '<' | ':' :] -> ()
          | [: :] -> () ] ]
  | [: `';';
       _ =
         parser
         [ [: `';' :] -> ()
         | [: :] -> () ] :] ->
      ()
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
