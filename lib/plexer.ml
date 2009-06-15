(* camlp5r pa_lex.cmo *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp5                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: plexer.ml,v 1.95 2007/09/14 12:44:26 deraugla Exp $ *)

value no_quotations = ref False;
value error_on_unknown_keywords = ref False;

value dollar_for_antiquotation = ref True;
value specific_space_dot = ref False;

value force_antiquot_loc = ref False;

(* The string buffering machinery *)

value rev_implode l =
  let s = String.create (List.length l) in
  loop (String.length s - 1) l where rec loop i =
    fun
    [ [c :: l] -> do { String.unsafe_set s i c; loop (i - 1) l }
    | [] -> s ]
;

module B :
  sig
    type t = 'abstract;
    value empty : t;
    value add : char -> t -> t;
    value get : t -> string;
  end =
  struct
    type t = list char;
    value empty = [];
    value add c l = [c :: l];
    value get = rev_implode;
  end
;

(* The lexer *)

type context =
  { after_space : mutable bool;
    dollar_for_antiquotation : bool;
    specific_space_dot : bool;
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

value stream_peek_nth n strm =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some x else None
    | [_ :: l] -> loop (n - 1) l ]
;

value rec ident = lexer [ "A..Za..z0..9_'\128..\255" ident! | ];
value rec ident2 = lexer [ "!?~=@^&+-*/%.:<>|$" ident2! | ];

value rec ident3 =
  lexer [ "0..9A..Za..z_!%&*+-./:<=>?@^|~'$\128..\255" ident3! | ]
;

value binary = lexer [ "01" ];
value octal = lexer [ "0..7" ];
value decimal = lexer [ "0..9" ];
value hexa = lexer [ "0..9a..fA..F" ];

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

value rec decimal_digits_under = lexer [ "0..9_" decimal_digits_under! | ];

value exponent_part =
  lexer
  [ "eE" [ "+-" | ] "0..9" ? "ill-formed floating-point constant"
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

value rec char_aux ctx bp =
  lexer
  [ "'"/
  | _ (char_aux ctx bp)!
  | -> err ctx (bp, $pos) "char not terminated" ]
;

value char ctx bp =
  lexer
  [ "\\" _ (char_aux ctx bp)!
  | "\\" -> err ctx (bp, $pos) "char not terminated"
  | ?= [ _ '''] _! "'"/ ]
;

value any ctx buf =
  parser bp [: `c :] -> do { ctx.line_cnt bp c; B.add c buf }
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
    [ "*" ")"
    | "*" comment!
    | "(" "*" comment! comment!
    | "(" comment!
    | "\"" (string ctx bp)! [ -> $add "\"" ] comment!
    | "'" (char ctx bp) comment!
    | "'" comment!
    | (any ctx) comment!
    | -> err ctx (bp, $pos) "comment not terminated" ]
;

value rec quotation ctx bp =
  lexer
  [ ">"/ ">"/
  | ">" (quotation ctx bp)!
  | "<" "<" (quotation ctx bp)! [ -> $add ">>" ]! (quotation ctx bp)!
  | "<" ":" ident! "<" (quotation ctx bp)! [ -> $add ">>" ]!
      (quotation ctx bp)!
  | "<" ":" ident! (quotation ctx bp)!
  | "<" (quotation ctx bp)!
  | "\\"/ "><\\" (quotation ctx bp)!
  | "\\" (quotation ctx bp)!
  | (any ctx) (quotation ctx bp)!
  | -> err ctx (bp, $pos) "quotation not terminated" ]
;

value less ctx bp buf strm =
  if no_quotations.val then
    match strm with lexer
    [ [ -> $add "<" ] ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
  else
    match strm with lexer
    [ "<"/ (quotation ctx bp) -> ("QUOTATION", ":" ^ $buf)
    | ":"/ ident! [ -> $add ":" ]! "<"/ ? "character '<' expected"
      (quotation ctx bp) ->
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
  | "a..zA..Z0..9_" (antiquot ctx bp)!
  | ":" (antiquot_rest ctx bp)! -> $buf
  | "\\"/ (any ctx) (antiquot_rest ctx bp)! -> ":" ^ $buf
  | (any ctx) (antiquot_rest ctx bp)! -> ":" ^ $buf
  | -> err ctx (bp, $pos) "antiquotation not terminated" ]
;

value antiloc bp ep s = Printf.sprintf "%d,%d:%s" bp ep s;

value rec antiquot_loc ctx bp =
  lexer
  [ "$"/ -> antiloc bp $pos (":" ^ $buf)
  | "a..zA..Z0..9_" (antiquot_loc ctx bp)!
  | ":" (antiquot_rest ctx bp)! -> antiloc bp $pos $buf
  | "\\"/ (any ctx) (antiquot_rest ctx bp)! -> antiloc bp $pos (":" ^ $buf)
  | (any ctx) (antiquot_rest ctx bp)! -> antiloc bp $pos (":" ^ $buf)
  | -> err ctx (bp, $pos) "antiquotation not terminated" ]
;

value dollar ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    ("ANTIQUOT", antiquot ctx bp buf strm)
  else if force_antiquot_loc.val then
    ("ANTIQUOT_LOC", antiquot_loc ctx bp buf strm)
  else
    match strm with lexer
    [ [ -> $add "$" ] ident2! -> ("", $buf) ]
;

value question ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    match strm with parser
    [ [: `'$'; s = antiquot ctx bp $empty; `':' :] ->
        ("QUESTIONANTIQUOTCOLON", s)
    | [: `'$'; s = antiquot ctx bp $empty :] ->
        ("QUESTIONANTIQUOT", s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else if force_antiquot_loc.val then
    match strm with parser
    [ [: `'$'; s = antiquot_loc ctx bp $empty; `':' :] ->
        ("QUESTIONANTIQUOTCOLON_LOC", s)
    | [: `'$'; s = antiquot_loc ctx bp $empty :] ->
        ("QUESTIONANTIQUOT_LOC", s)
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
        ("TILDEANTIQUOTCOLON", s)
    | [: `'$'; s = antiquot ctx bp $empty :] ->
        ("TILDEANTIQUOT", s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else if force_antiquot_loc.val then
    match strm with parser
    [ [: `'$'; s = antiquot_loc ctx bp $empty; `':' :] ->
        ("TILDEANTIQUOTCOLON_LOC", s)
    | [: `'$'; s = antiquot_loc ctx bp $empty :] ->
        ("TILDEANTIQUOT_LOC", s)
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
  [ "\r\n"
  | _ any_to_nl!
  | ]
;

value next_token_after_spaces ctx bp =
  lexer
  [ "A..Z" ident! ->
      let id = $buf in
      try ("", ctx.find_kwd id) with [ Not_found -> ("UIDENT", id) ]
  | "a..z_\128..\255" ident! ->
      let id = $buf in
      try ("", ctx.find_kwd id) with [ Not_found -> ("LIDENT", id) ]
  | "1..9" number!
  | "0" "oO" (digits octal)!
  | "0" "xX" (digits hexa)!
  | "0" "bB" (digits binary)!
  | "0" number!
  | "'"/ (char ctx bp) -> ("CHAR", $buf)
  | "'" -> keyword_or_error ctx (bp, $pos) "'"
  | "\""/ (string ctx bp)! -> ("STRING", $buf)
  | "$"/ (dollar ctx bp)!
  | "!=@^&+-*/%" ident2! -> keyword_or_error ctx (bp, $pos) $buf
  | "~"/ "a..z" ident! tildeident!
  | "~" (tilde ctx bp)
  | "?"/ "a..z" ident! questionident!
  | "?" (question ctx bp)!
  | "<"/ (less ctx bp)!
  | ":" "]:=>" -> keyword_or_error ctx (bp, $pos) $buf
  | ":" -> keyword_or_error ctx (bp, $pos) $buf
  | ">|" "]}" -> keyword_or_error ctx (bp, $pos) $buf
  | ">|" ident2! -> keyword_or_error ctx (bp, $pos) $buf
  | "[{" ?= [ "<<" | "<:" ] -> keyword_or_error ctx (bp, $pos) $buf
  | "[{" "|<:" -> keyword_or_error ctx (bp, $pos) $buf
  | "[{" -> keyword_or_error ctx (bp, $pos) $buf
  | "." "." -> keyword_or_error ctx (bp, $pos) ".."
  | "." ->
      let id =
        if ctx.specific_space_dot && ctx.after_space then " ." else "."
      in
      keyword_or_error ctx (bp, $pos) id
  | ";" ";" -> keyword_or_error ctx (bp, $pos) ";;"
  | ";" -> keyword_or_error ctx (bp, $pos) ";"
  | "\\"/ ident3! -> ("LIDENT", $buf)
  | (any ctx) -> keyword_or_error ctx (bp, $pos) $buf ]
;

value rec next_token ctx buf =
  parser bp
  [ [: `('\n' | '\r' as c); s :] ep -> do {
      incr Plexing.line_nb.val;
      Plexing.bol_pos.val.val := ep;
      ctx.set_line_nb ();
      ctx.after_space := True;
      next_token ctx (B.add c buf) s
    }
  | [: `(' ' | '\t' | '\026' | '\012' as c); s :] -> do {
      ctx.after_space := True;
      next_token ctx (B.add c buf) s
    }
  | [: `'#' when bp = Plexing.bol_pos.val.val; s :] ->
      if linedir 1 s then do {
        let buf = any_to_nl (B.add '#' buf) s in
        incr Plexing.line_nb.val;
        Plexing.bol_pos.val.val := Stream.count s;
        ctx.set_line_nb ();
        ctx.after_space := True;
        next_token ctx buf s
      }
      else
        let loc = ctx.make_lined_loc (bp, bp + 1) (B.get buf) in
        (keyword_or_error ctx (bp, bp + 1) "#", loc)
  | [: `'(';
       a =
         parser
         [ [: `'*'; buf = comment ctx bp (B.add '*' (B.add '(' buf)) !;
              s :] -> do {
             ctx.set_line_nb ();
             ctx.after_space := True;
             next_token ctx buf s
           }
         | [: :] ep ->
             let loc = ctx.make_lined_loc (bp, ep) (B.get buf) in
             (keyword_or_error ctx (bp, ep) "(", loc) ] ! :] -> a
  | [: tok = next_token_after_spaces ctx bp $empty :] ep ->
      let loc = ctx.make_lined_loc (bp, max (bp + 1) ep) (B.get buf) in
      (tok, loc)
  | [: _ = Stream.empty :] ->
      let loc = ctx.make_lined_loc (bp, bp + 1) (B.get buf) in
      (("EOI", ""), loc) ]
;

value next_token_fun ctx glexr (cstrm, s_line_nb, s_bol_pos) =
  try do {
    match Plexing.restore_lexing_info.val with
    [ Some (line_nb, bol_pos) -> do {
        s_line_nb.val := line_nb;
        s_bol_pos.val := bol_pos;
        Plexing.restore_lexing_info.val := None
      }
    | None -> () ];
    Plexing.line_nb.val := s_line_nb;
    Plexing.bol_pos.val := s_bol_pos;
    let comm_bp = Stream.count cstrm in
    ctx.set_line_nb ();
    ctx.after_space := False;
    let (r, loc) = next_token ctx B.empty cstrm in
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
     find_kwd = Hashtbl.find kwd_table;
     line_cnt bp1 c =
       match c with
       [ '\n' | '\r' -> do {
           incr Plexing.line_nb.val;
           Plexing.bol_pos.val.val := bp1 + 1;
         }
       | c -> () ];
     set_line_nb () = do {
       line_nb.val := Plexing.line_nb.val.val;
       bol_pos.val := Plexing.bol_pos.val.val;
     };
     make_lined_loc loc comm =
       Ploc.make line_nb.val bol_pos.val loc}
  in
  Plexing.lexer_func_of_parser (next_token_fun ctx glexr)
;

value rec check_keyword_stream =
  parser [: _ = check $empty; _ = Stream.empty :] -> True
and check =
  lexer
  [ "A..Za..z\128..\255" check_ident!
  | "!?~=@^&+-*/%." check_ident2!
  | "$" check_ident2!
  | "<" ?= [ ":" | "<" ]
  | "<" check_ident2!
  | ":" "]:=>"
  | ":"
  | ">|" "]}"
  | ">|" check_ident2!
  | "[{" ?= [ "<<" | "<:" ]
  | "[{" "|<:"
  | "[{"
  | ";" ";"
  | ";"
  | _ ]
and check_ident =
  lexer [ "A..Za..z0..9_'\128..\255" check_ident! | ]
and check_ident2 =
  lexer [ "!?~=@^&+-*/%.:<>|" check_ident2! | ]
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

value error_ident_and_keyword p_con p_prm =
  raise
    (Plexing.Error
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
  | "TILDEIDENT" | "TILDEIDENTCOLON" | "QUESTIONIDENT" |
    "QUESTIONIDENTCOLON" | "INT" | "INT_l" | "INT_L" | "INT_n" | "FLOAT" |
    "CHAR" | "STRING" | "QUOTATION" |
    "ANTIQUOT" | "ANTIQUOT_LOC" | "EOI" ->
      ()
  | "QUESTIONANTIQUOTCOLON" | "QUESTIONANTIQUOT"
  | "QUESTIONANTIQUOTCOLON_LOC" | "QUESTIONANTIQUOT_LOC" -> ()
  | "TILDEANTIQUOTCOLON" | "TILDEANTIQUOT"
  | "TILDEANTIQUOTCOLON_LOC" | "TILDEANTIQUOT_LOC" -> ()
  | _ ->
      raise
        (Plexing.Error
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
  | ("QUESTIONANTIQUOT", p_prm) ->
      fun
      [ ("QUESTIONANTIQUOT", prm) when eq_before_colon p_prm prm ->
          after_colon prm
      | _ -> raise Stream.Failure ]
  | ("QUESTIONANTIQUOTCOLON", p_prm) ->
      fun
      [ ("QUESTIONANTIQUOTCOLON", prm) when eq_before_colon p_prm prm ->
          after_colon prm
      | _ -> raise Stream.Failure ]
  | ("TILDEANTIQUOT", p_prm) ->
      fun
      [ ("TILDEANTIQUOT", prm) when eq_before_colon p_prm prm ->
          after_colon prm
      | _ -> raise Stream.Failure ]
  | ("TILDEANTIQUOTCOLON", p_prm) ->
      fun
      [ ("TILDEANTIQUOTCOLON", prm) when eq_before_colon p_prm prm ->
          after_colon prm
      | _ -> raise Stream.Failure ]
  | tok -> Plexing.default_match tok ]
;

value gmake () =
  let kwd_table = Hashtbl.create 301 in
  let id_table = Hashtbl.create 301 in
  let glexr =
    ref
     {Plexing.tok_func = fun []; tok_using = fun []; tok_removing = fun [];
      tok_match = fun []; tok_text = fun []; tok_comm = None}
  in
  let glex =
    {Plexing.tok_func = func kwd_table glexr;
     tok_using = using_token kwd_table id_table;
     tok_removing = removing_token kwd_table id_table; tok_match = tok_match;
     tok_text = text; tok_comm = None}
  in
  do { glexr.val := glex; glex }
;
