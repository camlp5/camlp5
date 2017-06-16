(* camlp5 pa_r.cmo pa_rp.cmo pa_extend.cmo q_MLast.cmo pr_dump.cmo *)
(* pa_scheme.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Pcaml;
open Exparser;
open Versdep;

type choice α β =
  [ Left of α
  | Right of β ]
;

(* Buffer *)

module Buff =
  struct
    value buff = ref (string_create 80);
    value store len x = do {
      if len >= string_length buff.val then
        buff.val :=
          string_cat buff.val (string_create (string_length buff.val))
      else ();
      string_set buff.val len x;
      succ len
    };
    value mstore len s =
      add_rec len 0 where rec add_rec len i =
        if i == String.length s then len
        else add_rec (store len s.[i]) (succ i)
    ;
    value get len = bytes_to_string (string_sub buff.val 0 len);
  end
;

value rename_id s =
  if String.length s > 0 && s.[String.length s - 1] = '#' then
    String.sub s 0 (String.length s - 1)
  else Pcaml.rename_id.val s
;

(* Lexer *)

value rec skip_to_eol len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some ('\n' | '\r' as c) → do { Stream.junk strm__; Buff.store len c }
      | Some c → do {
          Stream.junk strm__;
          skip_to_eol (Buff.store len c) strm__
        }
      | _ → raise Stream.Failure ]
;

value no_ident =
  ['('; ')'; '['; ']'; '{'; '}'; ' '; '\t'; '\n'; '\r'; ';'; '.']
;

value rec ident len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some x when not (List.mem x no_ident) → do {
          Stream.junk strm__;
          ident (Buff.store len x) strm__
        }
      | _ → len ]
;

value identifier kwt s =
  let con =
    try do {
      (Hashtbl.find kwt s : unit);
      ""
    }
    with
    [ Not_found →
        match s.[0] with
        [ 'A'..'Z' → "UIDENT"
        | _ → "LIDENT" ] ]
  in
  (con, s)
;

value rec string len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some '"' → do { Stream.junk strm__; Buff.get len }
      | Some '\\' → do {
          Stream.junk strm__;
          match strm__ with parser
          [ [: `c :] -> string (Buff.store (Buff.store len '\\') c) strm__
          | [: :] -> raise (Stream.Error "") ]
        }
      | Some x → do { Stream.junk strm__; string (Buff.store len x) strm__ }
      | _ → raise Stream.Failure ]
;

value rec end_exponent_part_under len =
  parser
  [ [: `('0'..'9' as c) :] ->
      end_exponent_part_under (Buff.store len c) strm__
  | [: :] -> ("FLOAT", Buff.get len) ]
;

value end_exponent_part len =
  parser
  [ [: `('0'..'9' as c) :] ->
      end_exponent_part_under (Buff.store len c) strm__
  | [: :] -> raise (Stream.Error "ill-formed floating-point constant") ]
;

value exponent_part len =
  parser
  [ [: `('+' | '-' as c) :] -> end_exponent_part (Buff.store len c) strm__
  | [: :] -> end_exponent_part len strm__ ]
;

value rec decimal_part len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some ('0'..'9' as c) → do {
          Stream.junk strm__;
          decimal_part (Buff.store len c) strm__
        }
      | Some ('e' | 'E') → do {
          Stream.junk strm__;
          exponent_part (Buff.store len 'E') strm__
        }
      | _ → ("FLOAT", Buff.get len) ]
;

value rec number len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some ('0'..'9' as c) → do {
          Stream.junk strm__;
          number (Buff.store len c) strm__
        }
      | Some '.' → do {
          Stream.junk strm__;
          decimal_part (Buff.store len '.') strm__
        }
      | Some ('e' | 'E') → do {
          Stream.junk strm__;
          exponent_part (Buff.store len 'E') strm__
        }
      | Some 'l' → do { Stream.junk strm__; ("INT_l", Buff.get len) }
      | Some 'L' → do { Stream.junk strm__; ("INT_L", Buff.get len) }
      | Some 'n' → do { Stream.junk strm__; ("INT_n", Buff.get len) }
      | _ → ("INT", Buff.get len) ]
;

value binary = parser [: `('0'..'1' as c) :] -> c;

value octal = parser [: `('0'..'7' as c) :] -> c;

value hexa = parser [: `('0'..'9' | 'a'..'f' | 'A'..'F' as c) :] -> c;

value rec digits_under kind len =
  parser
  [ [: d = kind :] -> digits_under kind (Buff.store len d) strm__
  | [: :] ->
      match Stream.peek strm__ with
      [ Some '_' → do {
          Stream.junk strm__;
          digits_under kind (Buff.store len '_') strm__
        }
      | Some 'l' → do { Stream.junk strm__; ("INT_l", Buff.get len) }
      | Some 'L' → do { Stream.junk strm__; ("INT_L", Buff.get len) }
      | Some 'n' → do { Stream.junk strm__; ("INT_n", Buff.get len) }
      | _ → ("INT", Buff.get len) ] ]
;

value digits kind bp len =
  parser
  [ [: d = kind :] ->
      try digits_under kind (Buff.store len d) strm__ with
      [ Stream.Failure → raise (Stream.Error "") ]
  | [: :] ->
      let ep = Stream.count strm__ in
      Ploc.raise (Ploc.make_unlined (bp, ep))
        (Failure "ill-formed integer constant") ]
;

value base_number kwt bp len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some ('b' | 'B') → do {
          Stream.junk strm__;
          digits binary bp (Buff.store len 'b') strm__
        }
      | Some ('o' | 'O') → do {
          Stream.junk strm__;
          digits octal bp (Buff.store len 'o') strm__
        }
      | Some ('x' | 'X') → do {
          Stream.junk strm__;
          digits hexa bp (Buff.store len 'x') strm__
        }
      | _ →
          let len = ident (Buff.store 0 '#') strm__ in
          identifier kwt (Buff.get len) ]
;

value rec operator len =
  parser
  [ [: `'.' :] -> Buff.store len '.'
  | [: :] -> len ]
;

value char_or_quote_id x =
  parser
  [ [: `''' :] -> ("CHAR", String.make 1 x)
  | [: :] ->
      let s = strm__ in
      let ep = Stream.count strm__ in
      if List.mem x no_ident then
        Ploc.raise (Ploc.make_unlined (ep - 2, ep - 1))
          (Stream.Error "bad quote")
      else
        let len = Buff.store (Buff.store 0 ''') x in
        let s = Buff.get (ident len s) in
        ("LIDENT", s) ]
;

value rec char len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some ''' → do { Stream.junk strm__; len }
      | Some x → do { Stream.junk strm__; char (Buff.store len x) strm__ }
      | _ → raise Stream.Failure ]
;

value quote =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some '\\' → do {
          Stream.junk strm__;
          match strm__ with parser
          [ [: `c :] ->
              let len =
                try char (Buff.store (Buff.store 0 '\\') c) strm__ with
                [ Stream.Failure → raise (Stream.Error "") ]
              in
              ("CHAR", Buff.get len)
          | [: :] -> raise (Stream.Error "") ]
        }
      | Some x → do { Stream.junk strm__; char_or_quote_id x strm__ }
      | _ → raise Stream.Failure ]
;

value rec antiquot_rest bp len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some '$' → do { Stream.junk strm__; len }
      | Some x → do {
          Stream.junk strm__;
          try antiquot_rest bp (Buff.store len x) strm__ with
          [ Stream.Failure → raise (Stream.Error "") ]
        }
      | _ →
          let ep = Stream.count strm__ in
          Ploc.raise (Ploc.make_unlined (bp, ep))
            (Failure "antiquotation not terminated") ]
;

value antiloc d1 d2 s = Printf.sprintf "%d,%d:%s" d1 d2 s;

value rec antiquot_loc bp len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some '$' → do {
          Stream.junk strm__;
          let ep = Stream.count strm__ in
          antiloc bp ep (":" ^ Buff.get len)
        }
      | Some ('a'..'z' | 'A'..'Z' | '0'..'9' | '_' as c) → do {
          Stream.junk strm__;
          try antiquot_loc bp (Buff.store len c) strm__ with
          [ Stream.Failure → raise (Stream.Error "") ]
        }
      | Some ':' → do {
          Stream.junk strm__;
          let len =
            try antiquot_rest bp (Buff.store len ':') strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          antiloc bp ep (Buff.get len)
        }
      | Some c → do {
          Stream.junk strm__;
          let len =
            try antiquot_rest bp (Buff.store len c) strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          antiloc bp ep (":" ^ Buff.get len)
        }
      | _ →
          let ep = Stream.count strm__ in
          Ploc.raise (Ploc.make_unlined (bp, ep))
            (Failure "antiquotation not terminated") ]
;

value rec next_token_after_spaces kwt =
  parser bp
    [: :] ->
      match Stream.peek strm__ with
      [ Some '(' → do { Stream.junk strm__; (("", "("), (bp, bp + 1)) }
      | Some ')' → do { Stream.junk strm__; (("", ")"), (bp, bp + 1)) }
      | Some '[' → do { Stream.junk strm__; (("", "["), (bp, bp + 1)) }
      | Some ']' → do { Stream.junk strm__; (("", "]"), (bp, bp + 1)) }
      | Some '{' → do { Stream.junk strm__; (("", "{"), (bp, bp + 1)) }
      | Some '}' → do { Stream.junk strm__; (("", "}"), (bp, bp + 1)) }
      | Some '.' → do { Stream.junk strm__; (("DOT", ""), (bp, bp + 1)) }
      | Some '"' → do {
          Stream.junk strm__;
          let s =
            try string 0 strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (("STRING", s), (bp, ep))
        }
      | Some ''' → do {
          Stream.junk strm__;
          let tok =
            try quote strm__ with [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (tok, (bp, ep))
        }
      | Some '<' → do {
          Stream.junk strm__;
          let tok =
            try less kwt strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (tok, (bp, ep))
        }
      | Some '-' → do {
          Stream.junk strm__;
          let tok =
            try minus bp kwt strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (tok, (bp, ep))
        }
      | Some '#' → do {
          Stream.junk strm__;
          let tok =
            try sharp bp kwt strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (tok, (bp, ep))
        }
      | Some ('0'..'9' as c) → do {
          Stream.junk strm__;
          let tok =
            try number (Buff.store 0 c) strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (tok, (bp, ep))
        }
      | Some ('+' | '*' | '/' | '~' as c) → do {
          Stream.junk strm__;
          let len =
            try ident (Buff.store 0 c) strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let len =
            try operator len strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (identifier kwt (Buff.get len), (bp, ep))
        }
      | Some '$' → do {
          Stream.junk strm__;
          let tok =
            try dollar bp kwt strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (tok, (bp, ep))
        }
      | Some c → do {
          Stream.junk strm__;
          let len =
            try ident (Buff.store 0 c) strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          let ep = Stream.count strm__ in
          (identifier kwt (Buff.get len), (bp, ep))
        }
      | _ → (("EOI", ""), (bp, bp + 1)) ]
and dollar bp kwt strm =
  if Plexer.force_antiquot_loc.val then
    ("ANTIQUOT_LOC", antiquot_loc bp 0 strm)
  else
    match strm with parser
      [: :] ->
        let len = ident (Buff.store 0 '$') strm__ in
        identifier kwt (Buff.get len)
and sharp bp kwt =
  parser
  [ [: `'(' :] -> ("", "#(")
  | [: :] -> base_number kwt bp (Buff.store 0 '0') strm__ ]
and minus bp kwt =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some '.' → do { Stream.junk strm__; identifier kwt "-." }
      | Some ('0'..'9' as c) → do {
          Stream.junk strm__;
          try number (Buff.store (Buff.store 0 '-') c) strm__ with
          [ Stream.Failure → raise (Stream.Error "") ]
        }
      | Some '#' → do {
          Stream.junk strm__;
          try base_number kwt bp (Buff.mstore 0 "-0") strm__ with
          [ Stream.Failure → raise (Stream.Error "") ]
        }
      | _ →
          let len = ident (Buff.store 0 '-') strm__ in
          identifier kwt (Buff.get len) ]
and less kwt =
  parser
  [ [: `':' :] ->
      let lab =
        try label 0 strm__ with [ Stream.Failure → raise (Stream.Error "") ]
      in
      match strm__ with parser
      [ [: `'<' :] ->
          let q =
            try quotation 0 strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          ("QUOT", lab ^ ":" ^ q)
      | [: :] -> raise (Stream.Error "'<' expected") ]
  | [: :] ->
      let len = ident (Buff.store 0 '<') strm__ in
      identifier kwt (Buff.get len) ]
and label len =
  parser
  [ [: `('a'..'z' | 'A'..'Z' | '_' as c) :] -> label (Buff.store len c) strm__
  | [: :] -> Buff.get len ]
and quotation len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some '>' → do { Stream.junk strm__; quotation_greater len strm__ }
      | Some x → do {
          Stream.junk strm__;
          quotation (Buff.store len x) strm__
        }
      | _ → failwith "quotation not terminated" ]
and quotation_greater len =
  parser
  [ [: `'>' :] -> Buff.get len
  | [: :] -> quotation (Buff.store len '>') strm__ ]
;

value get_buff len _ = Buff.get len;

value rec lexer len kwt =
  parser bp
    [: :] ->
      match Stream.peek strm__ with
      [ Some ('\t' | '\r' as c) → do {
          Stream.junk strm__;
          lexer (Buff.store len c) kwt strm__
        }
      | Some ' ' → do {
          Stream.junk strm__;
          after_space (Buff.store len ' ') kwt strm__
        }
      | Some ';' → do {
          Stream.junk strm__;
          let len =
            try skip_to_eol (Buff.store len ';') strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          lexer len kwt strm__
        }
      | Some '\n' → do {
          Stream.junk strm__;
          let s = strm__ in
          let len = Buff.store len '\n' in
          if Sys.interactive.val then
            (Buff.get len, (("NL", ""), (bp, bp + 1)))
          else lexer len kwt s
        }
      | _ →
          let comm = get_buff len strm__ in
          let a =
            try next_token_after_spaces kwt strm__ with
            [ Stream.Failure → raise (Stream.Error "") ]
          in
          (comm, a) ]
and after_space len kwt =
  parser
  [ [: `'.' :] ->
      let ep = Stream.count strm__ in
      (Buff.get len, (("SPACEDOT", ""), (ep - 1, ep)))
  | [: :] -> lexer len kwt strm__ ]
;

value lexer_using kwt (con, prm) =
  match con with
  [ "CHAR" | "DOT" | "EOI" | "INT" | "INT_l" | "INT_L" | "INT_n" | "FLOAT" |
    "LIDENT" | "NL" | "QUOT" | "SPACEDOT" | "STRING" | "UIDENT" →
      ()
  | "ANTIQUOT" | "ANTIQUOT_LOC" → ()
  | "" → try Hashtbl.find kwt prm with [ Not_found → Hashtbl.add kwt prm () ]
  | _ →
      raise
        (Plexing.Error
           ("the constructor \"" ^ con ^ "\" is not recognized by Plexer")) ]
;

value lexer_text (con, prm) =
  if con = "" then "'" ^ prm ^ "'"
  else if prm = "" then con
  else con ^ " \"" ^ prm ^ "\""
;

value lexer_gmake () =
  let kwt = Hashtbl.create 89
  and lexer2 kwt (s, _, _) =
    let (comm, (t, loc)) = lexer 0 kwt s in
    (t, Ploc.make_loc Plexing.input_file.val 1 0 loc comm)
  in
  {Plexing.tok_func = Plexing.lexer_func_of_parser (lexer2 kwt);
   Plexing.tok_using = lexer_using kwt; Plexing.tok_removing = fun [];
   Plexing.tok_match = Plexing.default_match; Plexing.tok_text = lexer_text;
   Plexing.tok_comm = None}
;

(* Building AST *)

type sexpr =
  [ Sacc of MLast.loc and sexpr and sexpr
  | Santi of MLast.loc and string and string
  | Sarr of MLast.loc and MLast.v (list sexpr)
  | Schar of MLast.loc and MLast.v string
  | Sexpr of MLast.loc and list sexpr
  | Sint of MLast.loc and MLast.v string
  | Sint_l of MLast.loc and MLast.v string
  | Sint_L of MLast.loc and MLast.v string
  | Sint_n of MLast.loc and MLast.v string
  | Sfloat of MLast.loc and MLast.v string
  | Slid of MLast.loc and string
  | Slidv of MLast.loc and MLast.v string
  | Slist of MLast.loc and list sexpr
  | Squot of MLast.loc and string and string
  | Srec of MLast.loc and list sexpr
  | Sstring of MLast.loc and MLast.v string
  | Suid of MLast.loc and string
  | Suidv of MLast.loc and MLast.v string ]
;

value loc_of_sexpr =
  fun
  [ Sacc loc _ _ | Santi loc _ _ | Sarr loc _ | Schar loc _ | Sexpr loc _ |
    Sint loc _ | Sint_l loc _ | Sint_L loc _ | Sint_n loc _ | Sfloat loc _ |
    Slid loc _ | Slidv loc _ | Slist loc _ | Squot loc _ _ | Srec loc _ |
    Sstring loc _ | Suid loc _ | Suidv loc _ →
      loc ]
;
value error_loc loc err = Ploc.raise loc (Stream.Error (err ^ " expected"));
value error se err = error_loc (loc_of_sexpr se) err;
Pcaml.sync.val := fun _ → ();

value strm_n = "strm__";
value peek_fun loc = <:expr< Stream.peek >>;
value junk_fun loc = <:expr< Stream.junk >>;

value assoc_left_parsed_op_list =
  ["+"; "*"; "+."; "*."; "land"; "lor"; "lxor"]
;
value assoc_right_parsed_op_list = ["and"; "or"; "^"; "@"];
value and_by_couple_op_list = ["="; "<>"; "<"; ">"; "<="; ">="; "=="; "!="];

value op_apply loc e1 e2 =
  fun
  [ "and" → <:expr< $e1$ && $e2$ >>
  | "or" → <:expr< $e1$ || $e2$ >>
  | x → <:expr< $lid:x$ $e1$ $e2$ >> ]
;

value string_se =
  fun
  [ Sstring loc <:vala< s >> → s
  | se → error se "string" ]
;

value rec longident_se =
  fun
  [ Sacc _ se1 se2 → longident_se se1 @ longident_se se2
  | Suid _ s → [rename_id s]
  | Slid _ s → [rename_id s]
  | se → error se "longident" ]
;

value lident_expr loc s =
  if String.length s > 1 && s.[0] = '`' then
    let s = String.sub s 1 (String.length s - 1) in
    <:expr< ` $s$ >>
  else <:expr< $lid:(rename_id s)$ >>
;

value rec anti_list_map f =
  fun
  [ [Santi _ ("list" | "_list") s] → <:vala< $s$ >>
  | sel → <:vala< (List.map f sel) >> ]
;

value anti_longident_se =
  fun
  [ Santi _ ("list" | "_list" | "" | "_") s → <:vala< $s$ >>
  | se → <:vala< (longident_se se) >> ]
;

value anti_lid =
  fun
  [ Slid _ s →
      let s = rename_id s in
      Some <:vala< s >>
  | Slidv _ s → Some s
  | Santi _ ("" | "_") s → Some <:vala< $s$ >>
  | _ → None ]
;

value anti_lid_or_error =
  fun
  [ Slid _ s →
      let s = rename_id s in
      <:vala< s >>
  | Slidv _ s → s
  | Santi _ ("" | "_") s → <:vala< $s$ >>
  | se → error se "lowercase identifier" ]
;

value anti_uid_or_error =
  fun
  [ Suid _ s →
      let s = rename_id s in
      <:vala< s >>
  | Suidv _ s → s
  | Santi _ ("" | "_") s → <:vala< $s$ >>
  | se → error se "uppercase identifier" ]
;

value rec module_expr_se =
  fun
  [ Sexpr loc [Slid _ "functor"; se1; se2; se3] →
      let s = anti_uid_or_error se1 in
      let mt = module_type_se se2 in
      let me = module_expr_se se3 in
      <:module_expr< functor ($_uid:s$ : $mt$) -> $me$ >>
  | Sexpr loc [Slid _ "struct" :: sl] →
      let mel = anti_list_map str_item_se sl in
      <:module_expr< struct $_list:mel$ end >>
  | Sexpr loc [se1; se2] →
      let me1 = module_expr_se se1 in
      let me2 = module_expr_se se2 in
      <:module_expr< $me1$ $me2$ >>
  | Sexpr loc [Slid _ ":"; se1; se2] →
      let me = module_expr_se se1 in
      let mt = module_type_se se2 in
      <:module_expr< ($me$ : $mt$) >>
  | Sacc loc se1 se2 →
      let me1 = module_expr_se se1 in
      let me2 = module_expr_se se2 in
      <:module_expr< $me1$ . $me2$ >>
  | Suid loc s → <:module_expr< $uid:(rename_id s)$ >>
  | Suidv loc s → <:module_expr< $_uid:s$ >>
  | Santi loc "" s → <:module_expr< $xtr:s$ >>
  | se → error se "module expr" ]
and module_type_se =
  fun
  [ Sexpr loc [Slid _ "functor"; se1; se2; se3] →
      let s = anti_uid_or_error se1 in
      let mt1 = module_type_se se2 in
      let mt2 = module_type_se se3 in
      <:module_type< functor ($_uid:s$ : $mt1$) -> $mt2$ >>
  | Sexpr loc [Slid _ "sig" :: sel] →
      let sil = anti_list_map sig_item_se sel in
      <:module_type< sig $_list:sil$ end >>
  | Sexpr loc [Slid _ "with"; se :: sel] →
      let mt = module_type_se se in
      let wcl = anti_list_map with_constr_se sel in
      <:module_type< $mt$ with $_list:wcl$ >>
  | Sexpr loc [se1; se2] →
      let mt1 = module_type_se se1 in
      let mt2 = module_type_se se2 in
      <:module_type< $mt1$ $mt2$ >>
  | Sacc loc se1 se2 →
      let mt1 = module_type_se se1 in
      let mt2 = module_type_se se2 in
      <:module_type< $mt1$ . $mt2$ >>
  | Slid loc s → <:module_type< $lid:(rename_id s)$ >>
  | Slidv loc s → <:module_type< $_lid:s$ >>
  | Suid loc s → <:module_type< $uid:(rename_id s)$ >>
  | Suidv loc s → <:module_type< $_uid:s$ >>
  | Santi loc "" s → <:module_type< $xtr:s$ >>
  | se → error se "module type" ]
and with_constr_se =
  fun
  [ Sexpr loc [Slid _ ("type" | "typeprivate" as pf); se1; se2] →
      let (tn, tp) =
        match se1 with
        [ Santi _ ("list" | "_list") s → (<:vala< $s$ >>, <:vala< [] >>)
        | Sexpr _ [se :: sel] →
            let tn = anti_longident_se se in
            let tp = anti_list_map type_param_se sel in
            (tn, tp)
        | se → (<:vala< (longident_se se) >>, <:vala< [] >>) ]
      in
      let pf = pf = "typeprivate" in
      let te = ctyp_se se2 in
      <:with_constr< type $_:tn$ $_list:tp$ = $flag:pf$ $te$ >>
  | se → error se "with constr" ]
and sig_item_se =
  fun
  [ Sexpr loc [Slid _ "class"; se1; se2] →
      let (n, tvl) =
        match se1 with
        [ Slid _ n → (n, [])
        | Sexpr _ [Slid _ n :: sel] → (n, List.map type_param_se sel)
        | se → error se "class name" ]
      in
      let cd =
        {MLast.ciLoc = loc; MLast.ciVir = <:vala< False >>;
         MLast.ciPrm = (loc, <:vala< tvl >>); MLast.ciNam = <:vala< n >>;
         MLast.ciExp = class_type_se se2}
      in
      <:sig_item< class $list:[cd]$ >>
  | Sexpr loc [Slid _ "exception"; se :: sel] →
      let c = anti_uid_or_error se in
      let tl = anti_list_map ctyp_se sel in
      <:sig_item< exception $_:c$ of $_list:tl$ >>
  | Sexpr loc [Slid _ "external"; se1; se2 :: sel] →
      let i = anti_lid_or_error se1 in
      let t = ctyp_se se2 in
      let pd = anti_list_map string_se sel in
      <:sig_item< external $_lid:i$ : $t$ = $_list:pd$ >>
  | Sexpr loc [Slid _ "include"; se] →
      let mt = module_type_se se in
      <:sig_item< include $mt$ >>
  | Sexpr loc [Slid _ "module"; se1; se2] →
      let s = anti_uid_or_error se1 in
      let mb = module_type_se se2 in
      <:sig_item< module $_uid:s$ : $mb$ >>
  | Sexpr loc [Slid _ ("module*" | "modulerec*" as rf) :: sel] →
      let rf = rf = "modulerec*"
      and lmb = anti_list_map sig_module_se sel in
      <:sig_item< module $flag:rf$ $_list:lmb$ >>
  | Sexpr loc [Slid _ "moduletype"; se1; se2] →
      let s = anti_uid_or_error se1 in
      let mt = module_type_se se2 in
      <:sig_item< module type $_:s$ = $mt$ >>
  | Sexpr loc [Slid _ "open"; se] →
      let s = anti_longident_se se in
      <:sig_item< open $_:s$ >>
  | Sexpr loc [Slid _ "type" :: sel] →
      let tdl = type_declaration_list_se sel in
      <:sig_item< type $list:tdl$ >>
  | Sexpr loc [Slid _ "type*" :: sel] →
      let tdl = anti_list_map type_declaration_se sel in
      <:sig_item< type $_list:tdl$ >>
  | Sexpr loc [Slid _ "value"; se1; se2] →
      let s = anti_lid_or_error se1 in
      let t = ctyp_se se2 in
      <:sig_item< value $_lid:s$ : $t$ >>
  | Sexpr loc [Slid _ "#"; se1] →
      let s = anti_lid_or_error se1 in
      <:sig_item< # $_lid:s$ >>
  | Sexpr loc [Slid _ "#"; se1; se2] →
      let s = anti_lid_or_error se1
      and e = expr_se se2 in
      <:sig_item< # $_lid:s$ $e$ >>
  | se → error se "sig item" ]
and str_item_se se =
  match se with
  [ Sexpr loc [Slid _ "class"; Slid _ s; se] →
      let ce = class_expr_se se in
      <:str_item< class $s$ = $ce$ >>
  | Sexpr loc [Slid _ "class"; Sexpr _ [Slid _ s :: sel]; se] →
      let tpl = List.map type_param_se sel
      and ce = class_expr_se se in
      <:str_item< class $s$ [ $list:tpl$ ] = $ce$ >>
  | Sexpr loc [Slid _ ("define" | "definerec" as r); se :: sel] →
      let r = r = "definerec" in
      let (p, e) = fun_binding_se se (begin_se loc sel) in
      <:str_item< value $flag:r$ $p$ = $e$ >>
  | Sexpr loc [Slid _ ("define*" | "definerec*" as rf) :: sel] →
      let rf = rf = "definerec*" in
      let lbs = anti_list_map let_binding_se sel in
      <:str_item< value $flag:rf$ $_list:lbs$ >>
  | Sexpr loc [Slid _ "exception"; se :: sel] →
      let c = anti_uid_or_error se in
      let tl = anti_list_map ctyp_se sel in
      <:str_item< exception $_:c$ of $_list:tl$ >>
  | Sexpr loc [Slid _ "exceptionrebind"; se1; se2] →
      let c = anti_uid_or_error se1 in
      let id = anti_longident_se se2 in
      <:str_item< exception $_uid:c$ = $_:id$ >>
  | Sexpr loc [Slid _ "external"; se1; se2 :: sel] →
      let i = anti_lid_or_error se1 in
      let t = ctyp_se se2 in
      let pd = anti_list_map string_se sel in
      <:str_item< external $_lid:i$ : $t$ = $_list:pd$ >>
  | Sexpr loc [Slid _ "include"; se] →
      let me = module_expr_se se in
      <:str_item< include $me$ >>
  | Sexpr loc [Slid _ "module"; se1; se2] →
      let (i, mb) = str_module_se (Sexpr loc [se1; se2]) in
      <:str_item< module $_uid:i$ = $mb$ >>
  | Sexpr loc [Slid _ ("module*" | "modulerec*" as rf) :: sel] →
      let rf = rf = "modulerec*" in
      let lmb = anti_list_map str_module_se sel in
      <:str_item< module $flag:rf$ $_list:lmb$ >>
  | Sexpr loc [Slid _ "moduletype"; se1; se2] →
      let s = anti_uid_or_error se1 in
      let mt = module_type_se se2 in
      <:str_item< module type $_:s$ = $mt$ >>
  | Sexpr loc [Slid _ "open"; se] →
      let s = anti_longident_se se in
      <:str_item< open $_:s$ >>
  | Sexpr loc [Slid _ "type" :: sel] →
      let tdl = type_declaration_list_se sel in
      <:str_item< type $list:tdl$ >>
  | Sexpr loc [Slid _ "type*" :: sel] →
      let tdl = anti_list_map type_declaration_se sel in
      <:str_item< type $_list:tdl$ >>
  | Sexpr loc [Slid _ "#"; se1] →
      match anti_lid se1 with
      [ Some s → <:str_item< # $_lid:s$ >>
      | None →
          let loc = loc_of_sexpr se in
          let e = expr_se se in
          <:str_item< $exp:e$ >> ]
  | Sexpr loc [Slid _ "#"; se1; se2] →
      match anti_lid se1 with
      [ Some s →
          let e = expr_se se2 in
          <:str_item< # $_lid:s$ $e$ >>
      | None →
          let loc = loc_of_sexpr se in
          let e = expr_se se in
          <:str_item< $exp:e$ >> ]
  | _ →
      let loc = loc_of_sexpr se in
      let e = expr_se se in
      <:str_item< $exp:e$ >> ]
and str_module_se =
  fun
  [ Sexpr loc [se1; se2] → (anti_uid_or_error se1, module_expr_se se2)
  | se → error se "module binding" ]
and sig_module_se =
  fun
  [ Sexpr loc [se1; se2] → (anti_uid_or_error se1, module_type_se se2)
  | se → error se "module binding" ]
and expr_se =
  fun
  [ Sacc loc se1 se2 →
      let e1 = expr_se se1 in
      match se2 with
      [ Slist loc [se2] →
          let e2 = expr_se se2 in
          <:expr< $e1$ .[ $e2$ ] >>
      | Sexpr loc [se2] →
          let e2 = expr_se se2 in
          <:expr< $e1$ .( $e2$ ) >>
      | _ →
          let e2 = expr_se se2 in
          <:expr< $e1$ . $e2$ >> ]
  | Slid loc s → lident_expr loc s
  | Slidv loc s → <:expr< $_lid:s$ >>
  | Suid loc s → <:expr< $uid:(rename_id s)$ >>
  | Suidv loc s → <:expr< $_uid:s$ >>
  | Sint loc s → <:expr< $_int:s$ >>
  | Sint_l loc s → <:expr< $_int32:s$ >>
  | Sint_L loc s → <:expr< $_int64:s$ >>
  | Sint_n loc s → <:expr< $_nativeint:s$ >>
  | Sfloat loc s → <:expr< $_flo:s$ >>
  | Schar loc s → <:expr< $_chr:s$ >>
  | Sstring loc s → <:expr< $_str:s$ >>
  | Sexpr loc [Slid _ "~"; se] →
      let s = anti_lid_or_error se in
      <:expr< ~{$_:s$} >>
  | Sexpr loc [Slid _ "~"; se1; se2] →
      let s = anti_lid_or_error se1 in
      let e = expr_se se2 in
      <:expr< ~{$_:s$ = $e$} >>
  | Sexpr loc [Slid _ "?"; se1; se2] →
      let s = anti_lid_or_error se1 in
      let e = expr_se se2 in
      <:expr< ?{$_:s$ = $e$} >>
  | Sexpr loc [Slid _ "?"; se] →
      let s = anti_lid_or_error se in
      <:expr< ?{$_:s$} >>
  | Sexpr loc [] → <:expr< () >>
  | Sexpr loc [Slid _ s; e1 :: ([_ :: _] as sel)]
    when List.mem s assoc_left_parsed_op_list →
      loop (expr_se e1) (List.map expr_se sel) where rec loop e1 =
        fun
        [ [] → e1
        | [e2 :: el] → loop (op_apply loc e1 e2 s) el ]
  | Sexpr loc [Slid _ s :: ([_; _ :: _] as sel)]
    when List.mem s assoc_right_parsed_op_list →
      loop (List.map expr_se sel) where rec loop =
        fun
        [ [] → assert False
        | [e1] → e1
        | [e1 :: el] →
            let e2 = loop el in
            op_apply loc e1 e2 s ]
  | Sexpr loc [Slid _ s :: ([_; _ :: _] as sel)]
    when List.mem s and_by_couple_op_list →
      loop (List.map expr_se sel) where rec loop =
        fun
        [ [] | [_] → assert False
        | [e1; e2] → <:expr< $lid:s$ $e1$ $e2$ >>
        | [e1 :: ([e2; _ :: _] as el)] →
            let a1 = op_apply loc e1 e2 s in
            let a2 = loop el in
            <:expr< $a1$ && $a2$ >> ]
  | Sexpr loc [Slid _ "-"; se] →
      let e = expr_se se in
      <:expr< - $e$ >>
  | Sexpr loc [Slid _ "-."; se] →
      let e = expr_se se in
      <:expr< -. $e$ >>
  | Sexpr loc [Slid _ "if"; se; se1] →
      let e = expr_se se in
      let e1 = expr_se se1 in
      <:expr< if $e$ then $e1$ else () >>
  | Sexpr loc [Slid _ "if"; se; se1; se2] →
      let e = expr_se se in
      let e1 = expr_se se1 in
      let e2 = expr_se se2 in
      <:expr< if $e$ then $e1$ else $e2$ >>
  | Sexpr loc [Slid _ "cond" :: sel] →
      loop sel where rec loop =
        fun
        [ [Sexpr loc [Slid _ "else" :: sel]] → begin_se loc sel
        | [Sexpr loc [se1 :: sel1] :: sel] →
            let e1 = expr_se se1 in
            let e2 = begin_se loc sel1 in
            let e3 = loop sel in
            <:expr< if $e1$ then $e2$ else $e3$ >>
        | [] → <:expr< () >>
        | [se :: _] → error se "cond clause" ]
  | Sexpr loc [Slid _ "while"; se :: sel] →
      let e = expr_se se in
      let el = anti_list_map expr_se sel in
      <:expr< while $e$ do { $_list:el$ } >>
  | Sexpr loc [Slid _ ("for" | "fordown" as d); sei; se1; se2 :: sel] →
      let i = anti_lid_or_error sei in
      let e1 = expr_se se1 in
      let e2 = expr_se se2 in
      let dir = d = "for" in
      let el = anti_list_map expr_se sel in
      <:expr< for $_lid:i$ = $e1$ $to:dir$ $e2$ do { $_list:el$ } >>
  | Sexpr loc [Slid loc1 "lambda"] → <:expr< fun [] >>
  | Sexpr loc [Slid loc1 "lambda"; sep :: sel] →
      let e = begin_se loc1 sel in
      match ipatt_opt_se sep with
      [ Left p → <:expr< fun $p$ -> $e$ >>
      | Right (se, sel) →
          List.fold_right
            (fun se e →
               let p = ipatt_se se in
               <:expr< fun $p$ -> $e$ >>)
            [se :: sel] e ]
  | Sexpr loc [Slid _ "lambda_match" :: sel] →
      let pel =
        match sel with
        [ [Sexpr _ [Santi loc ("list" | "_list") s]] → <:vala< $s$ >>
        | _ → <:vala< (List.map (match_case loc) sel) >> ]
      in
      <:expr< fun [ $_list:pel$ ] >>
  | Sexpr loc [Slid _ ("let" | "letrec" as r) :: sel] →
      match sel with
      [ [Sexpr _ sel1 :: sel2] →
          let r = r = "letrec" in
          let lbs = anti_list_map let_binding_se sel1 in
          let e = begin_se loc sel2 in
          <:expr< let $flag:r$ $_list:lbs$ in $e$ >>
      | [Slid _ n; Sexpr _ sl :: sel] →
          let n = rename_id n in
          let (pl, el) =
            List.fold_right
              (fun se (pl, el) →
                 match se with
                 [ Sexpr _ [se1; se2] →
                     ([patt_se se1 :: pl], [expr_se se2 :: el])
                 | se → error se "named let" ])
              sl ([], [])
          in
          let e1 =
            List.fold_right (fun p e → <:expr< fun $p$ -> $e$ >>) pl
              (begin_se loc sel)
          in
          let e2 =
            List.fold_left (fun e1 e2 → <:expr< $e1$ $e2$ >>)
              <:expr< $lid:n$ >> el
          in
          <:expr< let rec $lid:n$ = $e1$ in $e2$ >>
      | [se :: _] → error se "let_binding"
      | _ → error_loc loc "let_binding" ]
  | Sexpr loc [Slid _ "let*" :: sel] →
      match sel with
      [ [Sexpr _ sel1 :: sel2] →
          List.fold_right
            (fun se ek →
               let (p, e) = let_binding_se se in
               <:expr< let $p$ = $e$ in $ek$ >>)
            sel1 (begin_se loc sel2)
      | [se :: _] → error se "let_binding"
      | _ → error_loc loc "let_binding" ]
  | Sexpr loc [Slid _ "letmodule"; se1; se2; se3] →
      let s = anti_uid_or_error se1 in
      let me = module_expr_se se2 in
      let e = expr_se se3 in
      <:expr< let module $_:s$ = $me$ in $e$ >>
  | Sexpr loc [Slid _ "match"; se :: sel] →
      let e = expr_se se in
      let pel =
        match sel with
        [ [Sexpr _ [Santi _ ("list" | "_list") s]] → <:vala< $s$ >>
        | _ → <:vala< (List.map (match_case loc) sel) >> ]
      in
      <:expr< match $e$ with [ $_list:pel$ ] >>
  | Sexpr loc [Slid _ "parser" :: sel] →
      let (po, sel) =
        match sel with
        [ [(Slid _ _ as se) :: sel] → (Some (patt_se se), sel)
        | sel → (None, sel) ]
      in
      let pcl = List.map parser_case_se sel in
      Exparser.cparser loc po pcl
  | Sexpr loc [Slid _ "match_with_parser"; se :: sel] →
      let e = expr_se se in
      let (po, sel) =
        match sel with
        [ [(Slid _ _ as se) :: sel] → (Some (patt_se se), sel)
        | sel → (None, sel) ]
      in
      let pcl = List.map parser_case_se sel in
      Exparser.cparser_match loc e po pcl
  | Sexpr loc [Slid _ "try"; se :: sel] →
      let e = expr_se se in
      let pel =
        match sel with
        [ [Sexpr _ [Santi _ ("list" | "_list") s]] → <:vala< $s$ >>
        | _ → <:vala< (List.map (match_case loc) sel) >> ]
      in
      <:expr< try $e$ with [ $_list:pel$ ] >>
  | Sexpr loc [Slid _ "begin" :: sel] →
      let el = anti_list_map expr_se sel in
      <:expr< do { $_list:el$ } >>
  | Sexpr loc [Slid _ ":="; se1; se2] →
      let e1 = expr_se se1 in
      let e2 = expr_se se2 in
      <:expr< $e1$ := $e2$ >>
  | Sarr loc sel →
      let el = Pcaml.vala_map (List.map expr_se) sel in
      <:expr< [| $_list:el$ |] >>
  | Sexpr loc [Slid _ "values" :: sel] →
      let el = anti_list_map expr_se sel in
      <:expr< ($_list:el$) >>
  | Srec loc [Slid _ "with"; se :: sel] →
      let e = expr_se se
      and lel = anti_list_map (label_expr_se loc) sel in
      <:expr< { ($e$) with $_list:lel$ } >>
  | Srec loc sel →
      let lel = anti_list_map (label_expr_se loc) sel in
      <:expr< { $_list:lel$ } >>
  | Sexpr loc [Slid _ ":"; se1; se2] →
      let e = expr_se se1 in
      let t = ctyp_se se2 in
      <:expr< ($e$ : $t$) >>
  | Sexpr loc [se] →
      let e = expr_se se in
      <:expr< $e$ () >>
  | Sexpr loc [Slid _ "assert"; se] →
      let e = expr_se se in
      <:expr< assert $e$ >>
  | Sexpr loc [Slid _ "lazy"; se] →
      let e = expr_se se in
      <:expr< lazy $e$ >>
  | Sexpr loc [Slid _ "new"; se] →
      let sl = anti_longident_se se in
      <:expr< new $_list:sl$ >>
  | Sexpr loc [Slid _ "`"; Suid _ s] → <:expr< ` $s$ >>
  | Sexpr loc [Slid _ "send"; se; Slid _ s] →
      let e = expr_se se in
      <:expr< $e$ # $s$ >>
  | Sexpr loc [se :: sel] →
      List.fold_left
        (fun e se →
           let e1 = expr_se se in
           <:expr< $e$ $e1$ >>)
        (expr_se se) sel
  | Slist loc sel →
      loop sel where rec loop =
        fun
        [ [] → <:expr< [] >>
        | [se1; Slid _ "."; se2] →
            let e = expr_se se1 in
            let el = expr_se se2 in
            <:expr< [$e$ :: $el$] >>
        | [se :: sel] →
            let e = expr_se se in
            let el = loop sel in
            <:expr< [$e$ :: $el$] >> ]
  | Squot loc typ txt → Pcaml.handle_expr_quotation loc (typ, txt)
  | Santi loc "" s → <:expr< $xtr:s$ >>
  | Santi loc _ s → error_loc loc "expr" ]
and begin_se loc =
  fun
  [ [] → <:expr< () >>
  | [se] → expr_se se
  | sel →
      let el = List.map expr_se sel in
      let loc = Ploc.encl (loc_of_sexpr (List.hd sel)) loc in
      <:expr< do { $list:el$ } >> ]
and let_binding_se =
  fun
  [ Sexpr loc [se :: sel] →
      let e = begin_se loc sel in
      match ipatt_opt_se se with
      [ Left p → (p, e)
      | Right _ → fun_binding_se se e ]
  | se → error se "let_binding" ]
and fun_binding_se se e =
  match se with
  [ Sexpr _ [Slid _ "values" :: _] → (ipatt_se se, e)
  | Sexpr _ [Slid _ ":"; _; _] → (ipatt_se se, e)
  | Sexpr _ [se1 :: sel] →
      match ipatt_opt_se se1 with
      [ Left p →
          let e =
            List.fold_right
              (fun se e →
                 let loc =
                   Ploc.encl (loc_of_sexpr se) (MLast.loc_of_expr e)
                 in
                 let p = ipatt_se se in
                 <:expr< fun $p$ -> $e$ >>)
              sel e
          in
          (p, e)
      | Right _ → (ipatt_se se, e) ]
  | _ → (ipatt_se se, e) ]
and match_case loc =
  fun
  [ Sexpr loc [Sexpr _ [Slid _ "when"; se; sew] :: sel] →
      (patt_se se, <:vala< (Some (expr_se sew)) >>, begin_se loc sel)
  | Sexpr loc [se :: sel] → (patt_se se, <:vala< None >>, begin_se loc sel)
  | se → error se "match_case" ]
and label_expr_se loc =
  fun
  [ Sexpr _ [se1; se2] → (patt_se se1, expr_se se2)
  | se → error se "label_expr" ]
and label_patt_se loc =
  fun
  [ Sexpr _ [se1; se2] → (patt_se se1, patt_se se2)
  | se → error se "label_patt" ]
and label_ipatt_se loc =
  fun
  [ Sexpr _ [se1; se2] → (ipatt_se se1, ipatt_se se2)
  | se → error se "label_ipatt" ]
and parser_case_se =
  fun
  [ Sexpr _ [Sexpr _ sel; se1; se2] →
      let sp = stream_patt_se sel in
      let po = Some (ipatt_se se1) in
      let e = expr_se se2 in
      (sp, po, e)
  | Sexpr _ [Sexpr _ sel; se] →
      let sp = stream_patt_se sel in
      let e = expr_se se in
      (sp, None, e)
  | se → error se "parser_case" ]
and stream_patt_se =
  fun
  [ [se :: sel] →
      let spc = stream_patt_comp_se se in
      let sp = stream_patt_kont_se sel in
      [(spc, SpoNoth) :: sp]
  | [] → [] ]
and stream_patt_kont_se =
  fun
  [ [se; Slid _ "!" :: sel] →
      let spc = stream_patt_comp_se se in
      let sp = stream_patt_kont_se sel in
      [(spc, SpoBang) :: sp]
  | [se1; Slid _ "?"; se2 :: sel] →
      let spc = stream_patt_comp_se se1 in
      let e = expr_se se2 in
      let sp = stream_patt_kont_se sel in
      [(spc, SpoQues e) :: sp]
  | [se :: sel] →
      let spc = stream_patt_comp_se se in
      let sp = stream_patt_kont_se sel in
      [(spc, SpoNoth) :: sp]
  | [] → [] ]
and stream_patt_comp_se =
  fun
  [ Sexpr loc [Slid _ "`"; se] → SpTrm loc (patt_se se) <:vala< None >>
  | Sexpr loc [Slid _ "`"; se1; se2] →
      let e = expr_se se2 in
      SpTrm loc (patt_se se1) <:vala< (Some e) >>
  | Sexpr loc [Slid _ "let"; se1; se2] →
      SpLet loc (ipatt_se se1) (expr_se se2)
  | Sexpr loc [se1; se2] → SpNtr loc (patt_se se1) (expr_se se2)
  | se → SpStr (loc_of_sexpr se) (patt_se se) ]
and patt_se =
  fun
  [ Sacc loc se1 se2 →
      let p1 = patt_se se1 in
      let p2 = patt_se se2 in
      <:patt< $p1$ . $p2$ >>
  | Slid loc "_" → <:patt< _ >>
  | Slid loc s → <:patt< $lid:(rename_id s)$ >>
  | Slidv loc s → <:patt< $_lid:s$ >>
  | Suid loc s → <:patt< $uid:(rename_id s)$ >>
  | Suidv loc s → <:patt< $_uid:s$ >>
  | Sint loc s → <:patt< $_int:s$ >>
  | Sint_l loc s → <:patt< $_int32:s$ >>
  | Sint_L loc s → <:patt< $_int64:s$ >>
  | Sint_n loc s → <:patt< $_nativeint:s$ >>
  | Sfloat loc s → <:patt< $_flo:s$ >>
  | Schar loc s → <:patt< $_chr:s$ >>
  | Sstring loc s → <:patt< $_str:s$ >>
  | Sexpr loc [Slid _ "~"; se] →
      let s = anti_lid_or_error se in
      <:patt< ~{$_:s$} >>
  | Sexpr loc [Slid _ "~"; se1; se2] →
      let s = anti_lid_or_error se1
      and p = patt_se se2 in
      <:patt< ~{$_:s$ = $p$} >>
  | Sexpr loc [Slid _ "?"; se] →
      match se with
      [ Sexpr _ [se1; se2] →
          let s = anti_lid_or_error se1
          and e = expr_se se2 in
          <:patt< ?{$_:s$ = $e$} >>
      | se →
          let s = anti_lid_or_error se in
          <:patt< ?{$_:s$} >> ]
  | Sexpr loc [Slid _ "?"; se1; se2] →
      let e = expr_se se2 in
      match se1 with
      [ Sexpr _ [se1; se2] →
          let s = anti_lid_or_error se1
          and p = patt_se se2 in
          <:patt< ?{$_:s$ = ?{$p$ = $e$}} >>
      | se →
          let s = anti_lid_or_error se in
          <:patt< ?{$_:s$ = $e$} >> ]
  | Srec loc sel →
      let lpl = anti_list_map (label_patt_se loc) sel in
      <:patt< { $_list:lpl$ } >>
  | Sexpr loc [Slid _ ":"; se1; se2] →
      let p = patt_se se1 in
      let t = ctyp_se se2 in
      <:patt< ($p$ : $t$) >>
  | Sexpr loc [Slid _ "or"; se :: sel] →
      List.fold_left
        (fun p se →
           let p1 = patt_se se in
           <:patt< $p$ | $p1$ >>)
        (patt_se se) sel
  | Sexpr loc [Slid _ "range"; se1; se2] →
      let p1 = patt_se se1 in
      let p2 = patt_se se2 in
      <:patt< $p1$ .. $p2$ >>
  | Sarr loc sel →
      let pl = Pcaml.vala_map (List.map patt_se) sel in
      <:patt< [| $_list:pl$ |] >>
  | Sexpr loc [Slid _ "values" :: sel] →
      let pl = anti_list_map patt_se sel in
      <:patt< ($_list:pl$) >>
  | Sexpr loc [Slid _ "as"; se1; se2] →
      let p1 = patt_se se1 in
      let p2 = patt_se se2 in
      <:patt< ($p1$ as $p2$) >>
  | Sexpr loc [Slid _ "`"; Suid _ s] → <:patt< ` $s$ >>
  | Sexpr loc [se :: sel] →
      List.fold_left
        (fun p se →
           let p1 = patt_se se in
           <:patt< $p$ $p1$ >>)
        (patt_se se) sel
  | Sexpr loc [] → <:patt< () >>
  | Slist loc sel →
      loop sel where rec loop =
        fun
        [ [] → <:patt< [] >>
        | [se1; Slid _ "."; se2] →
            let p = patt_se se1 in
            let pl = patt_se se2 in
            <:patt< [$p$ :: $pl$] >>
        | [se :: sel] →
            let p = patt_se se in
            let pl = loop sel in
            <:patt< [$p$ :: $pl$] >> ]
  | Squot loc typ txt → Pcaml.handle_patt_quotation loc (typ, txt)
  | Santi loc "" s → <:patt< $xtr:s$ >>
  | Santi loc _ s → error_loc loc "patt" ]
and ipatt_se se =
  match ipatt_opt_se se with
  [ Left p → p
  | Right _ → patt_se se ]
and ipatt_opt_se =
  fun
  [ Slid loc "_" → Left <:patt< _ >>
  | Slid loc s → Left <:patt< $lid:(rename_id s)$ >>
  | Sexpr loc [Slid _ "~"; Slid _ s] → Left <:patt< ~{$lid:s$} >>
  | Sexpr loc [Slid _ "~"; Slid _ s; se] →
      let p = patt_se se in
      Left <:patt< ~{$lid:s$ = $p$} >>
  | Sexpr loc [Slid _ "?"; se] →
      match se with
      [ Sexpr _ [se1; Slid _ p] →
          let s = anti_lid_or_error se1 in
          Left <:patt< ?{$_:s$ = $lid:p$} >>
      | se →
          let s = anti_lid_or_error se in
          Left <:patt< ?{$_:s$} >> ]
  | Sexpr loc [Slid _ "?"; se1; se2] →
      let e = expr_se se2 in
      match se1 with
      [ Sexpr _ [se1; Slid _ p] →
          let s = anti_lid_or_error se1 in
          Left <:patt< ?{$_:s$ = ?{$lid:p$ = $e$}} >>
      | se →
          let s = anti_lid_or_error se in
          Left <:patt< ?{$_:s$ = $e$} >> ]
  | Sexpr loc [Slid _ ":"; se1; se2] →
      let p = ipatt_se se1 in
      let t = ctyp_se se2 in
      Left <:patt< ($p$ : $t$) >>
  | Sexpr loc [Slid _ "as"; se1; se2] →
      let p1 = ipatt_se se1 in
      let p2 = ipatt_se se2 in
      Left <:patt< ($p1$ as $p2$) >>
  | Sexpr loc [Slid _ "values" :: sel] →
      let pl = List.map ipatt_se sel in
      Left <:patt< ( $list:pl$ ) >>
  | Srec loc sel →
      let lpl = List.map (label_ipatt_se loc) sel in
      Left <:patt< { $list:lpl$ } >>
  | Sexpr loc [] → Left <:patt< () >>
  | Sexpr loc [se :: sel] → Right (se, sel)
  | se → error se "ipatt" ]
and type_declaration_se =
  fun
  [ Sexpr loc [se1; se2] →
      let (n1, loc1, tpl) =
        match se1 with
        [ Sexpr _ [Slid loc n :: sel] →
            (rename_id n, loc, List.map type_param_se sel)
        | Slid loc n → (rename_id n, loc, [])
        | se → error se "type declaration" ]
      in
      let n = (loc1, <:vala< n1 >>) in
      {MLast.tdNam = <:vala< n >>; MLast.tdPrm = <:vala< tpl >>;
       MLast.tdPrv = <:vala< False >>; MLast.tdDef = ctyp_se se2;
       MLast.tdCon = <:vala< [] >>}
  | se → error se "type_decl" ]
and type_declaration_list_se =
  fun
  [ [se1; se2 :: sel] →
      let (n1, loc1, tpl) =
        match se1 with
        [ Sexpr _ [Slid loc n :: sel] →
            (rename_id n, loc, List.map type_param_se sel)
        | Slid loc n → (rename_id n, loc, [])
        | se → error se "type declaration" ]
      in
      let n = (loc1, <:vala< n1 >>) in
      let td =
        {MLast.tdNam = <:vala< n >>; MLast.tdPrm = <:vala< tpl >>;
         MLast.tdPrv = <:vala< False >>; MLast.tdDef = ctyp_se se2;
         MLast.tdCon = <:vala< [] >>}
      in
      [td :: type_declaration_list_se sel]
  | [] → []
  | [se :: _] → error se "type_decl" ]
and type_param_se se =
  match se with
  [ Slid _ s when String.length s >= 2 && s.[0] = ''' →
      let s = String.sub s 1 (String.length s - 1) in
      (<:vala< (Some s) >>, None)
  | Slid _ s when String.length s >= 3 && s.[1] = ''' →
      let vara =
        if s.[0] = '+' then Some True
        else if s.[0] = '-' then Some False
        else error se "type_param"
      and s = String.sub s 2 (String.length s - 2) in
      (<:vala< (Some s) >>, vara)
  | se → error se "type_param" ]
and ctyp_se =
  fun
  [ Sexpr loc [Slid _ "sum" :: sel] →
      let cdl = anti_list_map constructor_declaration_se sel in
      <:ctyp< [ $_list:cdl$ ] >>
  | Sexpr loc [Slid _ "variants" :: sel] →
      let cdl = anti_list_map variant_declaration_se sel in
      <:ctyp< [ = $_list:cdl$ ] >>
  | Sexpr loc [Slid _ "variantsless" :: sel] →
      let cdl = anti_list_map variant_declaration_se sel in
      <:ctyp< [ < $_list:cdl$ ] >>
  | Sexpr loc [Slid _ "variantsgreater" :: sel] →
      let cdl = anti_list_map variant_declaration_se sel in
      <:ctyp< [ > $_list:cdl$ ] >>
  | Srec loc sel →
      let ldl = anti_list_map label_declaration_se sel in
      <:ctyp< { $_list:ldl$ } >>
  | Sexpr loc [Slid _ "->" :: ([_; _ :: _] as sel)] →
      loop sel where rec loop =
        fun
        [ [] → assert False
        | [se] → ctyp_se se
        | [se :: sel] →
            let t1 = ctyp_se se in
            let loc = Ploc.encl (loc_of_sexpr se) loc in
            let t2 = loop sel in
            <:ctyp< $t1$ -> $t2$ >> ]
  | Sexpr loc [Slid _ "as"; se1; se2] →
      let t1 = ctyp_se se1 in
      let t2 = ctyp_se se2 in
      <:ctyp< ($t1$ as $t2$) >>
  | Sexpr loc [Slid _ "*" :: sel] →
      let tl = anti_list_map ctyp_se sel in
      <:ctyp< ($_list:tl$) >>
  | Sexpr loc [Slid _ "=="; se1; se2] →
      let t1 = ctyp_se se1 in
      let t2 = ctyp_se se2 in
      <:ctyp< $t1$ == $t2$ >>
  | Sexpr loc [Slid _ "?"; se1; se2] →
      let s = anti_lid_or_error se1
      and t = ctyp_se se2 in
      <:ctyp< ?$_:s$: $t$ >>
  | Sexpr loc [Slid _ "~"; se1; se2] →
      let s = anti_lid_or_error se1
      and t = ctyp_se se2 in
      <:ctyp< ~$_:s$: $t$ >>
  | Sexpr loc [Slid _ "object" :: sel] →
      let fl = object_field_list_se sel in
      <:ctyp< < $_list:fl$ > >>
  | Sexpr loc [Slid _ "objectvar" :: sel] →
      let fl = object_field_list_se sel in
      <:ctyp< < $_list:fl$ .. > >>
  | Sexpr loc [se :: sel] →
      List.fold_left
        (fun t se →
           let t2 = ctyp_se se in
           <:ctyp< $t$ $t2$ >>)
        (ctyp_se se) sel
  | Sacc loc se1 se2 →
      let t1 = ctyp_se se1 in
      let t2 = ctyp_se se2 in
      <:ctyp< $t1$ . $t2$ >>
  | Slid loc "_" → <:ctyp< _ >>
  | Slid loc s →
      if s.[0] = ''' then
        let s = String.sub s 1 (String.length s - 1) in
        <:ctyp< '$s$ >>
      else <:ctyp< $lid:(rename_id s)$ >>
  | Slidv loc s → <:ctyp< $_lid:s$ >>
  | Suid loc s → <:ctyp< $uid:(rename_id s)$ >>
  | Suidv loc s → <:ctyp< $_uid:s$ >>
  | Santi loc "" s → <:ctyp< $xtr:s$ >>
  | se → error se "ctyp" ]
and object_field_list_se sel =
  anti_list_map
    (fun
     [ Sexpr loc [Slid _ s; se] →
         let t = ctyp_se se in
         (s, t)
     | se → error_loc (loc_of_sexpr se) "object field" ])
    sel
and constructor_declaration_se =
  fun
  [ Sexpr loc [Suid _ ci :: sel] →
      (loc, <:vala< (rename_id ci) >>, <:vala< (List.map ctyp_se sel) >>,
       None)
  | se → error se "constructor_declaration" ]
and variant_declaration_se =
  fun
  [ Sexpr loc [Slid _ "`"; Suid _ s] → <:poly_variant< ` $s$ >>
  | Sexpr loc [Slid _ "`"; Suid _ s :: sel] →
      let (a, sel) =
        match sel with
        [ [Slid _ "&" :: sel] → (True, sel)
        | sel → (False, sel) ]
      in
      let tl = List.map ctyp_se sel in
      <:poly_variant< ` $s$ of $flag:a$ $list:tl$ >>
  | se →
      let t = ctyp_se se in
      let loc = loc_of_sexpr se in
      <:poly_variant< $t$ >> ]
and label_declaration_se =
  fun
  [ Sexpr loc [Slid _ lab; Slid _ "mutable"; se] →
      (loc, rename_id lab, True, ctyp_se se)
  | Sexpr loc [Slid _ lab; se] → (loc, rename_id lab, False, ctyp_se se)
  | se → error se "label_declaration" ]
and class_sig_item_se =
  fun
  [ Sexpr loc [Slid _ "method"; Slid _ n; se] →
      let t = ctyp_se se in
      <:class_sig_item< method $n$ : $t$ >>
  | Sexpr loc [Slid _ "value"; Slid _ "mutable"; Slid _ n; se] →
      let t = ctyp_se se in
      <:class_sig_item< value mutable $n$ : $t$ >>
  | se → error se "class_sig_item" ]
and class_str_item_se =
  fun
  [ Sexpr loc [Slid _ "inherit"; se; Slid _ s] →
      let ce = class_expr_se se in
      <:class_str_item< inherit $ce$ $opt:(Some s)$ >>
  | Sexpr loc [Slid _ "inherit"; se] →
      let ce = class_expr_se se in
      <:class_str_item< inherit $ce$ >>
  | Sexpr loc [Slid _ "initializer"; se] →
      let e = expr_se se in
      <:class_str_item< initializer $e$ >>
  | Sexpr loc [Slid _ "method"; Slid _ "virtual"; Slid _ n; se] →
      let t = ctyp_se se in
      <:class_str_item< method virtual $n$ : $t$ >>
  | Sexpr loc [Slid _ "method"; Slid _ "private"; Slid _ n; se] →
      let e = expr_se se in
      <:class_str_item< method private $n$ = $e$ >>
  | Sexpr loc
      [Slid _ "method"; Slid _ "private"; Sexpr _ [Slid _ n :: sel]; se] →
      let e =
        List.fold_right
          (fun se e →
             let p = patt_se se in
             <:expr< fun $p$ -> $e$ >>)
          sel (expr_se se)
      in
      <:class_str_item< method private $n$ = $e$ >>
  | Sexpr loc [Slid _ "method"; Slid _ n; se] →
      let e = expr_se se in
      <:class_str_item< method $n$ = $e$ >>
  | Sexpr loc [Slid _ "method"; Sexpr _ [Slid _ n :: sel]; se] →
      let e =
        List.fold_right
          (fun se e →
             let p = patt_se se in
             <:expr< fun $p$ -> $e$ >>)
          sel (expr_se se)
      in
      <:class_str_item< method $n$ = $e$ >>
  | Sexpr loc [Slid _ "value"; Slid _ "mutable"; Slid _ n; se] →
      let e = expr_se se in
      <:class_str_item< value mutable $n$ = $e$ >>
  | Sexpr loc [Slid _ "value"; Slid _ n; se] →
      let e = expr_se se in
      <:class_str_item< value $n$ = $e$ >>
  | se → error se "class_str_item" ]
and class_type_se =
  fun
  [ Sexpr loc [Slid _ "->"; se :: sel] →
      loop [se :: sel] where rec loop =
        fun
        [ [] → assert False
        | [se] → class_type_se se
        | [se :: sel] →
            let t = ctyp_se se in
            let ct = loop sel in
            <:class_type< [ $t$ ] -> $ct$ >> ]
  | Sexpr loc [Slid _ "object" :: sel] →
      let csl = List.map class_sig_item_se sel in
      <:class_type< object $list:csl$ end >>
  | se → error se "class_type_se" ]
and class_expr_se =
  fun
  [ Sexpr loc [Slid _ "let"; Sexpr _ sel; se] →
      let lbl = anti_list_map let_binding_se sel in
      let ce = class_expr_se se in
      <:class_expr< let $_list:lbl$ in $ce$ >>
  | Sexpr loc [Slid _ "lambda"; se1; se2] →
      let ce = class_expr_se se2 in
      match ipatt_opt_se se1 with
      [ Left p → <:class_expr< fun $p$ -> $ce$ >>
      | Right (se, sel) →
          List.fold_right
            (fun se ce →
               let p = ipatt_se se in
               <:class_expr< fun $p$ -> $ce$ >>)
            [se :: sel] ce ]
  | Sexpr loc [Slid _ "object"; se :: sel] →
      let p =
        match se with
        [ Sexpr _ [] → None
        | se → Some (patt_se se) ]
      in
      let csl = List.map class_str_item_se sel in
      <:class_expr< object $opt:p$ $list:csl$ end >>
  | Sexpr loc [se :: sel] →
      loop (class_expr_se se) sel where rec loop ce =
        fun
        [ [se :: sel] →
            let e = expr_se se in
            loop <:class_expr< $ce$ $e$ >> sel
        | [] → ce ]
  | se →
      let sl = longident_se se in
      let loc = loc_of_sexpr se in
      <:class_expr< $list:sl$ >> ]
;

value directive_se =
  fun
  [ Sexpr _ [Slid _ s] → (s, None)
  | Sexpr _ [Slid _ s; se] →
      let e = expr_se se in
      (s, Some e)
  | se → error se "directive" ]
;

(* Parser *)

Pcaml.syntax_name.val := "Scheme";
Pcaml.no_constructors_arity.val := False;

do {
  Grammar.Unsafe.gram_reinit gram (lexer_gmake ());
  Grammar.Unsafe.clear_entry interf;
  Grammar.Unsafe.clear_entry implem;
  Grammar.Unsafe.clear_entry top_phrase;
  Grammar.Unsafe.clear_entry use_file;
  Grammar.Unsafe.clear_entry expr;
  Grammar.Unsafe.clear_entry patt;
  Grammar.Unsafe.clear_entry ctyp;
  Grammar.Unsafe.clear_entry str_item;
  Grammar.Unsafe.clear_entry sig_item;
  Grammar.Unsafe.clear_entry module_expr;
  Grammar.Unsafe.clear_entry module_type;
  Grammar.Unsafe.clear_entry with_constr;
  Grammar.Unsafe.clear_entry let_binding;
  Grammar.Unsafe.clear_entry type_decl;
  Grammar.Unsafe.clear_entry class_type;
  Grammar.Unsafe.clear_entry class_expr;
  Grammar.Unsafe.clear_entry class_sig_item;
  Grammar.Unsafe.clear_entry class_str_item
};

Pcaml.parse_interf.val := Grammar.Entry.parse interf;
Pcaml.parse_implem.val := Grammar.Entry.parse implem;

value sexpr = Grammar.Entry.create gram "sexpr";

EXTEND
  GLOBAL: implem interf top_phrase use_file expr patt ctyp str_item sig_item
    module_expr module_type with_constr sexpr;
  implem:
    [ [ "#"; se = sexpr ->
          let (n, dp) = directive_se se in
          ([(<:str_item< # $lid:n$ $opt:dp$ >>, loc)], None)
      | si = str_item; x = SELF ->
          let (sil, stopped) = x in
          let loc = MLast.loc_of_str_item si in
          ([(si, loc) :: sil], stopped)
      | EOI -> ([], Some loc) ] ]
  ;
  interf:
    [ [ "#"; se = sexpr ->
          let (n, dp) = directive_se se in
          ([(<:sig_item< # $lid:n$ $opt:dp$ >>, loc)], None)
      | si = sig_item; x = SELF ->
          let (sil, stopped) = x in
          let loc = MLast.loc_of_sig_item si in
          ([(si, loc) :: sil], stopped)
      | EOI -> ([], Some loc) ] ]
  ;
  top_phrase:
    [ [ "#"; se = sexpr ->
          let (n, dp) = directive_se se in
          Some <:str_item< # $lid:n$ $opt:dp$ >>
      | se = sexpr -> Some (str_item_se se)
      | EOI -> None ] ]
  ;
  use_file:
    [ [ "#"; se = sexpr ->
          let (n, dp) = directive_se se in
          ([<:str_item< # $lid:n$ $opt:dp$ >>], True)
      | si = str_item; x = SELF ->
          let (sil, stopped) = x in
          ([si :: sil], stopped)
      | EOI -> ([], False) ] ]
  ;
  expr:
    [ "top"
      [ se = sexpr -> expr_se se ] ]
  ;
  patt:
    [ [ se = sexpr -> patt_se se ] ]
  ;
  ctyp:
    [ [ se = sexpr -> ctyp_se se ] ]
  ;
  str_item:
    [ [ se = sexpr -> str_item_se se
      | e = expr -> <:str_item< $exp:e$ >> ] ]
  ;
  sig_item:
    [ [ se = sexpr -> sig_item_se se ] ]
  ;
  module_expr:
    [ [ se = sexpr -> module_expr_se se ] ]
  ;
  module_type:
    [ [ se = sexpr -> module_type_se se ] ]
  ;
  with_constr:
    [ [ se = sexpr -> with_constr_se se ] ]
  ;
  sexpr:
    [ [ se1 = SELF; DOT; se2 = SELF -> Sacc loc se1 se2 ]
    | [ "("; sl = LIST0 sexpr; ")" -> Sexpr loc sl
      | "["; sl = LIST0 sexpr; "]" -> Slist loc sl
      | "{"; sl = LIST0 sexpr; "}" -> Srec loc sl
      | "#("; sl = V (LIST0 sexpr); ")" -> Sarr loc sl
      | a = pa_extend_keyword -> Slid loc a
      | s = V LIDENT ->
          Pcaml.vala_mapa (fun s → Slid loc s)
            (fun s → Slidv loc <:vala< $s$ >>) s
      | s = V UIDENT ->
          Pcaml.vala_mapa (fun s → Suid loc s)
            (fun s → Suidv loc <:vala< $s$ >>) s
      | s = V INT -> Sint loc s
      | s = V INT_l -> Sint_l loc s
      | s = V INT_L -> Sint_L loc s
      | s = V INT_n -> Sint_n loc s
      | s = V FLOAT -> Sfloat loc s
      | s = V CHAR -> Schar loc s
      | s = V STRING -> Sstring loc s
      | s = SPACEDOT -> Slid loc "."
      | s = QUOT ->
          let i = String.index s ':' in
          let typ = String.sub s 0 i in
          let txt = String.sub s (i + 1) (String.length s - i - 1) in
          Squot loc typ txt
      | s = ANTIQUOT_LOC -> Santi loc "" s
      | s = ANTIQUOT_LOC "_" -> Santi loc "_" s
      | s = ANTIQUOT_LOC "list" -> Santi loc "list" s
      | s = ANTIQUOT_LOC "_list" -> Santi loc "_list" s
      | NL; s = SELF -> s
      | NL -> raise Stream.Failure ] ]
  ;
  pa_extend_keyword:
    [ [ "_" -> "_"
      | "," -> ","
      | "=" -> "="
      | ":" -> ":"
      | "/" -> "/"
      | "#" -> "#" ] ]
  ;
END;
