#load "pa_extend.cmo";
#load "pa_lexer.cmo";

value input_file = ref "" ;

type ctxt = {
  line_nb : ref int ;
  bol_pos : ref int
} ;

value rec number =
  pa_lexer
  [ '0'-'9' number!
  | -> ("INT", $buf)
  ]
;

value next_token_must ctxt =
  pa_lexer
  [ '0'-'9' number!
  | [ '+' | '-' | '*' | '/' | '(' | ')' ] -> ("",$buf)
  ]
;

value start_line ctxt ep = do {
    ctxt.line_nb.val := 1 + ctxt.line_nb.val ;
    ctxt.bol_pos.val := ep
}
;

value rec comment_rest ctxt buf = parser
  [ [: `'\n' :] ep -> do {
      start_line ctxt ep ;
      $add '\n'
    }
  | [: `c ; strm :] -> comment_rest ctxt ($add c) strm
  ]
;

value comment ctxt =
  pa_lexer
  [ "//" (comment_rest ctxt)!
  ]
;

value rec next_token ctxt buf = parser bp
  [ [: ?= [ '/' ; '/' ] ; buf = comment ctxt buf ; strm :] ->
      next_token ctxt buf strm
  | [: `(' '|'\t'|'\r' as c) ; strm :] ->
      next_token ctxt ($add c) strm
  | [: `'\n' ; strm :] ep -> do {
      start_line ctxt ep ;
      next_token ctxt ($add '\n') strm
    }
  | [: tok = next_token_must ctxt $empty :] ep ->
    let comm = $buf in
    let loc = Ploc.make_loc input_file.val ctxt.line_nb.val ctxt.bol_pos.val (bp,ep) comm in
    (tok, loc)
  | [: _ = Stream.empty :] ep ->
    let comm = $buf in
    let loc = Ploc.make_loc input_file.val ctxt.line_nb.val ctxt.bol_pos.val (bp,ep) comm in
    (("EOI",""), loc)
  ]
;

value next_token_fun (cstrm, s_line_nb, s_bol_pos) =
  let ctxt = { line_nb = s_line_nb ; bol_pos = s_bol_pos } in
  next_token ctxt $empty cstrm
;

type binop = [ ADD | SUB | DIV | MUL ] ;
type unop = [ PLUS | MINUS ] ;
type t = [
  BINOP of Ploc.t and binop and t and t
| UNOP of Ploc.t and unop and t
| INT of Ploc.t and int ]
;

value lexer = Plexing.lexer_func_of_parser next_token_fun ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

value g = Grammar.gcreate lexer;
value e = Grammar.Entry.create g "expression";

EXTEND
  e:
    [ [ x = e; "+"; y = e -> BINOP loc ADD x y
      | x = e; "-"; y = e -> BINOP loc SUB x y ]
    | [ x = e; "*"; y = e -> BINOP loc MUL x y
      | x = e; "/"; y = e -> BINOP loc DIV x  y ]
    | [ "-" ; x = e -> UNOP loc MINUS x
      | "+" ; x = e -> UNOP loc PLUS x ]
    | [ x = INT -> INT loc (int_of_string x)
      | "("; x = e; ")" -> x ] ]
  ;
END;

value eval e =
  let rec erec = fun [
    BINOP _ ADD x y -> (erec x)+(erec y)
  | BINOP _ SUB x y -> (erec x)-(erec y)
  | BINOP _ DIV x y -> (erec x)/(erec y)
  | BINOP _ MUL x y -> (erec x)*(erec y)
  | UNOP _ MINUS x -> -(erec x)
  | UNOP _ PLUS x -> erec x
  | INT _ x -> x
  ]
  in erec e
;

open Printf;

try
    let r = Grammar.Entry.parse e (Stream.of_channel stdin) in
    printf "<stdin> = %d\n" (eval r)
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
;
