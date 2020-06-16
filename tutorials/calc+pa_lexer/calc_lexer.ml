(* camlp5r *)
(* calc_lexer.ml,v *)

#load "pa_lexer.cmo";

value input_file = ref "" ;

type ctxt = {
  line_nb : ref int ;
  bol_pos : ref int
} ;

value rec number =
  lexer
  [ '0'-'9' number!
  | -> ("INT", $buf)
  ]
;

value nl ctxt c buf = parser bp
  [  [: :] -> do {
      if c = '\n' then ctxt.line_nb.val := 1 + ctxt.line_nb.val else () ;
      ctxt.bol_pos.val := bp;
      buf }
  ]
;

value next_token_must ctxt =
  lexer
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
  lexer
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
