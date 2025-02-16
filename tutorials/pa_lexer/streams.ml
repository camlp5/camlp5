(* camlp5r *)
(* streams.ml,v *)

open OUnit2;
open OUnitTest;

module LB = Plexing.Lexbuf ;
value lexer1 = lexer [ "[<" | "[:" | "[" ] ;
value lexer2 = lexer [ _ as c1 ] ;

value lexer3 = lexer [ ?= [ 'a' c ] when c = 'b' ] ;

value not_dollar buf =
  parser [: `c when c <> '$' :] -> do { $add c }
;

type t = [ Text of string | Interpolate of string and string ] ;

value rec text = lexer [
  not_dollar text
| ?= ["$$"] "$$" text
| -> Text $buf
]
;

value delim_bar_body delim buf strm =
  let rec ptxt = lexer [
    ?= ['|' c] when c = delim -> ($buf,"")
  | "|"/ (pfmt0 $buf)
  | _ ptxt
  ]
  and pfmt0 txt buf strm = pfmt txt $empty strm
  and pfmt txt = lexer [
    ?= ['|' c] when c = delim -> (txt, $buf)
  | _ (pfmt txt)
  ] in
  let (a,b) = ptxt buf strm in
  Interpolate a b
;

value rec token = lexer [
  not_dollar text
| ?= ["$$"] "$$" text

| "$(|"/ (delim_bar_body ')') "|)"/

]
;

value pa_string pafun s =
  s |> Stream.of_string |> pafun LB.empty |> LB.get ;

value pa_string' pafun s =
  s |> Stream.of_string |> pafun LB.empty ;

value suite = "pa_lexer" >::: [
  "simplest" >:: (fun [ _ -> do {
    assert_equal "[<" (pa_string lexer1 "[<")
  ; assert_equal "[:" (pa_string lexer1 "[:")
  ; assert_equal "[" (pa_string lexer1 "[.")
  ; assert_equal (Text"$$") (pa_string' token "$$")
  ; assert_equal (Text"foo") (pa_string' token "foo")
  ; assert_equal (Interpolate "foo" "") (pa_string' token "$(|foo|)")
  ; assert_equal (Interpolate "foo" "bar") (pa_string' token "$(|foo|bar|)")

  }])
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main suite
else ()
;
