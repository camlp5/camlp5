(* camlp5r *)
(* streams.ml,v *)

open OUnit2;
open OUnitTest;

value implode_chars cl =
  let len = List.length cl in
  let dest = Bytes.create len in
  let _ = 
    List.fold_left
      (fun start src -> do { Bytes.set dest start src; start + 1}) 
      0 cl
  in
    Bytes.to_string dest
;

type paren_kind_t = [
  PAREN
| PAREN_BAR
| BRACKET
| BRACKET_BAR
| BRACE
| BRACE_BAR
| ANGLE
| ANGLE_BAR
]
;

type token = [
  Text of string
| Interpolate of paren_kind_t and string and option string
| EOF
]
;

value test1 =
  parser [
      [: `'a' ; `('b' as b) ; `c :] -> (b, c)
    | [: `'a' ; `('c' as b) ; `c :] -> (b, c)
    ]
;

value test2 =
  parser [
      [: ?= ['|' ; ')'] ; `_; `c :] -> c
    | [: ?= ['|' ; '}'] ; `_; `c :] -> c
    | [: `c :] -> c
    ]
;

value delim_bar_body delim strm =
  let rec ptxt acc =
    parser [
        [: ?= ['|' ; c] when c = delim :] -> (implode_chars (List.rev acc), None)
      | [: `'|' ; strm :] -> pfmt (implode_chars (List.rev acc)) [] strm
      | [: `c ; strm :] -> ptxt [c::acc] strm
      ]
  and pfmt txt acc =
    parser [
        [: ?= ['|' ; c] when c = delim :] -> (txt, Some (implode_chars (List.rev acc)))
      | [: `'|' ; strm :] -> pfmt txt ['|'::acc] strm
      | [: `c ; strm :] -> pfmt txt [c::acc] strm
      ]
  in ptxt [] strm
;

value delim_body delim strm =
  let rec ptxt acc =
    parser [
        [: ?= [c] when c = delim :] -> (implode_chars (List.rev acc), None)
      | [: `'|' ; strm :] -> pfmt (implode_chars (List.rev acc)) [] strm
      | [: `c ; strm :] -> ptxt [c::acc] strm
      ]
  and pfmt txt acc =
    parser [
        [: ?= [c] when c = delim :] -> (txt, Some (implode_chars (List.rev acc)))
      | [: `'|' ; strm :] -> pfmt txt ['|'::acc] strm
      | [: `c ; strm :] -> pfmt txt [c::acc] strm
      ]
  in ptxt [] strm
;

value rec token = parser [
  [: `c when c <> '$' ; strm :] -> text [c] strm
| [: ?= ['$'; '$'] ; `'$' ; `'$' ; strm :] -> text ['$'; '$'] strm

| [: `'$' ; `'(' ; `'|' ; (txt,fmt) = delim_bar_body ')' ; `'|' ; `')' :] -> Interpolate PAREN_BAR txt fmt
| [: `'$' ; `'(' ; (txt,fmt) = delim_body ')' ; `')' :] -> Interpolate PAREN txt fmt

| [: `'$' ; `'[' ; `'|' ; (txt,fmt) = delim_bar_body ']' ; `'|' ; `']' :] -> Interpolate BRACKET_BAR txt fmt
| [: `'$' ; `'[' ; (txt,fmt) = delim_body ']' ; `']' :] -> Interpolate BRACKET txt fmt

]
and text acc = parser [
  [: `c when c <> '$' ; strm :] -> text [c::acc] strm
| [: ?= ['$'; '$'] ; `'$' ; `'$' ; strm :] -> text ['$'; '$' :: acc] strm
| [: :] -> Text (implode_chars (List.rev acc))
]
;

value rec tokens = parser [
  [: t = token ; strm :] -> [t :: tokens strm]
| [: :] -> []
]
;

value pa_string pfun s =
  s |> Stream.of_string |> pfun
;

value suite = "streams" >::: [
  "simplest" >:: (fun [ _ -> do {
    assert_equal (Text"a") (pa_string token "a")
  ; assert_equal (Text"$$") (pa_string token "$$")

 ; assert_equal (Interpolate PAREN_BAR "foo" None) (pa_string token "$(|foo|)")
 ; assert_equal (Interpolate PAREN_BAR "foo" (Some "bar")) (pa_string token "$(|foo|bar|)")
 ; assert_equal (Interpolate PAREN_BAR "foo)" None) (pa_string token "$(|foo)|)")
 ; assert_equal (Interpolate PAREN_BAR "foo" (Some "bar|")) (pa_string token "$(|foo|bar||)")
 ; assert_equal (Interpolate PAREN_BAR "foo)" (Some "bar|")) (pa_string token "$(|foo)|bar||)")
 ; assert_equal (Interpolate PAREN "foo" None) (pa_string token "$(foo)")

 ; assert_equal (Interpolate BRACKET_BAR "foo" None) (pa_string token "$[|foo|]")
 ; assert_equal (Interpolate BRACKET_BAR "foo" (Some "bar")) (pa_string token "$[|foo|bar|]")
 ; assert_equal (Interpolate BRACKET_BAR "foo)" None) (pa_string token "$[|foo)|]")
 ; assert_equal (Interpolate BRACKET_BAR "foo" (Some "bar|")) (pa_string token "$[|foo|bar||]")
 ; assert_equal (Interpolate BRACKET_BAR "foo)" (Some "bar|")) (pa_string token "$[|foo)|bar||]")
 ; assert_equal (Interpolate BRACKET "foo" None) (pa_string token "$[foo]")

  }])
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main suite
else ()
;
