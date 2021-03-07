(* camlp5r *)
(* o_lexer_test.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Pcaml ;

Printf.printf "Syntax: %s\n%!" Pcaml.syntax_name.val ;

EXTEND
  GLOBAL: expr
  ;
  expr: LEVEL "simple"
    [ [ "FOO" →
        <:expr< 1 >>
      ] ]
  ;

END
;

value expr_top s = s |> Stream.of_string |> Grammar.Entry.parse Pcaml.expr ;

value materialize (ts, loct) =
  let rec mrec i =
    let tok = Stream.next ts in
    let loc = Plexing.Locations.lookup loct i in
    if fst tok = "EOI" then [(tok,loc)]
    else [(tok,loc)::(mrec (i+1))]
  in mrec 0
;

value lex_string s =
  let cs = Stream.of_string s in
  let lexer = Grammar.glexer Pcaml.gram in
  let (ts, loct) = lexer.Plexing.tok_func cs in
  materialize (ts,loct)
;

value extract (t,loc) =
  let open Ploc in (t,(first_pos loc, last_pos loc, line_nb loc, bol_pos loc))
;

value pp_position pps (a,b,c,d) = Fmt.(pf pps "(%d,%d,%d,%d)" a b c d) ; 
value pp_positions l = Fmt.(str "%a" (list ~{sep=(const string ";")} pp_position) l) ;

value pp_rv pps ((a,b),pos) = Fmt.(pf pps "((%a,%a),%a)" Dump.string a Dump.string b pp_position pos) ;
value pp_rvs l = Fmt.(str "%a" (list ~{sep=(const string ";")} pp_rv) l) ;


open OUnit2;

value loc = Ploc.dummy ; 
value parse_tests = "parse" >::: [
    "expr-1" >:: (fun [ _ ->
      assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} <:expr< 1 >> (expr_top "1")
    ])
  ; "FOO-1" >:: (fun [ _ ->
      assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} <:expr< 1 >> (expr_top "FOO")
    ])
  ; "string-1" >:: (fun [ _ ->
      assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} <:expr< " foo " >> (expr_top "{a| foo |a}")
    ])
]
;

value lex_tests = "lex" >::: [
  "lex-1" >:: (fun [ _ -> do {
    assert_equal ~{printer=pp_rvs}
      [(("EOI",""),(0,1,1,0))]
      (List.map extract (lex_string ""))
  ; assert_equal ~{printer=pp_rvs}
      [(("STRING","foo"),(0,5,1,0))
      ;(("EOI",""),(5,6,1,0))]
      (List.map extract (lex_string {a|"foo"|a}))
  ; assert_equal ~{printer=pp_rvs}
      [(("STRING","foo"),(0,5,1,0))
      ;(("LIDENT","x"),(6,7,1,0))
      ;(("EOI",""),(7,8,1,0))]
      (List.map extract (lex_string {a|"foo" x|a}))
  ; assert_equal ~{printer=pp_rvs}
      [(("STRING","foo"),(0,7,1,0))
      ;(("LIDENT","x"),(8,9,1,0))
      ;(("EOI",""),(9,10,1,0))]
      (List.map extract (lex_string {a|{|foo|} x|a}))
  ; assert_equal ~{printer=pp_rvs}
      [(("LIDENT","u"),(0,1,1,0))
      ;(("STRING","foo\\nbar"),(4,15,2,2))
      ;(("LIDENT","x"),(17,18,4,16))
      ;(("EOI",""),(18,19,4,16))]
      (List.map extract (lex_string {a|u
  {|foo
bar|}
 x|a}))
  ; assert_equal ~{printer=pp_rvs}
      [(("LIDENT","u"),(0,1,1,0))
      ;(("STRING","foobarbuzz"),(4,26,2,2))
      ;(("LIDENT","x"),(28,29,5,27))
      ;(("EOI",""),(29,30,5,27))]
      (List.map extract (lex_string {a|u
  "foo\
   bar\
   buzz"
 x|a}))
  }
  ])
]
;

value tests = "o_lexer" >::: [
    "parse" >: parse_tests
  ; "lex" >: lex_tests
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main tests
else ()
;
