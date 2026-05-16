(**pp -syntax camlp5r  -package camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf,camlp5.pa_o.link,camlp5.quotations *)
(* camlp5r *)
(* r_lexer_test.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Pcaml ;

EXTEND
  GLOBAL: expr
  ;
  expr: LEVEL "simple"
    [ [ "FOO" →
        <:expr< 1 >>
      | "{|" ; e = expr ; "|}" -> e
      ] ]
  ;

END
;

value expr_top s = s |> Stream.of_string |> Grammar.Entry.parse Pcaml.expr ;

open OUnit2;

value loc = Ploc.dummy ; 
value parse_tests = "parse" >::: [
    "expr-1" >:: (fun [ _ ->
      assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} <:expr< 1 >> (expr_top "1")
    ])
  ; "do-1" >:: (fun [ _ ->
      assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} <:expr< do { 1 ; 2 } >> (expr_top "do { 1 ; 2 }")
    ])
  ; "FOO-1" >:: (fun [ _ ->
      assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} <:expr< 1 >> (expr_top "FOO")
    ])
  ; "string-1" >:: (fun [ _ ->
      assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} <:expr< " foo " >> (expr_top "{a| foo |a}")
    ])
  ; "new-token-1" >:: (fun [ _ ->
      assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} <:expr< foo >> (expr_top "{| foo |}")
    ])
]
;

value tests = "r_lexer" >::: [
    "parse" >: parse_tests
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main tests
else ()
;
