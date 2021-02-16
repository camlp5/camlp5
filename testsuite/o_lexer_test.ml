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

value tests = "o_lexer" >::: [
    "parse" >: parse_tests
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main tests
else ()
;
