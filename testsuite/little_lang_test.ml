(* camlp5r *)
(* pa_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";

open Testutil;
open Testutil2;

type expr = [
    EINT of string
  | EADD of expr and expr
  | ESUB of expr and expr
  | EDIV of expr and expr
  | EMUL of expr and expr
  | EPOW of expr and expr ]
;

value gram = Grammar.gcreate (Plexer.gmake ());

value expression = Grammar.Entry.create gram "expression";

EXTEND
  GLOBAL: expression
  ;
  expression:
    [ "add"
      [ e1 = expression ; "+" ; e2 = expression -> EADD e1 e2
      | e1 = expression ; "-" ; e2 = expression -> ESUB e1 e2
      ]
    | "mul"
      [ e1 = expression ; "*" ; e2 = expression -> EMUL e1 e2
      | e1 = expression ; "/" ; e2 = expression -> EDIV e1 e2
      ]
    | "pow"
      [ e1 = expression ; "**" ; e2 = expression -> EPOW e1 e2
      ]
    | "simple"
      [ i = INT -> EINT i
      | "(" ; e = expression ; ")" -> e
      ] ]
  ;

END
;

value expression_top s = s |> Stream.of_string |> Grammar.Entry.parse expression ;

open OUnit2;

value tests () = "little_lang" >::: [
    "expr-top-simple" >:: (fun [ _ ->
      assert_equal (EINT "1") (expression_top "1")
    ])
    ; "expr-top-pow" >:: (fun [ _ ->
      assert_equal (EPOW (EINT "1") (EINT "2")) (expression_top "1 ** 2")
    ])
    ; "expr-top-mul" >:: (fun [ _ ->
      assert_equal (EMUL (EINT "1") (EINT "2")) (expression_top "1 * 2")
    ])
    ; "expr-top-div" >:: (fun [ _ ->
      assert_equal (EDIV (EINT "1") (EINT "2")) (expression_top "1 / 2")
    ])
    ; "expr-top-sub" >:: (fun [ _ ->
      assert_equal (ESUB (EINT "1") (EINT "2")) (expression_top "1 - 2")
    ])
    ; "expr-top-add" >:: (fun [ _ ->
      assert_equal (EADD (EINT "1") (EINT "2")) (expression_top "1 + 2")
    ])
]
;

value _ = 
if invoked_with "little_lang_test" then
  run_test_tt_main (tests ())
else ()
;
