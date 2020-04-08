(* camlp5r *)
(* pa_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";

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

module Pa = struct
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

end ;

module Pr = struct
value pr_expression = Eprinter.make "expression";
value expression = Eprinter.apply pr_expression;

EXTEND_PRINTER
  pr_expression:
    [ "add"
      [ EADD x y -> pprintf pc "%p + %p" curr x curr y
      | ESUB x y -> pprintf pc "%p - %p" curr x curr y ]
    | "mul"
      [ EMUL x y -> pprintf pc "%p * %p" curr x curr y
      | EDIV x y -> pprintf pc "%p / %p" curr x curr y ]
    | "pow"
      [ EPOW x y -> pprintf pc "%p ** %p" curr x curr y ]
    | "simple"
      [ EINT i -> pprintf pc "%s" i ]
    | "bottom"
      [ z -> pprintf pc "(%p)" expression z ]
    ]
  ;
END;

end ;

value roundtrip s = s |> Pa.expression_top |> (Pr.expression Pprintf.empty_pc) ;

open OUnit2;

value parse_tests = "parse" >::: Pa.[
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
    ; "expr-top-add-pow" >:: (fun [ _ ->
      assert_equal (EADD (EINT "1") (EPOW (EINT "2") (EINT "3"))) (expression_top "1 + 2 ** 3")
    ])
    ; "roundtrip-top-add-pow" >:: (fun [ _ ->
      assert_equal (EADD (EINT "1") (EPOW (EINT "2") (EINT "3"))) (expression_top "1 + 2 ** 3")
    ])
]
;

value rt name s = 
  name >:: (fun [ _ ->
    assert_equal ~{printer=fun x -> x} s (roundtrip s)
  ])
;

value roundtrip_tests = "roundtrip" >::: Pa.[
    rt "expr-top-simple" "1"
    ; rt "expr-top-pow" "1 ** 2"
    ; rt "expr-top-mul" "1 * 2"
    ; rt "expr-top-div" "1 / 2"
    ; rt "expr-top-sub" "1 - 2"
    ; rt "expr-top-add" "1 + 2"
    ; rt "expr-top-add-pow" "1 + 2 ** 3"
]
;

value tests = "little_lang" >::: Pa.[
    "parse" >: parse_tests ;
    "roundtrip" >: roundtrip_tests
]
;

value _ = 
if invoked_with "little_lang_test" then
  run_test_tt_main tests
else ()
;
