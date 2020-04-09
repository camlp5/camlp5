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

type expr =
  [ Op of string and expr and expr
  | Int of int
  | Var of string ]
;

module Pa = struct
value gram = Grammar.gcreate (Plexer.gmake ());

value expression = Grammar.Entry.create gram "expression";

EXTEND
  GLOBAL: expression
  ;
  expression:
    [ LEFTA [ x = SELF; "+"; y = SELF -> Op "+" x y
      | x = SELF; "-"; y = SELF -> Op "-" x y ]
    | LEFTA [ x = SELF; "*"; y = SELF -> Op "*" x y
      | x = SELF; "/"; y = SELF -> Op "/" x y ]
    | RIGHTA [ x = SELF; "**"; y = SELF -> Op "**" x y]
    | [ x = INT -> Int (int_of_string x)
      | x = LIDENT -> Var x
      | "("; x = SELF; ")" -> x ] ]
  ;

END
;

value expression_top s = s |> Stream.of_string |> Grammar.Entry.parse expression ;

end ;

module Pr = struct
value pr_expression = Eprinter.make "expression";
value expression = Eprinter.apply pr_expression;
value expression_pow = Eprinter.apply_level pr_expression "pow";
value expression_simple = Eprinter.apply_level pr_expression "simple";

value pr_bad = Eprinter.make "bad";
value bad = Eprinter.apply pr_bad;


EXTEND_PRINTER
  pr_expression:
    [ "add"
      [ Op "+" x y -> pprintf pc "%p + %p" curr x curr y
      | Op "-" x y -> pprintf pc "%p - %p" curr x curr y ]
    | "mul"
      [ Op "*" x y -> pprintf pc "%p * %p" curr x curr y
      | Op "/" x y -> pprintf pc "%p / %p" curr x curr y ]
    | "pow"
      [ Op "**"  x y -> pprintf pc "%p ** %p" curr x curr y ]
    | "simple"
      [ Int i -> pprintf pc "%d" i
      | Var x -> pprintf pc "%s" x
      ]
    | "bottom"
      [ z ->
        let fail() = 
          failwith (Printf.sprintf "[internal error] pr_expression %d" (Obj.tag (Obj.repr z))) in
        pprintf pc "(%p)" (bottom ~{fail=fail}) z ]
    ]
  ;
  pr_bad:
    [ "simple"
      [ Int i -> pprintf pc "%d" i ]
    | "bottom"
      [ z ->
        let fail() = 
          failwith (Printf.sprintf "pr_bad %d" (Obj.tag (Obj.repr z))) in
        pprintf pc "(%p)" (bottom ~{fail=fail}) z ]
    ]
  ;
END;

end ;

value roundtrip s = s |> Pa.expression_top |> (Pr.expression Pprintf.empty_pc) ;
value bad_roundtrip s = s |> Pa.expression_top |> (Pr.bad Pprintf.empty_pc) ;

open OUnit2;

value parse_tests = "parse" >::: Pa.[
    "expr-top-simple" >:: (fun [ _ ->
      assert_equal (Int 1) (expression_top "1")
    ])
    ; "expr-top-pow" >:: (fun [ _ ->
      assert_equal (Op "**" (Int 1) (Int 2)) (expression_top "1 ** 2")
    ])
    ; "expr-top-mul" >:: (fun [ _ ->
      assert_equal (Op "*" (Int 1) (Int 2)) (expression_top "1 * 2")
    ])
    ; "expr-top-div" >:: (fun [ _ ->
      assert_equal (Op "/" (Int 1) (Int 2)) (expression_top "1 / 2")
    ])
    ; "expr-top-sub" >:: (fun [ _ ->
      assert_equal (Op "-" (Int 1) (Int 2)) (expression_top "1 - 2")
    ])
    ; "expr-top-add" >:: (fun [ _ ->
      assert_equal (Op "+" (Int 1) (Int 2)) (expression_top "1 + 2")
    ])
    ; "expr-top-add-pow" >:: (fun [ _ ->
      assert_equal (Op "+" (Int 1) (Op "**" (Int 2) (Int 3))) (expression_top "1 + 2 ** 3")
    ])
    ; "expr-top-add-pow-1" >:: (fun [ _ ->
      assert_equal (Op "+" (Int 1) (Op "**" (Int 2) (Int 3))) (expression_top "1 + 2 ** 3")
    ])
    ; "expr-top-add-pow-2" >:: (fun [ _ ->
      assert_equal (Op "**" (Op "+" (Int 1) (Int 2)) (Int 3)) (expression_top "(1 + 2) ** 3")
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
    ; rt "expr-top-add-pow-1" "1 + 2 ** 3"
    ; rt "expr-top-add-pow-2" "(1 + 2) ** 3"
    ; "bad-simple" >:: (fun [ _ ->
      assert_equal "1" (bad_roundtrip "1")
    ])
    ; "bad-add" >:: (fun [ _ ->
      assert_raises (Failure("pr_bad 0"))
      (fun () -> bad_roundtrip "1+2")
    ])
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
