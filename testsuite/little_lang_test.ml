(* camlp5r *)
(* pa_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

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
    [ "add" LEFTA [ x = SELF; "+"; y = SELF -> Op "+" x y
      | x = SELF; "-"; y = SELF -> Op "-" x y ]
    | "mul" LEFTA [ x = SELF; "*"; y = SELF -> Op "*" x y
      | x = SELF; "/"; y = SELF -> Op "/" x y ]
    | "pos" RIGHTA [ x = SELF; "**"; y = SELF -> Op "**" x y]
    | "simple" [ x = INT -> Int (int_of_string x)
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

module Eval = struct
  value do_eval = ref (Extfun.empty) ;
  value eval e = Extfun.apply do_eval.val e ;

  value rec pow a = fun [
    0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a) ] ;

  do_eval.val :=
  extfun do_eval.val with [
    Int n -> n
  | Op "+" a b -> (eval a) + (eval b)
  | Op "**" a b -> pow (eval a) (eval b)
  ]
  ;
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
   ; "expr-top-pow-pow" >:: (fun [ _ ->
      assert_equal (Op "**" (Int 2) (Op "**" (Int 2) (Int 2))) (expression_top "2 ** 2 ** 2")
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

value eval_pa s = s |> Pa.expression_top |> Eval.eval ;

value extfun_tests = "extfun" >::: [
  "simplest" >:: (fun [ _ ->
    assert_equal 1 (eval_pa "1")
  ])
  ; "add" >:: (fun [ _ ->
    assert_equal 2 (eval_pa "1+1")
  ])
   ; "add-pow" >:: (fun [ _ ->
    assert_equal 65537 (eval_pa "1+2**2**2**2")
  ])
]
;

value tests = "little_lang" >::: Pa.[
    "parse" >: parse_tests
    ; "roundtrip" >: roundtrip_tests
    ; "extfun" >: extfun_tests
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main tests
else ()
;
