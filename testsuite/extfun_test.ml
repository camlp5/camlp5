(* camlp5r *)
(* extfun_test.ml *)

open Testutil;

open OUnit2;
open OUnitTest;

value pa_expr s =
 s |> Stream.of_string |> Grammar.Entry.parse Pcaml.expr
;

type t = { a : int ; b : (string * list int) } ;

value pr_ctyp ty = Eprinter.apply Pcaml.pr_ctyp Pprintf.empty_pc ty ;

value tests = "extfun" >::: [
  "simplest" >:: (fun [ _ ->
  let f = Extfun.empty in
  let f = extfun f with [ 1 -> 1 ] in do {
    assert_bool "just checking that this actually works" (0 <> (Extfun.apply f 1)) ;
    assert_equal 1 (Extfun.apply f 1) ;
    assert_raises Extfun.Failure (fun _ -> Extfun.apply f 2)
  }
  ])
  ; "add overlapping" >:: (fun [ _ ->
  let f = ref Extfun.empty in do {
    f.val := extfun f.val with [ 1 -> "one" ] ;
    assert_equal "one" (Extfun.apply f.val 1) ;
    f.val := extfun f.val with [ 1 -> "two" ] ;
    assert_equal "two" (Extfun.apply f.val 1)
  }
  ])
  ; "record" >:: (fun [ _ ->
  let f = ref Extfun.empty in do {
    let r1 = { a = 1 ; b =("a",  [1 ; 2]) } in
    let r2 = { a = 2 ; b =("a",  [1 ; 2]) } in
    f.val := extfun f.val with [ { a=1 } -> "one" ] ;
    assert_equal ~{msg="one"} "one" (Extfun.apply f.val r1) ;
    f.val := extfun f.val with [ { b = (_, [1 ; 2 ]) } -> "two" ] ;
    assert_equal ~{msg="two"} "two" (Extfun.apply f.val r2)
  }
  ])
  ; "expr-1" >:: (fun [ _ ->
  let f = ref Extfun.empty in do {
    f.val := extfun f.val with [ <:expr< 1 >> -> "one" ] ;
    let e = pa_expr "1" in
    assert_equal ~{msg="one"} "one" (Extfun.apply f.val e)
  }
  ])
  ; "expr-extension-1" >:: (fun [ _ ->
  let f = ref Extfun.empty in do {
    f.val := extfun f.val with [ <:expr< [%foo:  $type:t$] >> -> pr_ctyp t ] ;
    let e = pa_expr "[%foo: _]" in
    assert_equal ~{msg="should be <<_>>"} "_" (Extfun.apply f.val e)
  }
  ])
  ; "expr-extension-2" >:: (fun [ _ ->
  let f = ref Extfun.empty in do {
    f.val := extfun f.val with [ <:expr< [%foo:  $type:t$] >> -> pr_ctyp t ] ;
    let e = pa_expr "[%foo: result int bool]" in
    assert_equal ~{msg="should be <<result int bool>>"} "result int bool" (Extfun.apply f.val e)
  }
  ])

]
;

value _ = run_test_tt_main tests ;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
