(* camlp5r *)
(* extfun_test.ml *)
#load "pa_extfun.cmo";

open Testutil;

open OUnit2;
open OUnitTest;

type t = { a : int ; b : (string * list int) } ;

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
]
;

value _ = run_test_tt_main tests ;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
