(* camlp5r *)
(* extfun_test.ml *)
#load "pa_extfun.cmo";

open Testutil;

open OUnit2;
open OUnitTest;

value tests = "test pa_o -> pr_r" >::: [
  "simplest" >:: (fun [ _ ->
  let f = Extfun.empty in
  let f = extfun f with [ 1 -> 1 ] in do {
    assert_bool "just checking that this actually works" (0 <> (Extfun.apply f 1)) ;
    assert_equal 1 (Extfun.apply f 1) ;
    assert_raises Extfun.Failure (fun _ -> Extfun.apply f 2)
  }
  ])
  ;
  "add overlapping" >:: (fun [ _ ->
  let f = ref Extfun.empty in do {
    f.val := extfun f.val with [ 1 -> "one" ] ;
    assert_equal "one" (Extfun.apply f.val 1) ;
    f.val := extfun f.val with [ 1 -> "two" ] ;
    assert_equal "two" (Extfun.apply f.val 1)
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
