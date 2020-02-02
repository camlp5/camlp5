(* camlp5r *)
(* o2r_test.ml *)

open Testutil;

open OUnit2;
open OUnitTest;

value tests = "test pa_o -> pr_r" >::: [
    "simplest" >:: (fun [ _ ->
        assert_equal
          {foo|do { 1; 2 } ;
3 ;
value x = 1 ;
|foo}
          (pr (pa1 "(1; 2);; 3 ;; let x = 1 ;;"))
                        ])
]
;

value _ = run_test_tt_main tests ;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
