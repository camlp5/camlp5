(* camlp5r *)
(* o2r_test.ml *)

open Testutil;
open Testutil2;

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

value _ =
if invoked_with "o2r_test" then
  run_test_tt_main tests
else ()
;  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
