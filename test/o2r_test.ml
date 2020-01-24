open Testutil

open OUnit2
open OUnitTest

let tests = "test pa_o -> pr_r" >::: [
    "simplest" >:: (fun _ ->
        assert_equal
          {|do { 1; 2 } ;
3 ;
value x = 1 ;
|}
          (pr (pa "(1; 2);; 3 ;; let x = 1 ;;"))
      )
]

let _ = run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
