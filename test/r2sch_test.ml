open Testutil

open OUnit2
open OUnitTest
;;

Pcaml.inter_phrases := Some ("\n") ;;

let tests = "test pa_r -> pr_scheme" >::: [
    "simplest" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|(begin 1 2)
3
(define x 1)
|}
          (pr (pa "do { 1; 2 }; 3 ; value x = 1 ;"))
      )
]

let _ = run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
