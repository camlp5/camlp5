open Testutil

open OUnit2
open OUnitTest
;;

Pcaml.inter_phrases := None ;;

let tests = "test pa_scheme -> pr_r" >::: [
    "simplest" >:: (fun _ ->
        assert_equal
          {|do { 1; 2 } ;
3 ;
value x = 1 ;
|}
          (pr (pa {|(begin 1 2)  3  (define x 1)|}))
      )
]
(*
let _ = run_test_tt_main tests ;;
*)  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
