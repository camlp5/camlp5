open Testutil

open OUnit2
open OUnitTest
;;

print_string (pr (pa "do { 1; 2 }; 3 ; value x = 1 ;")) ;;
flush stdout ;;

let tests = "test pa_scheme -> pr_r" >::: [
    "simplest" >:: (fun _ ->
        assert_equal
          {|(begin 1 2) ;
3 ;
(define x 1) ;
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
