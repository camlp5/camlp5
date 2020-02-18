(* camlp5r *)
(* o2r_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";\n" ;

value tests = "test pa_o -> pr_r" >::: (Papr_test_matrix.o2r PAPR.both_pa1 PAPR.both_pr ()) ;

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
