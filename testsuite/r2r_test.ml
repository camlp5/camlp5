(* camlp5r *)
(* r2r_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";\n" ;

value tests = "test pa_r -> pr_r" >::: (Papr_test_matrix.r2r pa1 pr ()) ;

value _ =
if invoked_with "r2r_test" then
  run_test_tt_main tests
else ()
;  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
