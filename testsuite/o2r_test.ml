(* camlp5r *)
(* o2r_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";\n" ;

value tests = "matrix" >::: (Papr_test_matrix.o2r PAPR.both_pa1 PAPR.both_pr None ()) ;

value _ =
if not Sys.interactive.val then
  run_test_tt_main tests
else ()
;  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
