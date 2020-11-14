(* camlp5r *)
(* o2o_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";;\n" ;

value both_official_pa = (Official.Implem.pa, Official.Interf.pa) ;

value tests = "matrix" >::: (Papr_test_matrix.o2o PAPR.both_pa1 PAPR.both_pr (Some both_official_pa) ()) ;

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
