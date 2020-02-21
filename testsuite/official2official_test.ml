(* camlp5r *)
(* official2official_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";;\n" ;

value both_pa = (Official.Implem.pa, Official.Interf.pa) ;
value both_pr = (Official.Implem.pr, Official.Interf.pr) ;

value tests = "test pa_o -> pr_official" >::: (Papr_test_matrix.official2official both_pa both_pr ()) ;


value _ =
if invoked_with "official2official_test" then
  run_test_tt_main tests
else ()
;  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
