(* camlp5r *)
(* official2official_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";;\n" ;

value both_pa = (Official.Implem.pa, Official.Interf.pa) ;
value both_pr = (Official.Implem.pr, Official.Interf.pr) ;

value tests = "matrix" >::: (Papr_test_matrix.official2official both_pa both_pr (Some Testutil.Official.both_pa) ()) ;


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
