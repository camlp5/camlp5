(* camlp5r *)
(* q_MLast_test.ml *)

open Testutil ;
open Testutil2 ;
open OUnit2 ;
open OUnitTest ;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main Antiquotation_test.official_parser_tests
else ()
;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
