(**pp -syntax camlp5r *)
(* camlp5r *)
(* q_MLast_test.ml *)

open Testutil ;
open Testutil2 ;
open OUnit2 ;
open OUnitTest ;

Pcaml.no_constructors_arity.val := False;
Pcaml.inter_phrases.val := Some ";\n" ;
module PAPR = PAPRGen(MLParsers.RP_Q.Base)(MLPrinters.RP.Base.Printers) ;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main (Antiquotation_test.q_MLast_parser_tests ~{pa=PAPR.Implem.pa1} ~{pr=PAPR.Implem.pr})
else ()
;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
