(**pp -syntax camlp5r *)
(* camlp5r *)
(* o2r_test.ml *)

[@@@warnerror "-generative-application-expects-unit";];

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";\n" ;


module PatRP = struct
  module Base = Mlsyntax.PrintBase(struct end) ;
  module R = Print_patr.PP(Base) ;
  module RO = Print_patro.PP(Base)(R) ;
  module RP = Print_patrp.PP(Base)(R) ;
  module Pretty = MLPrinters.PrettyPrint(Base.Printers) ;
end ;

module PAPR = PAPRGen(MLParsers.OP.Base)(PatRP.Base.Printers) ;

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
