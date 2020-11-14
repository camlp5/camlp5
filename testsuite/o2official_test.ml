(* camlp5r *)
(* o2official_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";;\n" ;


module Official = struct
module Implem = struct
value pr l =
  Pr_official.(with_buffer_formatter pp_implem (l, Ploc.dummy))
;
end ;
module Interf = struct
value pr l =
  Pr_official.(with_buffer_formatter pp_interf (l, Ploc.dummy))
;
end ;
value both_pr = (Implem.pr, Interf.pr) ;
end ;

value tests = "matrix" >::: (Papr_test_matrix.o2official PAPR.both_pa1 Official.both_pr (Some Testutil.Official.both_pa) ()) ;


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
