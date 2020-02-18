(* camlp5r *)
(* o2official_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";;\n" ;

value pr_official l = do {
  let b = Buffer.create 23 in
  let bfmt = Format.formatter_of_buffer b in
  Pr_official.pp_implem bfmt (l, Ploc.dummy) ;
  Buffer.contents b
}
;

value tests = "test pa_o -> pr_official" >::: (Papr_test_matrix.o2official pa1 pr_official ()) ;


value _ =
if invoked_with "o2official_test" then
  run_test_tt_main tests
else ()
;  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
