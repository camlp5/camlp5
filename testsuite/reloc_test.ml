(* camlp5r *)
(* reloc_test.ml *)

open Testutil;

open OUnit2;
open OUnitTest;

value pa_expr s =
 s |> Stream.of_string |> Grammar.Entry.parse Pcaml.expr
;

value pr_expr ty = Eprinter.apply Pcaml.pr_expr Pprintf.empty_pc ty ;

value suite = "reloc" >::: [
  "simplest" >:: (fun [ _ ->
    let a = {foo| [%"nterm"] |foo} |> Stream.of_string |> Grammar.Entry.parse Pcaml.expr in
    let b = {foo|   [%"nterm"] |foo} |> Stream.of_string |> Grammar.Entry.parse Pcaml.expr in
    assert_equal ~{msg="should be equal"} ~{cmp=Reloc.eq_expr} a b
  ])
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main suite
else ()
;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
