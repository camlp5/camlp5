(**pp -syntax camlp5r *)
(* camlp5r *)
(* reloc_test.ml *)

open Testutil;

open OUnit2;
open OUnitTest;

open MLParsers.RP.Base.Parsers ;
value pa_expr s =
 s |> Stream.of_string |> Grammar.Entry.parse expr
;

open MLPrinters.R.Pretty ;
value show_expr e = Fmt.(str "%a" pp_expr e) ;

value suite = "reloc" >::: [
  "simplest" >:: (fun [ _ ->
    let a = {foo| [%"nterm"] |foo} |> pa_expr in
    let b = {foo|   [%"nterm"] |foo} |> pa_expr in
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
