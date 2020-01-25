open Testutil
open Testutil2

open OUnit2
open OUnitTest
;;

let pa_sexpr s = Grammar.Entry.parse Pa_schemer.sexpr (Stream.of_string s);;
let pa_str_item s = Grammar.Entry.parse Pcaml.str_item (Stream.of_string s);;
let pa_implem s = Grammar.Entry.parse Pcaml.implem (Stream.of_string s);;

let tests = "test pa_scheme -> pr_r" >::: [
    "sexpr" >:: (fun _ ->
          let _ = pa_sexpr {|(begin 1 2)  3  (define x 1)|} in ();
      );
    "str_item" >:: (fun _ ->
          let _ = pa_str_item {|(module M (struct (define x 1)))|} in ();
      );
    "implem" >:: (fun _ ->
          let _ = pa_implem {|(module M (struct (define x 1)))|} in ();
      );
    "str_item empty module" >:: (fun _ ->
          let _ = pa_str_item {|(module M (struct ))|} in ();
      );
    "simplest" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|do { 1; 2 } ;
3 ;
value x = 1 ;
|}
          (pr (pa {|(begin 1 2)  3  (define x 1)|}))
      );
    "simple module" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|module M = struct value x = 1; end ;
|}
          (pr (pa {|(module M (struct (define x 1)))|}))
      );
    "empty module" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|module M = struct value x = 1; end ;
|}
          (pr (exn_wrap_result pa {|(module M (struct )|}))
      );

]

(* Run the tests in test suite *)
let _ =
if invoked_with "sch2r_test" then begin
  run_test_tt_main ("all_tests" >::: [
        tests ;
    ])
end
;;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
