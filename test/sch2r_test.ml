open Testutil
open Testutil2

open OUnit2
open OUnitTest
;;

let pa_sexpr s = Grammar.Entry.parse Pa_schemer.sexpr (Stream.of_string s);;

let tests = "test pa_scheme -> pr_r" >::: [
    "sexpr" >:: (fun _ ->
          let _ = pa_sexpr {|(begin 1 2)  3  (define x 1)|} in ();
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

let _ = run_test_tt_main tests ;;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
