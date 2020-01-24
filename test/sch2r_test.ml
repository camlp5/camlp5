open Testutil

open OUnit2
open OUnitTest
;;

let tests = "test pa_scheme -> pr_r" >::: [
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
          (pr (wrap_err pa {|(module M (struct )|}))
      );
]

let _ = run_test_tt_main tests ;;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
