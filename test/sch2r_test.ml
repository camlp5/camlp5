open Testutil
open Testutil2

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
          {|module M = struct  end ;
|}
          (pr (exn_wrap_result pa {|(module M (struct ))|}))
      );
    "let-module nonblank" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|let module M = struct  end in 1 ;
|}
          (pr (exn_wrap_result pa {|(letmodule M (struct ) 1)|}))
      );
    "let-module blank" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|let module _ = struct  end in 1 ;
|}
          (pr (exn_wrap_result pa {|(letmodule _ (struct ) 1)|}))
      );
    "let-open" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|let open M in 1 ;
|}
          (pr (exn_wrap_result pa {|(letopen M 1)|}))
      );
]

(* Run the tests in test suite *)
let _ =
if invoked_with "sch2r_test.pa_scheme" || invoked_with "sch2r_test.pa_schemer" then begin
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
