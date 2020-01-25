open Testutil

open OUnit2
open OUnitTest
;;

Pcaml.inter_phrases := Some ("\n") ;;

let tests = "test pa_r -> pr_scheme" >::: [
    "simplest" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|(begin 1 2)
3
(define x 1)
|}
          (pr (pa "do { 1; 2 }; 3 ; value x = 1 ;"))
      ) ;
    "simple module" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|(module M (struct (define x 1)))
|}
          (pr (pa "module M = struct value x = 1 ; end ;"))
      ) ;
    "empty module" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|(module M (struct ))
|}
          (pr (pa "module M = struct end ;"))
      ) ;
    "let-module-blank" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|(letmodule _ (struct ) 1)
|}
          (pr (pa "let module _ = struct end in 1 ;"))
      ) ;
    "let-open" >:: (fun _ ->
        assert_equal ~msg:"not equal" ~printer:(fun x -> x)
          {|(letopen M 1)
|}
          (pr (pa "let open M in 1 ;"))
      ) ;
]

let _ = run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
