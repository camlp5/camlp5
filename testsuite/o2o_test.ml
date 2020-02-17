(* camlp5r *)
(* o2o_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";;\n" ;

value tests = "test pa_o -> pr_o" >::: [
    "simplest" >:: (fun [ _ ->
        assert_equal ~{printer=(fun (x:string) -> x)}
          {foo|let _ = 1; 2;;
let _ = 3;;
let x = 1;;
|foo}
          (pr (pa1 "(1; 2);; 3 ;; let x = 1 ;;"))
                        ]) ;
    "infix1" >:: (fun [ _ ->
        assert_equal ~{printer=(fun (x:string) -> x)}
          {foo|let _ = (a + b) c;;
|foo}
          (pr (pa1 "(a + b) c;;"))
                        ]);
    "infix2" >:: (fun [ _ ->
        assert_equal ~{printer=(fun (x:string) -> x)}
          {foo|let _ = (a --> b) c;;
|foo}
          (pr (pa1 "(a --> b) c;;"))
                        ])
]
;

value _ =
if invoked_with "o2o_test" then
  run_test_tt_main tests
else ()
;  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
