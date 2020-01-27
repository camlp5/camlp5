(* camlp5r *)
(* testutil.ml *)
#load "pa_ounit2.cmo";

open Testutil ;
open OUnit2 ;
open OUnitTest ;

Pcaml.inter_phrases.val := Some ("\n") ;

value tests = "test pa_r -> pr_scheme" >::: [
    "simplest" >:: (fun  [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|(begin 1 2)
3
(define x 1)
|foo}
          (pr (pa "do { 1; 2 }; 3 ; value x = 1 ;"))
                         ]) ;
    "simple module" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [x -> x])}
          {foo|(module M (struct (define x 1)))
|foo}
          (pr (pa "module M = struct value x = 1 ; end ;"))
                             ]) ;
    "empty module" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x])}
          {foo|(module M (struct ))
|foo}
          (pr (pa "module M = struct end ;"))
                            ]) ;
    "let-module-blank" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [x -> x])}
          {foo|(letmodule _ (struct ) 1)
|foo}
          (pr (pa "let module _ = struct end in 1 ;"))
                                ]) ;
    "let-open" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [x -> x])}
          {foo|(letopen M 1)
|foo}
          (pr (pa "let open M in 1 ;"))
                        ])
  ]
 ;

value _ = run_test_tt_main tests ;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
