(* camlp5r *)
(* testutil.ml *)
#load "pa_ounit2.cmo";

open Testutil ;
open Testutil2 ;

open OUnit2 ;
open OUnitTest ;

value tests = "test pa_scheme -> pr_r" >::: [
    "simplest" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun x -> x)}
          {foo|do { 1; 2 } ;
3 ;
value x = 1 ;
|foo}
          (pr (pa {foo|(begin 1 2)  3  (define x 1)|foo}))
                        ]);
    "simple module" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|module M = struct value x = 1; end ;
|foo}
          (pr (pa {foo|(module M (struct (define x 1)))|foo}))
                             ]);
    "empty module" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|module M = struct  end ;
|foo}
          (pr (exn_wrap_result pa {foo|(module M (struct ))|foo}))
                            ]);
    "let-module nonblank" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|let module M = struct  end in 1 ;
|foo}
          (pr (exn_wrap_result pa {foo|(letmodule M (struct ) 1)|foo}))
                                   ]);
    "let-module blank" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|let module _ = struct  end in 1 ;
|foo}
          (pr (exn_wrap_result pa {foo|(letmodule _ (struct ) 1)|foo}))
                                ]);
    "let-open" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|let open M in 1 ;
|foo}
          (pr (exn_wrap_result pa {foo|(letopen M 1)|foo}))
                        ])
]
;

(* Run the tests in test suite *)
value _ =
if invoked_with "sch2r_test.pa_scheme" || invoked_with "sch2r_test.pa_schemer" then
  run_test_tt_main ("all_tests" >::: [
        tests
    ])
else ()
;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
