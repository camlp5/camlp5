(* camlp5r *)
(* sch2r_test.ml *)

open Testutil ;
open Testutil2 ;

open OUnit2 ;
open OUnitTest ;

Pcaml.inter_phrases.val := Some ";\n" ;

value pa1 = PAPR.Implem.pa1 ;
value pr = PAPR.Implem.pr ;

value tests = "test pa_scheme -> pr_r" >::: [
    "simplest" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun x -> x)}
          {foo|do { 1; 2 };
3;
value x = 1;
|foo}
          (pr (pa1 {foo|(begin 1 2)  3  (define x 1)|foo}))
                        ]);
    "simple module" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|module M = struct value x = 1; end;
|foo}
          (pr (pa1 {foo|(module M (struct (define x 1)))|foo}))
                             ]);
    "empty module" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|module M = struct  end;
|foo}
          (pr (exn_wrap_result pa1 {foo|(module M (struct ))|foo}))
                            ]);
    "let-module nonblank" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|let module M = struct  end in 1;
|foo}
          (pr (exn_wrap_result pa1 {foo|(letmodule M (struct ) 1)|foo}))
                                   ]);
IFDEF OCAML_VERSION < OCAML_4_10_0 THEN
    "unused" >:: (fun _ -> ())
ELSE
    "let-module blank" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|let module _ = struct  end in 1;
|foo}
          (pr (exn_wrap_result pa1 {foo|(letmodule _ (struct ) 1)|foo}))
                                ])
END
;
    "let-open" >:: (fun [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=(fun [ x -> x ])}
          {foo|let open M in 1;
|foo}
          (pr (exn_wrap_result pa1 {foo|(letopen M 1)|foo}))
                        ])
]
;

(* Run the tests in test suite *)
value _ =
if not Sys.interactive.val then
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
