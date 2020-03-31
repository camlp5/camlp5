(* camlp5r *)
(* q_MLast_test.ml *)
#load "pa_macro.cmo";

open Testutil ;
open OUnit2 ;
open OUnitTest ;

Pcaml.inter_phrases.val := Some (";\n") ;

value pa1 = PAPR.Implem.pa1 ;
value pr = PAPR.Implem.pr ;
value fmt_string s = Printf.sprintf "<<%s>>" s ;

value tests = "test pa_r+q_MLast -> pr_r" >::: [
    "expr-simplest" >:: (fun  [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=fmt_string}
          {foo|MLast.ExInt loc (Ploc.VaVal "1") "";
|foo}
          (pr (pa1 {foo| <:expr< 1 >> ; |foo}))
                         ]) ;
    "expr-patt-any" >:: (fun  [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=fmt_string}
          {foo|MLast.PaAny loc;
|foo}
          (pr (pa1 {foo| <:patt< _ >> ; |foo}))
                         ]) ;
    "patt-patt-any" >:: (fun  [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=fmt_string}
          {foo|match x with [ MLast.PaAny _ → 1 ];
|foo}
          (pr (pa1 {foo| match x with [ <:patt< _ >> -> 1 ]; |foo}))
                         ]) 
  ]
 ;

value _ = run_test_tt_main tests ;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
