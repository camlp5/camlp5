(* camlp5r *)
(* o_top_test.ml *)
#load "pa_macro.cmo";

open OUnit2 ;
open OUnitTest ;
open Testutil ;
open Testutil2;
open Camlp5_top_funs;

Pcaml.inter_phrases.val := Some (";;") ;

value pr t =
  with_buffer_formatter Pprintast.toplevel_phrase t;

value lexbuf_contents lb =
  let open Lexing in
  let pos = lb.lex_curr_pos in
  let len = lb.lex_buffer_len - lb.lex_curr_pos in
  (Bytes.to_string (Bytes.sub lb.lex_buffer pos len))
;

value papr s =
  let lb = Lexing.from_string s in
  let rv = wrapped_toplevel_phrase lb in
  let rvs = pr rv in
  (rvs, lexbuf_contents lb)
;

value fmt_pair (x,y) = "<<"^x^"||"^y^">>" ;

value tests = "test o top" >::: [
    "simplest" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} (";;1"," ") (papr {foo| 1;; |foo})
    ]) ;
    "bug-1" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ("let x = M (a b)"," ") (papr {foo| let x = M(a b);; |foo})
    ]) ;
    "bug-1b" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} (";;M (a b)"," 1;;") (papr {foo|M(a b);; 1;;|foo})
    ]) ;
    "bug-2" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} (";;let open M.N in a b"," ") (papr {foo| M.N.(a b);; |foo})
    ]) ;
    "directive-1" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#require  "foo"|foo}," ") (papr {foo| #require "foo";; |foo})
    ])
  ]
 ;

value _ =
if invoked_with "o_top_test" then
  run_test_tt_main tests
else ()
;  
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)

