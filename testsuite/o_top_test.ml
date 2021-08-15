(* camlp5r *)
(* o_top_test.ml *)

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
    ]) ;
    "show-1" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#show  List|foo}," 1") (papr {foo| #show List;; 1|foo})
    ]) ;
    "show-2" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#show  Stdlib.List|foo}," 1") (papr {foo| #show Stdlib.List;; 1|foo})
    ]) ;
    "show-3" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#show  Stdlib.List.hd|foo}," 1") (papr {foo| #show Stdlib.List.hd;; 1|foo})
    ]) ;
    "show-4" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#show  hd|foo}," 1") (papr {foo| #show hd;; 1|foo})
    ]) ;
    "bug-3" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} (";;F.f 1"," 1") (papr {foo| (F.f 1);; 1|foo})
    ])
  ]
 ;

(* this needs to remain using invoked_with *)
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

