(* camlp5r *)
(* o_top_test.ml *)

open Lexing;
open OUnit2 ;
open OUnitTest ;
open Testutil ;
open Testutil2;
(*
open Camlp5_top_funs;
 *)
Pcaml.inter_phrases.val := Some (";;") ;

value lexbuf_contents lb =
  let open Lexing in
  let pos = lb.lex_curr_pos in
  let len = lb.lex_buffer_len - lb.lex_curr_pos in
  (Bytes.to_string (Bytes.sub lb.lex_buffer pos len))
;

value toplevel_phrase cs =
  Grammar.Entry.parse Pcaml.top_phrase cs
;

value pr_toplevel_phrase phr =
  let t = match phr with
      [ Some phr -> Ast2pt.phrase phr
      | None -> raise End_of_file ] in

  with_buffer_formatter Pprintast.toplevel_phrase t
;

value highlight_locations lb loc1 loc2 =
  let loc1 = (Ploc.first_pos loc1, Ploc.last_pos loc1) in
  try do {
    let pos0 = -lb.lex_abs_pos in
    if pos0 < 0 then raise Exit else ();
    let pos_at_bol = ref 0 in
    print_string "Toplevel input:\n# ";
    for pos = 0 to lb.lex_buffer_len - pos0 - 1 do {
      let c = Bytes.get lb.lex_buffer (pos+pos0) in
      if c = '\n' then do {
        if pos_at_bol.val <= fst loc1 && snd loc1 <= pos then do {
          print_string "\n  ";
          for i = pos_at_bol.val to fst loc1 - 1 do { print_char ' ' };
          for i = fst loc1 to snd loc1 - 1 do { print_char '^' };
          print_char '\n'
        }
        else if pos_at_bol.val <= fst loc1 && fst loc1 < pos then do {
          print_char '\r';
          print_char (if pos_at_bol.val = 0 then '#' else ' ');
          print_char ' ';
          for i = pos_at_bol.val to fst loc1 - 1 do { print_char '.' };
          print_char '\n'
        }
        else if pos_at_bol.val <= snd loc1 && snd loc1 < pos then do {
          for i = pos - 1 downto snd loc1 do { print_string "\008.\008" };
          print_char '\n'
        }
        else print_char '\n';
        pos_at_bol.val := pos + 1;
        if pos < lb.lex_buffer_len - pos0 - 1 then print_string "  " else ()
      }
      else print_char c;
    };
    flush stdout
  }
  with
  [ Exit -> () ]
;

value print_location lb loc =
  if List.mem Toploop.input_name.val [""; "//toplevel//"] then
    highlight_locations lb loc (-1, -1)
  else
    do {
      Format.fprintf Format.err_formatter "%s%!"
        (Pcaml.string_of_loc Toploop.input_name.val (Ploc.line_nb loc)
	   (Ploc.first_pos loc - Ploc.bol_pos loc)
	   (Ploc.last_pos loc - Ploc.bol_pos loc));
    }
;

value wrap f shfn lb =
  let cs =
    let shift = shfn lb in
    Stream.from
      (fun i ->
         if i < shift then Some ' '
         else do {
           while
             lb.lex_curr_pos >= lb.lex_buffer_len &&
             not lb.lex_eof_reached
           do {
             lb.refill_buff lb
           };
           if lb.lex_curr_pos >= lb.lex_buffer_len then None
           else do {
             let c = Bytes.get lb.lex_buffer lb.lex_curr_pos in
             lb.lex_curr_pos := lb.lex_curr_pos + 1;
             Some c
           }
         })
  in
  try f cs with
  [ Ploc.Exc _ (Sys.Break as x) -> raise x
  | End_of_file as x -> raise x
  | x -> do {
      let x =
        match x with
        [ Ploc.Exc loc x -> do { print_location lb loc; x }
        | x -> x ]
      in
      match x with
      [ Stream.Failure | Stream.Error _ -> Pcaml.sync.val cs
      | _ -> () ];
      Format.open_hovbox 0;
      Pcaml.report_error x;
      Format.close_box ();
      Format.print_newline ();
      raise Exit
    } ]
;

value wrapped_entry e lb =
  wrap (Grammar.Entry.parse e) (fun _ -> 0) lb
;


value papr0 (e, pr) s =
  let lb = Lexing.from_string s in
  let rv = wrapped_entry e lb in
  let rvs = pr rv in
  (rvs, lexbuf_contents lb)
;

value papr = papr0 (Pcaml.top_phrase, pr_toplevel_phrase) ;

value pr_str_item si = Eprinter.apply Pcaml.pr_str_item Pprintf.empty_pc si ;

value papr_str_item = papr0 (Pcaml.str_item, pr_str_item) ;

value fmt_pair (x,y) = "<<"^x^"||"^y^">>" ;

value tests = "test o top2" >::: [
    "empty" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ("","") (papr {foo|;;|foo})
    ])
  ; "simplest" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} (";;1"," ") (papr {foo| 1;; |foo})
  ])
  ; "bug-1" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ("let x = M (a b)"," ") (papr {foo| let x = M(a b);; |foo})
  ])
  ; "bug-1b" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} (";;M (a b)"," 1;;") (papr {foo|M(a b);; 1;;|foo})
  ])
  ; "bug-2" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} (";;let open M.N in a b"," ") (papr {foo| M.N.(a b);; |foo})
  ])
  ; "directive-1" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#require  "foo"|foo}," ") (papr {foo| #require "foo";; |foo})
  ])
  ; "show-1" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#show  List|foo}," 1") (papr {foo| #show List;; 1|foo})
  ])
  ; "show-2" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#show  Stdlib.List|foo}," 1") (papr {foo| #show Stdlib.List;; 1|foo})
  ])
  ; "show-3" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#show  Stdlib.List.hd|foo}," 1") (papr {foo| #show Stdlib.List.hd;; 1|foo})
  ])
  ; "show-4" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ({foo|#show  hd|foo}," 1") (papr {foo| #show hd;; 1|foo})
  ])
  ; "bug-3" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} (";;F.f 1"," 1") (papr {foo| (F.f 1);; 1|foo})
  ])
  ; "bug-4" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ("let x::[] = [1]"," ") (papr {foo|let [x] = [1];; |foo})
  ])
  ; "compare-to-bug-4" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ("let x = 1"," ") (papr {foo|let x = 1;; |foo})
  ])
  ; "compare-to-bug-4'" >:: (fun  [ _ ->
      assert_equal ~{printer=fmt_pair} ("let x = 1"," ") (papr_str_item {foo|let x = 1;; |foo})
  ])
  ]
;

(* this needs to remain using invoked_with *)
value _ =
if invoked_with "o_top_test2" then
  run_test_tt_main tests
else ()
;  
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)

