(* camlp5r *)
(* Copyright (c) INRIA 2007-2017 *)

open OUnit2;

value doit kind s =
  let loc = Ploc.make_unlined (0,String.length s) in
  let ((attrloc, attrid),(payloc,pay)) = Quotedext.make_string kind loc s in
  ((Ploc.first_pos attrloc, Ploc.last_pos attrloc, attrid),
   (Ploc.first_pos payloc, Ploc.last_pos payloc, pay))
;

value printer ((a,b,c),(d,e,f)) = Fmt.(str "(%d,%d,%a),(%d,%d,%a)" a b Dump.string c d e Dump.string f) ;

value simple_tests = "lex" >::: [
  "simple" >:: (fun [ _ -> do {
    assert_equal ~{printer=printer} ((3,9,"foo"),(7,9,"abc")) (doit "%%" "{%%foo|abc|}")
  ; assert_equal ~{printer=printer} ((3,7,"foo"),(7,9,"\n")) (doit "%%" "{%%foo|\n|}")
  ; assert_equal ~{printer=printer} ((3,7,"foo"),(7,9,"\"")) (doit "%%" "{%%foo|\"|}")
  }
  ])

]
;

value tests = "quotedext" >::: [
    "simple" >: simple_tests
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main tests
else ()
;
