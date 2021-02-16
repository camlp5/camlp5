(* camlp5r *)
(* grammar_bug_test.ml *)

open OUnit2 ;
open OUnitTest ;
open OUnitAssert ;
open MLast ;

value car = List.hd;
value cdr = List.tl;
value rec sep_last = fun [
    [] -> failwith "sep_last"
  | [hd] -> (hd,[])
  | [hd::tl] ->
      let (l,tl) = sep_last tl in (l,[hd::tl])
]
;

value loc = Ploc.dummy ;

value smart_exn_eq e1 e2 =
  let rec eqrec e1 e2 =
  match (e1, e2) with [
    (Ploc.Exc _ e1, Ploc.Exc _ e2) -> eqrec e1 e2
  | (Stream.Error msg1, Stream.Error msg2) -> msg1 = msg2
  | (Failure msg1, Failure msg2) -> msg1 = msg2
  | (Syntaxerr.Error (Other _), Syntaxerr.Error (Other _)) -> True
  | _ -> e1 = e2
  ]
  in eqrec e1 e2
;

value assert_bool ?{printer} msg b =
  if not b then
    let msg0 = match printer with [ None -> "" | Some (f, arg) -> f arg ] in
    assert_failure (msg0^msg)
  else ()
;

value assert_raises_exn_pred ?{msg} ?{exnmsg} exnpred (f: unit -> 'a) =
  let pexn =
    Printexc.to_string
  in
  let get_error_string () =
    let str =
      Format.sprintf
        "expected exception %s, but no exception was raised."
        (match exnmsg with [ None -> "<no message provided>" | Some msg -> msg ])
    in
      match msg with [
          None ->
            assert_failure str

        | Some s ->
            assert_failure (s^"\n"^str) ]
  in
    match raises f with [
       None ->
          assert_failure (get_error_string ())

      | Some e ->
          let msg = match msg with [ None -> "" | Some s -> s ] in
          assert_bool ~{printer=(pexn,e)} msg (exnpred e) ]
;

open Alt_pa_o ;

value has_argle = ref False ;

value tests () = "grammar_bug" >::: [
    "argle1-2" >:: (fun [ _ ->
                          ignore(pa_argle1 ".")
                          ])
    ; "argle1b-2" >:: (fun [ _ ->
                             ignore(pa_argle1b ".")
                          ])
    ; "argle2-1" >:: (fun [ _ ->
        pa_argle2 "a"
                          ])
    ; "argle2-2" >:: (fun [ _ ->
        pa_argle2 "."
                          ])
    ]
 ;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main (tests ())
else ()
;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
