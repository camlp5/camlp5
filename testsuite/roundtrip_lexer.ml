(* camlp5r *)
(* roundtrip_lexer.ml,v *)

value lex_stream is =
  let lexer = Plexer.gmake() in
  let (strm, locfun) = lexer.Plexing.tok_func is in
  let rec tolist acc i =
    match Stream.peek strm with [
      None -> List.rev acc
    | Some (("EOI",_) as p) -> do {
      Stream.junk strm ;
      List.rev [("", p) :: acc]
    }
    | Some p -> do {
        Stream.junk strm ;
        let loc = locfun i in
        let comm = Ploc.comment loc in
        tolist [(comm, p) :: acc] (i+1)
      }
   ]
  in
  tolist [] 0
;

value pp_stream l =
List.iter (fun (comm, (_, tok)) -> do {
  print_string comm ;
  print_string tok
}) l ;

value rec sep_last = fun [
    [] -> failwith "sep_last"
  | [ hd ] -> (hd,[])
  | [ hd::tl ] ->
      let (l,tl) = sep_last tl in (l,[ hd::tl ])
  ]
;

value invoked_with ?{flag} cmdna =
  let variant_names = [cmdna; cmdna^".byte"; cmdna^".native"; cmdna^".opt"] in

  let argv = Array.to_list Sys.argv in
  let path = Pcre.split ~{rex=(Pcre.regexp "/")} (List.hd argv) in
  let (fname, _) = sep_last path in

  List.exists ((=) fname) variant_names &&
  match flag with [
    None -> True
  | Some flag ->
    let flag' = "-"^flag in
    let flag'' = "--"^flag in
    List.exists ((=) flag') (List.tl argv) ||
      List.exists ((=) flag'') (List.tl argv) ]
;

value roundtrip_lexer () =
 let cs = Stream.of_channel stdin in
 cs |> lex_stream |> pp_stream
;

(* Run the tests in test suite *)
value _ =
if invoked_with "roundtrip_lexer" then
  roundtrip_lexer ()
else ()
;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
