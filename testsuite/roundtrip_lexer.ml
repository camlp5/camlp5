(* camlp5r *)
(* roundtrip_lexer.ml,v *)

type d_op_t = [
    DOP_le |
    DOP_lt |
    DOP_eq |
    DOP_gt |
    DOP_ge
  ]
;

type d_version_t = string
;

type dexpr = [
    DE_uident of Ploc.t and string
  | DE_version_op of Ploc.t and (Ploc.t * d_op_t) and (Ploc.t * d_version_t)
  | DE_parens of Ploc.t and dexpr and Ploc.t
  | DE_not of Ploc.t and dexpr
  | DE_and of dexpr and Ploc.t and dexpr
  | DE_or of dexpr and Ploc.t and dexpr
  ]
;

value lex_stream1 is =
  let lexer = Plexer.gmake() in
  let (strm, locfun) = lexer.Plexing.tok_func is in
  let rec addloc i =
    parser
      [
        [: `(("EOI",_) as p) :] -> [: `("",p) :]
      | [: `p ; strm :] ->
         let comm = i |> locfun |> Ploc.comment in
         [: `(comm,p) ; addloc (i+1) strm :]
      ] in
  addloc 0 strm
;

value pp_stream1 strm =
  let rec pp1 =
    parser
      [
        [: `(comm,("STRING",tok)) ; strm :] -> do {
          print_string comm ;
          Printf.printf "\"%s\"" tok ;
          pp1 strm
        }
      | [: `(comm,(_,tok)) ; strm :] -> do {
          print_string comm ;
          print_string tok ;
          pp1 strm
        }
      | [: :] -> ()
      ] in
  pp1 strm
;

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
  let cs = Stream.of_channel stdin in do {
    cs |> lex_stream1 |> pp_stream1 ;
    print_newline()
  }
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
