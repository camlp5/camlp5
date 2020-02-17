(* camlp5r *)
(* testutil.ml,v *)

open Printf;

value list_of_stream_eof eoftok strm =
  let rec lrec acc = parser [
    [: `e when e = eoftok :] -> List.rev [ e::acc ]
  | [: `e ; strm :] -> lrec [ e::acc ] strm
  | [: :] -> List.rev acc
  ] in
  lrec [] strm
;

value lex_string gram s =
  let lexer = Grammar.glexer gram in
  let (strm, _) = lexer.Plexing.tok_func (Stream.of_string s) in
  list_of_stream_eof ("EOI","") strm
;

value lex_string_loc s =
  let lexer = Plexer.gmake() in
  let (strm, locfun) = lexer.Plexing.tok_func (Stream.of_string s) in
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

value print_location loc =
  let loc =
    if Ploc.file_name loc = "" then
      Ploc.make_loc Pcaml.input_file.val 1 0 (0, 1) ""
    else loc
  in
  let fname = Ploc.file_name loc in
  let bp = Ploc.first_pos loc in
  let ep = Ploc.last_pos loc in
  if fname <> "-" then
    let line = Ploc.line_nb loc in
    let bol = Ploc.bol_pos loc in
    eprintf "%s"
      (Pcaml.string_of_loc fname line (bp - bol + 1) (ep - bol + 1))
  else
    eprintf "At location %d-%d\n" bp ep
;

value report_error exc = do {
  Format.set_formatter_out_channel stderr;
  Format.open_vbox 0;
  let exc =
    match exc with
    [ Ploc.Exc loc exc -> do { print_location loc; exc }
    | _ -> exc ]
  in
  Pcaml.report_error exc;
  Format.close_box ();
  Format.print_newline ();
};

value report_error_and_exit exc = do {
  report_error exc ;
  exit 2
};

value wrap_err f arg =
try f arg with exc -> report_error_and_exit exc
;

value pa strm = let (ast, _) = Pcaml.parse_implem.val strm in ast ;
value pa1 s = let ast = pa (Stream.of_string s) in ast ;
value pa_all s =
  let strm = Stream.of_string s in
  let rec pall = parser [
    [: x = pa ; strm :] ->
    if x = [] then [] else
      x @ (pall strm)
  | [: :] -> [] ] in
  pall strm
;

value pr l = do {
  let sep = match Pcaml.inter_phrases.val with [ None -> "" | Some s -> s ] in
  let b = Buffer.create 23 in
    List.iter (fun (ast, _) -> 
      let s = Eprinter.apply Pcaml.pr_str_item Pprintf.empty_pc ast in do {
        Buffer.add_string b s ;
        Buffer.add_string b sep ;
      }) l ;
    Buffer.contents b
}
;
  
value pa_original s =
  let lb = Lexing.from_string s in
  Parse.implementation lb
;
value pr_original st =
  Pprintast.string_of_structure st
;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
