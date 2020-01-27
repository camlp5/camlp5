(* camlp5r *)
(* testutil.ml,v *)

open Printf;

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

value pa s = let (ast, _) = Pcaml.parse_implem.val (Stream.of_string s) in ast ;
Pcaml.inter_phrases.val := Some " ;\n" ;
value pr l = 
  let sep = match Pcaml.inter_phrases.val with [ None -> "" | Some s -> s ] in
  let b = Buffer.create 23 in do {
    List.iter (fun (ast, _) -> 
      let s = Eprinter.apply Pcaml.pr_str_item Pprintf.empty_pc ast in do {
        Buffer.add_string b s ;
        Buffer.add_string b sep ;
      }) l ;
    Buffer.contents b
  }
;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
