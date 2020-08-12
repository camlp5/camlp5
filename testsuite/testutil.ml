(* camlp5r *)
(* testutil.ml,v *)

open Printf;

value map_stream f =
  let rec mrec = parser [
    [: `e ; strm :] -> [: `f e ; mrec strm :]
  | [: :] -> [: :]
  ] in mrec
;

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

value lex_string_loc gram s =
  let lexer = Grammar.glexer gram in
  let (strm, loct) = lexer.Plexing.tok_func (Stream.of_string s) in
  let rec tolist acc i =
    match Stream.peek strm with [
      None -> List.rev acc
    | Some (("EOI",_) as p) -> do {
      Stream.junk strm ;
      List.rev [("", p) :: acc]
    }
    | Some p -> do {
        Stream.junk strm ;
        let loc = Plexing.Locations.lookup loct i in
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

value report_error_and_exit ?{exit=True} exc = do {
  report_error exc ;
  if exit then Stdlib.exit 2 else raise exc
};

value wrap_err ?{exit=True} f arg =
try f arg with exc -> report_error_and_exit ~{exit=exit} exc
;

value with_input_file fname f arg =
  let oinput_file = Pcaml.input_file.val in do {
    Pcaml.input_file.val := fname ;
    try let rv = f arg in do { Pcaml.input_file.val := oinput_file ; rv }
    with exc -> do {
      Pcaml.input_file.val := oinput_file ;
      raise exc
    }
  }
;

module PAPR = struct
module Implem = struct
value pa ?{input_file="-"} strm = let (ast, _) = with_input_file input_file Pcaml.parse_implem.val strm in ast ;
value pa1 ?{input_file="-"} s = let ast = pa ~{input_file=input_file} (Stream.of_string s) in ast ;
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
end;

module Interf = struct
value pa ?{input_file="-"} strm = let (ast, _) = with_input_file input_file Pcaml.parse_interf.val strm in ast ;
value pa1 ?{input_file="-"} s = let ast = pa ~{input_file=input_file} (Stream.of_string s) in ast ;
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
      let s = Eprinter.apply Pcaml.pr_sig_item Pprintf.empty_pc ast in do {
        Buffer.add_string b s ;
        Buffer.add_string b sep ;
      }) l ;
    Buffer.contents b
}
;
end;
value both_pa1 = ((fun x -> Implem.pa1 x), (fun x -> Interf.pa1 x)) ;
value both_pr = ((fun x -> Implem.pr x), (fun x -> Interf.pr x)) ;
end;

value with_buffer_formatter f arg = do {
  let b = Buffer.create 23 in
  let bfmt = Format.formatter_of_buffer b in
  f bfmt arg ;
  Format.pp_print_flush bfmt () ;
  Buffer.contents b
}
;

module Official = struct

module Implem = struct
value pa s =
  let lb = Lexing.from_string s in
  Parse.implementation lb
;
value pr st =
  Pprintast.string_of_structure st
;
end ;

module Interf = struct
value pa s =
  let lb = Lexing.from_string s in
  Parse.interface lb
;

value pr st =
  with_buffer_formatter Pprintast.signature st
;
end ;
value both_pa = (Implem.pa, Interf.pa) ;
value both_pr = (Implem.pr, Interf.pr) ;
end ;


open OUnitAssert ;

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

value print_exceptions =
  let open Pcaml in
  fun [
    Ploc.Exc loc exn ->
      let msg = Printf.sprintf "%s: %s" (Ploc.string_of_location loc) (Printexc.to_string exn) in
      Some msg
    | _ -> None
  ]
;
Printexc.register_printer print_exceptions ;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
