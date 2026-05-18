(* camlp5r *)
(* pcaml.ml,v *)
(* Copyright (c) INRIA 2007-2019 *)

(* #load "pa_macro.cmo" *)
(* #load "pa_extend.cmo" *)

[@@@warnerror "-generative-application-expects-unit"];;

open Printf;;
open Pcamlbase;;

let version = "8.05.01";;
let syntax_name = ref "";;

let ocaml_version =
  let rec loop i =
    if i = String.length Versdep.sys_ocaml_version then
      Versdep.sys_ocaml_version
    else
      match Versdep.sys_ocaml_version.[i] with
        ' ' | '+' | '~' -> String.sub Versdep.sys_ocaml_version 0 i
      | _ -> loop (i + 1)
  in
  loop 0
;;

module Lexer = Plexer.Make (struct  end);;

module ParseBase = Mlsyntax.ParseBase (Lexer);;
include ParseBase.Parsers;;

type 'a ast_transducer_t =
  { name : string;
    parse : (char Stream.t -> 'a) option ref;
    transform : ('a -> 'a) option ref }
;;

let set_ast_parse att pf =
  match !(att.parse) with
    Some _ ->
      failwith
        (Printf.sprintf
           "Pcaml.set_ast_parse: transducer \"%s\" already has a parse(r)"
           att.name)
  | None -> att.parse := Some pf
;;

let set_ast_transform att tf =
  match !(att.transform) with
    Some _ ->
      failwith
        (Printf.sprintf
           "Pcaml.set_ast_transform: transducer \"%s\" already has a tranform(er)"
           att.name)
  | None -> att.transform := Some tf
;;

let transduce att x =
  let parse =
    match !(att.parse) with
      None ->
        failwith
          (Printf.sprintf
             "Pcaml.transduce: transducer \"%s\" has no configured parser"
             att.name)
    | Some x -> x
  in
  let x = parse x in
  match !(att.transform) with
    None -> x
  | Some f -> f x
;;

let transduce_interf =
  {name = "interf"; parse = ref None; transform = ref None}
;;
let transduce_implem =
  {name = "implem"; parse = ref None; transform = ref None}
;;
let transduce_top_phrase =
  {name = "top_phrase"; parse = ref None; transform = ref None}
;;
let transduce_use_file =
  {name = "use_file"; parse = ref None; transform = ref None}
;;

let parse_interf x = transduce transduce_interf x;;
let parse_implem x = transduce transduce_implem x;;
let parse_top_phrase x = transduce transduce_top_phrase x;;
let parse_use_file x = transduce transduce_use_file x;;

let rec skip_to_eol cs =
  match Stream.peek cs with
    Some '\n' -> ()
  | Some c -> Stream.junk cs; skip_to_eol cs
  | _ -> ()
;;
let sync = ref skip_to_eol;;

let output_file = ref None;;

let rename_id = ref (fun x -> x);;

module QuotationHelper = Quotation.QuotationExpansion (ParseBase);;
module QH = QuotationHelper;;

let pp_print_format pps str =
  let flush ini cnt =
    if cnt > ini then
      Format.pp_print_string pps (String.sub str ini (cnt - ini))
  in
  let rec loop ini cnt =
    if cnt == String.length str then flush ini cnt
    else
      match str.[cnt] with
        '\n' ->
          flush ini cnt;
          Format.pp_close_box pps ();
          Format.pp_force_newline pps ();
          Format.pp_open_box pps 2;
          loop (cnt + 1) (cnt + 1)
      | ' ' ->
          flush ini cnt;
          Format.pp_print_space pps ();
          loop (cnt + 1) (cnt + 1)
      | _ -> loop ini (cnt + 1)
  in
  Format.pp_open_box pps 2; loop 0 0; Format.pp_close_box pps ()
;;

let pp_print_file_failed pps file line char =
  Format.pp_print_string pps ", file \"";
  Format.pp_print_string pps file;
  Format.pp_print_string pps "\", line ";
  Format.pp_print_int pps line;
  Format.pp_print_string pps ", char ";
  Format.pp_print_int pps char
;;

let pp_print_exn pps =
  function
    Out_of_memory -> Format.pp_print_string pps "Out of memory\n"
  | Assert_failure (file, line, char) ->
      Format.pp_print_string pps "Assertion failed";
      pp_print_file_failed pps file line char
  | Match_failure (file, line, char) ->
      Format.pp_print_string pps "Pattern matching failed";
      pp_print_file_failed pps file line char
  | Stream.Error str ->
      if str = "" then Format.pp_print_string pps "Parse error"
      else pp_print_format pps ("Parse error: " ^ str)
  | Stream.Failure -> Format.pp_print_string pps "Parse failure"
  | Plexing.Error str ->
      Format.pp_print_string pps "Lexing error";
      if str <> "" then
        begin
          Format.pp_print_string pps ": ";
          Format.pp_print_string pps str
        end
      else Format.pp_print_string pps "."
  | Failure str ->
      Format.pp_print_string pps "Failure: "; Format.pp_print_string pps str
  | Invalid_argument str ->
      Format.pp_print_string pps "Invalid argument: ";
      Format.pp_print_string pps str
  | Sys_error msg ->
      Format.pp_print_string pps "I/O error: "; Format.pp_print_string pps msg
  | x ->
      Format.pp_print_string pps "Uncaught exception: ";
      Format.pp_print_string pps (Printexc.to_string x)
;;

let pp_report_error pps exn =
  match exn with
    Qerror (name, str, Finding, Not_found) ->
      let name = if name = "" then !(Quotation.default) else name in
      Format.pp_print_flush pps ();
      Format.pp_open_hovbox pps 2;
      Format.fprintf pps "Unbound quotation: \"%s\" for string \"%s\"" name
        str;
      Format.pp_close_box pps ()
  | Qerror (name, str, ctx, exn) ->
      QH.pp_report_quotation_error pps name str ctx; pp_print_exn pps exn
  | e -> pp_print_exn pps exn
;;

let report_error exn = pp_report_error Format.std_formatter exn;;

Printexc.register_printer
  (function
     Qerror (_, _, _, _) as exn ->
       let b = Buffer.create 23 in
       let pps = Format.formatter_of_buffer b in
       Format.fprintf pps "%a%!" pp_report_error exn; Some (Buffer.contents b)
   | _ -> None);;

let no_constructors_arity = Prtools.no_constructors_arity;;

let arg_spec_list_ref = ref [];;
let arg_spec_list () = !arg_spec_list_ref;;
let add_option name spec descr =
  arg_spec_list_ref := !arg_spec_list_ref @ [name, spec, descr]
;;
let add_options l = arg_spec_list_ref := !arg_spec_list_ref @ l;;

(* Printers *)

let undef x = ref (fun _ -> failwith x);;
let print_interf = undef "no printer";;
let print_implem = undef "no printer";;

module PrintBase = Mlsyntax.PrintBase (struct  end);;

include PrintBase.Printers;;

let flag_comments_in_phrases = ref true;;
let flag_equilibrate_cases = ref false;;
let flag_expand_letop_syntax = ref false;;

let inter_phrases = ref None;;

(* Directives *)

type directive_fun = MLast.expr option -> unit;;
let directives = ref [];;
let add_directive d f = directives := (d, f) :: !directives;;
let add_directives l = List.iter (fun (d, f) -> add_directive d f) l;;
let find_directive d = List.assoc d !directives;;

(* Equality over syntax trees *)

let eq_expr = Reloc.eq_expr;;
let eq_patt = Reloc.eq_patt;;
let eq_ctyp = Reloc.eq_ctyp;;
let eq_str_item = Reloc.eq_str_item;;
let eq_sig_item = Reloc.eq_sig_item;;
let eq_module_expr = Reloc.eq_module_expr;;
let eq_module_type = Reloc.eq_module_type;;
let eq_class_sig_item = Reloc.eq_class_sig_item;;
let eq_class_str_item = Reloc.eq_class_str_item;;
let eq_class_type = Reloc.eq_class_type;;
let eq_class_expr = Reloc.eq_class_expr;;

(* Mode transitional or strict *)

let strict_mode = ref false;;

let unvala x = x;;
let vala_it f x = ignore (f x);;

let vala_map f x = f x;;
let vala_mapa f g x = f x;;

add_option "-mode"
  (Arg.String
     (function
        "S" -> strict_mode := true
      | "T" -> strict_mode := false
      | _ -> failwith "bad mode; use option -help for details"))
  "<mode> Set strict (S) or transitional (T) mode (bootstrapping only).";;

add_option "-pmode"
  (Arg.Unit
     (fun () ->
        if !strict_mode then eprintf "strict\n" else eprintf "transitional\n";
        flush stderr;
        exit 0))
  "Print the current mode and exit.";;

add_option "-dquot" (Arg.String (fun s -> Quotation.default := s))
  "<name> Set default quotation.";;
