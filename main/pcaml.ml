(* camlp5r *)
(* pcaml.ml,v *)
(* Copyright (c) INRIA 2007-2019 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";

[@@@warnerror "-generative-application-expects-unit";] ;

open Printf;
open Pcamlbase ;

value version = "8.05.01";
value syntax_name = ref "";

value ocaml_version =
  loop 0 where rec loop i =
    if i = String.length Versdep.sys_ocaml_version then
      Versdep.sys_ocaml_version
    else
      match Versdep.sys_ocaml_version.[i] with
      | ' ' | '+' | '~' -> String.sub Versdep.sys_ocaml_version 0 i
      | _ -> loop (i + 1)
      end
;

module Lexer = Plexer.Make(struct end) ;

module ParseBase = Mlsyntax.ParseBase(Lexer) ;
include ParseBase.Parsers ;

type ast_transducer_t 'a = {
    name : string
  ; parse : ref (option (Stream.t char -> 'a))
  ; transform : ref (option ('a -> 'a))
  } ;

value set_ast_parse att pf =
  match att.parse.val with [
      Some _ -> failwith (Printf.sprintf "Pcaml.set_ast_parse: transducer \"%s\" already has a parse(r)" att.name)
    | None -> att.parse.val := Some pf
    ]
;

value set_ast_transform att tf =
  match att.transform.val with [
      Some _ -> failwith (Printf.sprintf "Pcaml.set_ast_transform: transducer \"%s\" already has a tranform(er)" att.name)
    | None -> att.transform.val := Some tf
    ]
;

value transduce att x =
  let parse = match att.parse.val with [
        None -> failwith (Printf.sprintf "Pcaml.transduce: transducer \"%s\" has no configured parser" att.name)
      | Some x -> x
      ] in
  let x = parse x in
  match att.transform.val with [
      None -> x
    | Some f -> f x
    ]
;

value transduce_interf = { name = "interf" ; parse = ref None ; transform = ref None } ;
value transduce_implem = { name = "implem" ; parse = ref None ; transform = ref None } ;
value transduce_top_phrase = { name = "top_phrase" ; parse = ref None ; transform = ref None } ;
value transduce_use_file = { name = "use_file" ; parse = ref None ; transform = ref None } ;

value parse_interf x = transduce transduce_interf x ;
value parse_implem x = transduce transduce_implem x ;
value parse_top_phrase x = transduce transduce_top_phrase x ;
value parse_use_file x = transduce transduce_use_file x ;

value rec skip_to_eol cs =
  match Stream.peek cs with
  [ Some '\n' -> ()
  | Some c -> do { Stream.junk cs; skip_to_eol cs }
  | _ -> () ]
;
value sync = ref skip_to_eol;

value output_file = ref None;

value rename_id = ref (fun x -> x);

module QuotationHelper = Quotation.QuotationExpansion(ParseBase);
module QH = QuotationHelper ;

value pp_print_format pps str = do {
  let flush ini cnt =
    if cnt > ini then Format.pp_print_string pps (String.sub str ini (cnt - ini))
    else ()
  in
  let rec loop ini cnt =
    if cnt == String.length str then flush ini cnt
    else
      match str.[cnt] with
      [ '\n' -> do {
          flush ini cnt;
          Format.pp_close_box pps ();
          Format.pp_force_newline pps ();
          Format.pp_open_box pps 2;
          loop (cnt + 1) (cnt + 1)
        }
      | ' ' -> do {
          flush ini cnt;
          Format.pp_print_space pps ();
          loop (cnt + 1) (cnt + 1)
        }
      | _ -> loop ini (cnt + 1) ]
  in
  Format.pp_open_box pps 2;
  loop 0 0;
  Format.pp_close_box pps ()
};

value pp_print_file_failed pps file line char = do {
  Format.pp_print_string pps ", file \"";
  Format.pp_print_string pps file;
  Format.pp_print_string pps "\", line ";
  Format.pp_print_int pps line;
  Format.pp_print_string pps ", char ";
  Format.pp_print_int pps char
};

value pp_print_exn pps =
  fun
  [ Out_of_memory -> Format.pp_print_string pps "Out of memory\n"
  | Assert_failure (file, line, char) -> do {
      Format.pp_print_string pps "Assertion failed";
      pp_print_file_failed pps file line char
    }
  | Match_failure (file, line, char) -> do {
      Format.pp_print_string pps "Pattern matching failed";
      pp_print_file_failed pps file line char
    }
  | Stream.Error str ->
      if str = "" then Format.pp_print_string pps "Parse error"
      else pp_print_format pps ("Parse error: " ^ str)
  | Stream.Failure -> Format.pp_print_string pps "Parse failure"
  | Plexing.Error str -> do {
      Format.pp_print_string pps "Lexing error";
      if str <> "" then do {
        Format.pp_print_string pps ": ";
        Format.pp_print_string pps str
      }
      else Format.pp_print_string pps ".";
    }
  | Failure str -> do {
      Format.pp_print_string pps "Failure: ";
      Format.pp_print_string pps str
    }
  | Invalid_argument str -> do {
      Format.pp_print_string pps "Invalid argument: ";
      Format.pp_print_string pps str
    }
  | Sys_error msg -> do {
      Format.pp_print_string pps "I/O error: ";
      Format.pp_print_string pps msg
    }
  | x -> do {
      Format.pp_print_string pps "Uncaught exception: ";
      Format.pp_print_string pps (Printexc.to_string x);
    } ]
;

value pp_report_error pps exn =
  match exn with
  [ Qerror name str Finding Not_found -> do {
      let name = if name = "" then Quotation.default.val else name in
      Format.pp_print_flush pps ();
      Format.pp_open_hovbox pps 2;
      Format.fprintf pps "Unbound quotation: \"%s\" for string \"%s\"" name str;
      Format.pp_close_box pps ()
    }
  | Qerror name str ctx exn -> do {
      QH.pp_report_quotation_error pps name str ctx;
      pp_print_exn pps exn
    }
  | e -> pp_print_exn pps exn ]
;

value report_error exn = pp_report_error Format.std_formatter exn ;

Printexc.register_printer (fun [
    (Qerror _ _ _ _) as exn ->
    let b = Buffer.create 23 in
    let pps = Format.formatter_of_buffer b in do {
      Format.fprintf pps "%a%!" pp_report_error exn ;
      Some (Buffer.contents b)
    }
  | _ -> None
]) ;

value no_constructors_arity = Prtools.no_constructors_arity;

value arg_spec_list_ref = ref [];
value arg_spec_list () = arg_spec_list_ref.val;
value add_option name spec descr =
  arg_spec_list_ref.val := arg_spec_list_ref.val @ [(name, spec, descr)]
;
value add_options l =
  arg_spec_list_ref.val := arg_spec_list_ref.val @ l
;

(* Printers *)

value undef x = ref (fun _ -> failwith x);
value print_interf = undef "no printer";
value print_implem = undef "no printer";

module PrintBase = Mlsyntax.PrintBase(struct end) ;

include PrintBase.Printers ;

value flag_comments_in_phrases = ref True;
value flag_equilibrate_cases = ref False;
value flag_expand_letop_syntax = ref False ;

value inter_phrases = ref None;

(* Directives *)

type directive_fun = option MLast.expr -> unit;
value directives = ref [];
value add_directive d f = directives.val := [(d, f) :: directives.val];
value add_directives l =
  List.iter (fun (d,f) -> add_directive d f) l ;
value find_directive d = List.assoc d directives.val;

(* Equality over syntax trees *)

value eq_expr = Reloc.eq_expr;
value eq_patt = Reloc.eq_patt;
value eq_ctyp = Reloc.eq_ctyp;
value eq_str_item = Reloc.eq_str_item;
value eq_sig_item = Reloc.eq_sig_item;
value eq_module_expr = Reloc.eq_module_expr;
value eq_module_type = Reloc.eq_module_type;
value eq_class_sig_item = Reloc.eq_class_sig_item;
value eq_class_str_item = Reloc.eq_class_str_item;
value eq_class_type = Reloc.eq_class_type;
value eq_class_expr = Reloc.eq_class_expr;

(* Mode transitional or strict *)

value strict_mode = ref (IFNDEF STRICT THEN False ELSE True END);

value unvala x =
  IFNDEF STRICT THEN x
  ELSE
    match x with
    [ Ploc.VaVal x -> x
    | Ploc.VaAnt a -> failwith ("unexpected antiquotation value " ^ a) ]
  END
;
value vala_it f x =
  IFNDEF STRICT THEN ignore(f x)
  ELSE
    match x with
    [ Ploc.VaVal x ->  ignore (f x)
    | Ploc.VaAnt a -> () ]
  END
;

value vala_map f x =
  IFNDEF STRICT THEN f x
  ELSE
    match x with
    [ Ploc.VaVal x -> Ploc.VaVal (f x)
    | Ploc.VaAnt a -> Ploc.VaAnt a ]
  END
;
value vala_mapa f g x =
  IFNDEF STRICT THEN f x
  ELSE
    match x with
    [ Ploc.VaVal x -> f x
    | Ploc.VaAnt y -> g y ]
  END
;

add_option "-mode"
  (Arg.String
     (fun
      [ "S" -> strict_mode.val := True
      | "T" -> strict_mode.val := False
      | _ -> failwith "bad mode; use option -help for details" ]))
  "<mode> Set strict (S) or transitional (T) mode (bootstrapping only).";

add_option "-pmode"
  (Arg.Unit
     (fun () -> do {
        if strict_mode.val then eprintf "strict\n"
        else eprintf "transitional\n";
        flush stderr;
        exit 0
      }))
  "Print the current mode and exit.";

add_option "-dquot" (Arg.String (fun s -> Quotation.default.val := s))
  "<name> Set default quotation.";
