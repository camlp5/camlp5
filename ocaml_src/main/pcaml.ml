(* camlp5r pa_macro.cmo pa_extend.cmo *)
(* This file has been generated by program: do not edit! *)
(* Copyright (c) INRIA 2007 *)

let version = "5.02";;
let syntax_name = ref "";;

let gram =
  Grammar.gcreate
    {Plexing.tok_func = (fun _ -> failwith "no loaded parsing module");
     Plexing.tok_using = (fun _ -> ()); Plexing.tok_removing = (fun _ -> ());
     Plexing.tok_match =
       (fun _ -> raise (Match_failure ("pcaml.ml", 12, 25)));
     Plexing.tok_text = (fun _ -> ""); Plexing.tok_comm = None}
;;

let interf = Grammar.Entry.create gram "interf";;
let implem = Grammar.Entry.create gram "implem";;
let top_phrase = Grammar.Entry.create gram "top_phrase";;
let use_file = Grammar.Entry.create gram "use_file";;
let sig_item = Grammar.Entry.create gram "sig_item";;
let str_item = Grammar.Entry.create gram "str_item";;
let module_type = Grammar.Entry.create gram "module_type";;
let module_expr = Grammar.Entry.create gram "module_expr";;
let expr = Grammar.Entry.create gram "expr";;
let patt = Grammar.Entry.create gram "patt";;
let ipatt = Grammar.Entry.create gram "ipatt";;
let ctyp = Grammar.Entry.create gram "ctyp";;
let let_binding = Grammar.Entry.create gram "let_binding";;
let type_declaration = Grammar.Entry.create gram "type_declaration";;
let match_case = Grammar.Entry.create gram "match_case";;
let constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration"
;;
let with_constr = Grammar.Entry.create gram "with_constr";;
let poly_variant = Grammar.Entry.create gram "poly_variant";;

let class_sig_item = Grammar.Entry.create gram "class_sig_item";;
let class_str_item = Grammar.Entry.create gram "class_str_item";;
let class_type = Grammar.Entry.create gram "class_type";;
let class_expr = Grammar.Entry.create gram "class_expr";;

let parse_interf = ref (Grammar.Entry.parse interf);;
let parse_implem = ref (Grammar.Entry.parse implem);;

let rec skip_to_eol cs =
  match Stream.peek cs with
    Some '\n' -> ()
  | Some c -> Stream.junk cs; skip_to_eol cs
  | _ -> ()
;;
let sync = ref skip_to_eol;;

let input_file = ref "";;
let output_file = ref None;;

let warning_default_function loc txt =
  let (bp, ep) = Ploc.first_pos loc, Ploc.last_pos loc in
  Printf.eprintf "<W> loc %d %d: %s\n" bp ep txt; flush stderr
;;

let warning = ref warning_default_function;;

List.iter (fun (n, f) -> Quotation.add n f)
  ["id", Quotation.ExStr (fun _ s -> "$0:" ^ s ^ "$");
   "string", Quotation.ExStr (fun _ s -> "\"" ^ String.escaped s ^ "\"")];;

let quotation_dump_file = ref (None : string option);;

type err_ctx =
    Finding
  | Expanding
  | ParsingResult of Ploc.t * string
;;
exception Qerror of string * err_ctx * exn;;

let expand_quotation gloc expander shift name str =
  let new_warning =
    let warn = !warning in
    let shift = Ploc.first_pos gloc + shift in
    fun loc txt -> warn (Ploc.shift shift loc) txt
  in
  Ploc.call_with warning new_warning
    (fun () ->
       try expander str with
         Ploc.Exc (loc, exc) ->
           let exc1 = Qerror (name, Expanding, exc) in
           let shift = Ploc.first_pos gloc + shift in
           let loc =
             let gloc_line_nb = Ploc.line_nb gloc in
             let loc_line_nb = Ploc.line_nb loc in
             if gloc_line_nb < 0 || loc_line_nb < 0 then
               Ploc.make_unlined
                 (shift + Ploc.first_pos loc, shift + Ploc.last_pos loc)
             else
               Ploc.make (gloc_line_nb + loc_line_nb - 1)
                 (if loc_line_nb = 1 then Ploc.bol_pos gloc
                  else shift + Ploc.bol_pos loc)
                 (shift + Ploc.first_pos loc, shift + Ploc.last_pos loc)
           in
           raise (Ploc.Exc (loc, exc1))
       | exc ->
           let exc1 = Qerror (name, Expanding, exc) in Ploc.raise gloc exc1)
    ()
;;

let parse_quotation_result entry loc shift name str =
  let cs = Stream.of_string str in
  try Grammar.Entry.parse entry cs with
    Ploc.Exc (iloc, Qerror (_, Expanding, exc)) ->
      let ctx = ParsingResult (iloc, str) in
      let exc1 = Qerror (name, ctx, exc) in Ploc.raise loc exc1
  | Ploc.Exc (_, (Qerror (_, _, _) as exc)) -> Ploc.raise loc exc
  | Ploc.Exc (iloc, exc) ->
      let ctx = ParsingResult (iloc, str) in
      let exc1 = Qerror (name, ctx, exc) in Ploc.raise loc exc1
;;

let handle_quotation loc proj in_expr entry reloc (name, str) =
  let shift =
    match name with
      "" -> String.length "<<"
    | _ -> String.length "<:" + String.length name + String.length "<"
  in
  let expander =
    try Quotation.find name with
      exc ->
        let exc1 = Qerror (name, Finding, exc) in
        raise (Ploc.Exc (Ploc.sub loc 0 shift, exc1))
  in
  let ast =
    match expander with
      Quotation.ExStr f ->
        let new_str = expand_quotation loc (f in_expr) shift name str in
        parse_quotation_result entry loc shift name new_str
    | Quotation.ExAst fe_fp ->
        expand_quotation loc (proj fe_fp) shift name str
  in
  reloc (fun _ -> loc) shift ast
;;

let expr_eoi = Grammar.Entry.create gram "expr_eoi";;
let patt_eoi = Grammar.Entry.create gram "patt_eoi";;
Grammar.extend
  [Grammar.Entry.obj (expr_eoi : 'expr_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action (fun _ (x : 'expr) (loc : Ploc.t) -> (x : 'expr_eoi))]];
   Grammar.Entry.obj (patt_eoi : 'patt_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action (fun _ (x : 'patt) (loc : Ploc.t) -> (x : 'patt_eoi))]]];;

let handle_expr_quotation loc x =
  handle_quotation loc fst true expr_eoi Reloc.expr x
;;

let handle_patt_quotation loc x =
  handle_quotation loc snd false patt_eoi Reloc.patt x
;;

let expr_reloc = Reloc.expr;;
let patt_reloc = Reloc.patt;;

let rename_id = ref (fun x -> x);;

let find_line loc str =
  let (bp, ep) = Ploc.first_pos loc, Ploc.last_pos loc in
  let rec find i line col =
    if i == String.length str then line, 0, col
    else if i == bp then line, col, col + ep - bp
    else if str.[i] == '\n' then find (succ i) (succ line) 0
    else find (succ i) line (succ col)
  in
  find 0 1 0
;;

let loc_fmt =
  match Sys.os_type with
    "MacOS" ->
      format_of_string "File \"%s\"; line %d; characters %d to %d\n### "
  | _ -> format_of_string "File \"%s\", line %d, characters %d-%d:\n"
;;

let report_quotation_error name ctx =
  let name = if name = "" then !(Quotation.default) else name in
  Format.print_flush ();
  Format.open_hovbox 2;
  Printf.eprintf "While %s \"%s\":"
    (match ctx with
       Finding -> "finding quotation"
     | Expanding -> "expanding quotation"
     | ParsingResult (_, _) -> "parsing result of quotation")
    name;
  match ctx with
    ParsingResult (loc, str) ->
      begin match !quotation_dump_file with
        Some dump_file ->
          Printf.eprintf " dumping result...\n";
          flush stderr;
          begin try
            let (line, c1, c2) = find_line loc str in
            let oc = open_out_bin dump_file in
            output_string oc str;
            output_string oc "\n";
            flush oc;
            close_out oc;
            Printf.eprintf loc_fmt dump_file line c1 c2;
            flush stderr
          with _ ->
            Printf.eprintf "Error while dumping result in file \"%s\""
              dump_file;
            Printf.eprintf "; dump aborted.\n";
            flush stderr
          end
      | None ->
          if !input_file = "" then
            Printf.eprintf
              "\n(consider setting variable Pcaml.quotation_dump_file)\n"
          else Printf.eprintf " (consider using option -QD)\n";
          flush stderr
      end
  | _ -> Printf.eprintf "\n"; flush stderr
;;

let print_format str =
  let rec flush ini cnt =
    if cnt > ini then Format.print_string (String.sub str ini (cnt - ini))
  in
  let rec loop ini cnt =
    if cnt == String.length str then flush ini cnt
    else
      match str.[cnt] with
        '\n' ->
          flush ini cnt;
          Format.close_box ();
          Format.force_newline ();
          Format.open_box 2;
          loop (cnt + 1) (cnt + 1)
      | ' ' -> flush ini cnt; Format.print_space (); loop (cnt + 1) (cnt + 1)
      | _ -> loop ini (cnt + 1)
  in
  Format.open_box 2; loop 0 0; Format.close_box ()
;;

let print_file_failed file line char =
  Format.print_string ", file \"";
  Format.print_string file;
  Format.print_string "\", line ";
  Format.print_int line;
  Format.print_string ", char ";
  Format.print_int char
;;

let print_exn =
  function
    Out_of_memory -> Format.print_string "Out of memory\n"
  | Assert_failure (file, line, char) ->
      Format.print_string "Assertion failed"; print_file_failed file line char
  | Match_failure (file, line, char) ->
      Format.print_string "Pattern matching failed";
      print_file_failed file line char
  | Stream.Error str -> print_format ("Parse error: " ^ str)
  | Stream.Failure -> Format.print_string "Parse failure"
  | Plexing.Error str ->
      Format.print_string "Lexing error: "; Format.print_string str
  | Failure str -> Format.print_string "Failure: "; Format.print_string str
  | Invalid_argument str ->
      Format.print_string "Invalid argument: "; Format.print_string str
  | Sys_error msg ->
      Format.print_string "I/O error: "; Format.print_string msg
  | x ->
      Format.print_string "Uncaught exception: ";
      Format.print_string
        (Obj.magic (Obj.field (Obj.field (Obj.repr x) 0) 0));
      if Obj.size (Obj.repr x) > 1 then
        begin
          Format.print_string " (";
          for i = 1 to Obj.size (Obj.repr x) - 1 do
            if i > 1 then Format.print_string ", ";
            let arg = Obj.field (Obj.repr x) i in
            if not (Obj.is_block arg) then
              Format.print_int (Obj.magic arg : int)
            else if Obj.tag arg = Obj.tag (Obj.repr "a") then
              begin
                Format.print_char '\"';
                Format.print_string (Obj.magic arg : string);
                Format.print_char '\"'
              end
            else Format.print_char '_'
          done;
          Format.print_char ')'
        end
;;

let report_error exn =
  match exn with
    Qerror (name, Finding, Not_found) ->
      let name = if name = "" then !(Quotation.default) else name in
      Format.print_flush ();
      Format.open_hovbox 2;
      Format.printf "Unbound quotation: \"%s\"" name;
      Format.close_box ()
  | Qerror (name, ctx, exn) -> report_quotation_error name ctx; print_exn exn
  | e -> print_exn exn
;;

let no_constructors_arity = Ast2pt.no_constructors_arity;;

let arg_spec_list_ref = ref [];;
let arg_spec_list () = !arg_spec_list_ref;;
let add_option name spec descr =
  arg_spec_list_ref := !arg_spec_list_ref @ [name, spec, descr]
;;

(* Printers *)

let undef x = ref (fun _ -> failwith x);;
let print_interf = undef "no printer";;
let print_implem = undef "no printer";;

let pr_expr = Eprinter.make "expr";;
let pr_patt = Eprinter.make "patt";;
let pr_ctyp = Eprinter.make "type";;
let pr_str_item = Eprinter.make "str_item";;
let pr_sig_item = Eprinter.make "sig_item";;
let pr_module_expr = Eprinter.make "module_expr";;
let pr_module_type = Eprinter.make "module_type";;
let pr_class_sig_item = Eprinter.make "class_sig_item";;
let pr_class_str_item = Eprinter.make "class_str_item";;
let pr_class_expr = Eprinter.make "class_expr";;
let pr_class_type = Eprinter.make "class_type";;
let pr_expr_fun_args = ref Extfun.empty;;

let flag_equilibrate_cases = ref false;;

(* Directives *)

type directive_fun = MLast.expr option -> unit;;
let directives = ref [];;
let add_directive d f = directives := (d, f) :: !directives;;
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
let vala_map f x = f x;;
let vala_mapa f g x = f x;;

add_option "-mode"
  (Arg.String
     (function
        "S" -> strict_mode := true
      | "T" -> strict_mode := false
      | _ -> failwith "bad mode; use option -help for details"))
  "<mode> Set strict (S) or transitional (T) mode.";;

add_option "-pmode"
  (Arg.Unit
     (fun () ->
        if !strict_mode then Printf.eprintf "strict\n"
        else Printf.eprintf "transitional\n";
        flush stderr;
        exit 0))
  "Print the current mode and exit";;
