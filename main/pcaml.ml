(* camlp5r pa_extend.cmo *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp5                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: pcaml.ml,v 1.21 2007/09/01 19:42:28 deraugla Exp $ *)

value version = "4.09-exp";
value syntax_name = ref "";

value gram =
  Grammar.gcreate
    {Token.tok_func _ = failwith "no loaded parsing module";
     Token.tok_using _ = (); Token.tok_removing _ = ();
     Token.tok_match = fun []; Token.tok_text _ = ""; Token.tok_comm = None}
;

value interf = Grammar.Entry.create gram "interf";
value implem = Grammar.Entry.create gram "implem";
value top_phrase = Grammar.Entry.create gram "top_phrase";
value use_file = Grammar.Entry.create gram "use_file";
value sig_item = Grammar.Entry.create gram "sig_item";
value str_item = Grammar.Entry.create gram "str_item";
value module_type = Grammar.Entry.create gram "module_type";
value module_expr = Grammar.Entry.create gram "module_expr";
value expr = Grammar.Entry.create gram "expr";
value patt = Grammar.Entry.create gram "patt";
value ctyp = Grammar.Entry.create gram "type";
value let_binding = Grammar.Entry.create gram "let_binding";
value type_declaration = Grammar.Entry.create gram "type_declaration";

value class_sig_item = Grammar.Entry.create gram "class_sig_item";
value class_str_item = Grammar.Entry.create gram "class_str_item";
value class_type = Grammar.Entry.create gram "class_type";
value class_expr = Grammar.Entry.create gram "class_expr";

value parse_interf = ref (Grammar.Entry.parse interf);
value parse_implem = ref (Grammar.Entry.parse implem);

value rec skip_to_eol cs =
  match Stream.peek cs with
  [ Some '\n' -> ()
  | Some c -> do { Stream.junk cs; skip_to_eol cs }
  | _ -> () ]
;
value sync = ref skip_to_eol;

value input_file = ref "";
value output_file = ref None;

value warning_default_function loc txt = do {
  let (bp, ep) = (Ploc.first_pos loc, Ploc.last_pos loc) in
  Printf.eprintf "<W> loc %d %d: %s\n" bp ep txt;
  flush stderr
};

value warning = ref warning_default_function;

value apply_with_var v x f =
  let vx = v.val in
  try do {
    v.val := x;
    let r = f () in
    v.val := vx;
    r
  }
  with e -> do { v.val := vx; raise e }
;

List.iter (fun (n, f) -> Quotation.add n f)
  [("id", Quotation.ExStr (fun _ s -> "$0:" ^ s ^ "$"));
   ("string", Quotation.ExStr (fun _ s -> "\"" ^ String.escaped s ^ "\""))];

value quotation_dump_file = ref (None : option string);

type err_ctx =
  [ Finding
  | Expanding
  | ParsingResult of Ploc.t and string ]
;
exception Qerror of string and err_ctx and exn;

value expand_quotation gloc expander shift name str =
  let new_warning =
    let warn = warning.val in
    let shift = Ploc.first_pos gloc + shift in
    fun loc txt -> warn (Ploc.shift shift loc) txt
  in
  apply_with_var warning new_warning
    (fun () ->
       try expander str with
       [ Ploc.Exc loc exc ->
           let exc1 = Qerror name Expanding exc in
           let shift = Ploc.first_pos gloc + shift in
           let loc =
             Ploc.make (Ploc.line_nb gloc + Ploc.line_nb loc - 1)
               (if Ploc.line_nb loc = 1 then Ploc.bol_pos gloc
                else shift + Ploc.bol_pos loc)
               (shift + Ploc.first_pos loc, shift + Ploc.last_pos loc)
           in
           raise (Ploc.Exc loc exc1)
       | exc ->
           let exc1 = Qerror name Expanding exc in
           Ploc.raise gloc exc1 ])
;

value parse_quotation_result entry loc shift name str =
  let cs = Stream.of_string str in
  try Grammar.Entry.parse entry cs with
  [ Ploc.Exc iloc (Qerror _ Expanding exc) ->
      let ctx = ParsingResult iloc str in
      let exc1 = Qerror name ctx exc in
      Ploc.raise loc exc1
  | Ploc.Exc _ (Qerror _ _ _ as exc) ->
      Ploc.raise loc exc
  | Ploc.Exc iloc exc ->
      let ctx = ParsingResult iloc str in
      let exc1 = Qerror name ctx exc in
      Ploc.raise loc exc1 ]
;

value handle_quotation loc proj in_expr entry reloc (name, str) =
  let shift =
    match name with
    [ "" -> String.length "<<"
    | _ -> String.length "<:" + String.length name + String.length "<" ]
  in
  let expander =
    try Quotation.find name with exc ->
      let exc1 = Qerror name Finding exc in
      raise (Ploc.Exc (Ploc.sub loc 0 shift) exc1)
  in
  let ast =
    match expander with
    [ Quotation.ExStr f ->
        let new_str = expand_quotation loc (f in_expr) shift name str in
        parse_quotation_result entry loc shift name new_str
    | Quotation.ExAst fe_fp ->
        expand_quotation loc (proj fe_fp) shift name str ]
  in
  reloc (fun _ -> loc) shift ast
;

value expr_eoi = Grammar.Entry.create gram "expression";
value patt_eoi = Grammar.Entry.create gram "pattern";
EXTEND
  expr_eoi:
    [ [ x = expr; EOI -> x ] ]
  ;
  patt_eoi:
    [ [ x = patt; EOI -> x ] ]
  ;
END;

value handle_expr_quotation loc x =
  handle_quotation loc fst True expr_eoi Reloc.expr x
;

value handle_patt_quotation loc x =
  handle_quotation loc snd False patt_eoi Reloc.patt x
;

value expr_reloc = Reloc.expr;
value patt_reloc = Reloc.patt;

value rename_id = ref (fun x -> x);

value find_line loc str =
  let (bp, ep) = (Ploc.first_pos loc, Ploc.last_pos loc) in
  find 0 1 0 where rec find i line col =
    if i == String.length str then (line, 0, col)
    else if i == bp then (line, col, col + ep - bp)
    else if str.[i] == '\n' then find (succ i) (succ line) 0
    else find (succ i) line (succ col)
;

value loc_fmt =
  match Sys.os_type with
  [ "MacOS" ->
      format_of_string "File \"%s\"; line %d; characters %d to %d\n### "
  | _ ->
      format_of_string "File \"%s\", line %d, characters %d-%d:\n" ]
;

value report_quotation_error name ctx = do {
  let name = if name = "" then Quotation.default.val else name in
  Format.print_flush ();
  Format.open_hovbox 2;
  Printf.eprintf "While %s \"%s\":"
    (match ctx with
     [ Finding -> "finding quotation"
     | Expanding -> "expanding quotation"
     | ParsingResult _ _ -> "parsing result of quotation" ])
    name;
  match ctx with
  [ ParsingResult loc str ->
      match quotation_dump_file.val with
      [ Some dump_file -> do {
          Printf.eprintf " dumping result...\n";
          flush stderr;
          try do {
            let (line, c1, c2) = find_line loc str in
            let oc = open_out_bin dump_file in
            output_string oc str;
            output_string oc "\n";
            flush oc;
            close_out oc;
            Printf.eprintf loc_fmt dump_file line c1 c2;
            flush stderr
          }
          with _ -> do {
            Printf.eprintf "Error while dumping result in file \"%s\""
              dump_file;
            Printf.eprintf "; dump aborted.\n";
            flush stderr
          }
        }
      | None -> do {
          if input_file.val = "" then
            Printf.eprintf
              "\n(consider setting variable Pcaml.quotation_dump_file)\n"
          else Printf.eprintf " (consider using option -QD)\n";
          flush stderr
        } ]
  | _ -> do { Printf.eprintf "\n"; flush stderr } ]
};

value print_format str = do {
  let rec flush ini cnt =
    if cnt > ini then Format.print_string (String.sub str ini (cnt - ini))
    else ()
  in
  let rec loop ini cnt =
    if cnt == String.length str then flush ini cnt
    else
      match str.[cnt] with
      [ '\n' -> do {
          flush ini cnt;
          Format.close_box ();
          Format.force_newline ();
          Format.open_box 2;
          loop (cnt + 1) (cnt + 1)
        }
      | ' ' -> do {
          flush ini cnt;
          Format.print_space ();
          loop (cnt + 1) (cnt + 1)
        }
      | _ -> loop ini (cnt + 1) ]
  in
  Format.open_box 2;
  loop 0 0;
  Format.close_box ()
};

value print_file_failed file line char = do {
  Format.print_string ", file \"";
  Format.print_string file;
  Format.print_string "\", line ";
  Format.print_int line;
  Format.print_string ", char ";
  Format.print_int char
};

value print_exn =
  fun
  [ Out_of_memory -> Format.print_string "Out of memory\n"
  | Assert_failure (file, line, char) -> do {
      Format.print_string "Assertion failed";
      print_file_failed file line char
    }
  | Match_failure (file, line, char) -> do {
      Format.print_string "Pattern matching failed";
      print_file_failed file line char
    }
  | Stream.Error str -> print_format ("Parse error: " ^ str)
  | Stream.Failure -> Format.print_string "Parse failure"
  | Token.Error str -> do {
      Format.print_string "Lexing error: ";
      Format.print_string str
    }
  | Failure str -> do {
      Format.print_string "Failure: ";
      Format.print_string str
    }
  | Invalid_argument str -> do {
      Format.print_string "Invalid argument: ";
      Format.print_string str
    }
  | Sys_error msg -> do {
      Format.print_string "I/O error: ";
      Format.print_string msg
    }
  | x -> do {
      Format.print_string "Uncaught exception: ";
      Format.print_string
        (Obj.magic (Obj.field (Obj.field (Obj.repr x) 0) 0));
      if Obj.size (Obj.repr x) > 1 then do {
        Format.print_string " (";
        for i = 1 to Obj.size (Obj.repr x) - 1 do {
          if i > 1 then Format.print_string ", " else ();
          let arg = Obj.field (Obj.repr x) i in
          if not (Obj.is_block arg) then
            Format.print_int (Obj.magic arg : int)
          else if Obj.tag arg = Obj.tag (Obj.repr "a") then do {
            Format.print_char '"';
            Format.print_string (Obj.magic arg : string);
            Format.print_char '"'
          }
          else Format.print_char '_';
        };
        Format.print_char ')'
      }
      else ()
    } ]
;

value report_error exn =
  match exn with
  [ Qerror name Finding Not_found -> do {
      let name = if name = "" then Quotation.default.val else name in
      Format.print_flush ();
      Format.open_hovbox 2;
      Format.printf "Unbound quotation: \"%s\"" name;
      Format.close_box ()
    }
  | Qerror name ctx exn -> do {
      report_quotation_error name ctx;
      print_exn exn
    }
  | e -> print_exn exn ]
;

value no_constructors_arity = Ast2pt.no_constructors_arity;

value arg_spec_list_ref = ref [];
value arg_spec_list () = arg_spec_list_ref.val;
value add_option name spec descr =
  arg_spec_list_ref.val := arg_spec_list_ref.val @ [(name, spec, descr)]
;

(* Printers *)

value undef x = ref (fun _ -> failwith x);
value print_interf = undef "no printer";
value print_implem = undef "no printer";

value pr_expr = Eprinter.make "expr";
value pr_patt = Eprinter.make "patt";
value pr_ctyp = Eprinter.make "type";
value pr_str_item = Eprinter.make "str_item";
value pr_sig_item = Eprinter.make "sig_item";
value pr_module_expr = Eprinter.make "module_expr";
value pr_module_type = Eprinter.make "module_type";
value pr_class_sig_item = Eprinter.make "class_sig_item";
value pr_class_str_item = Eprinter.make "class_str_item";
value pr_class_expr = Eprinter.make "class_expr";
value pr_class_type = Eprinter.make "class_type";
value pr_expr_fun_args = ref Extfun.empty;

module OldPrinters =
  struct
    open Spretty;
    type printer_t 'a =
      { pr_fun : mutable string -> 'a -> string -> kont -> pretty;
        pr_levels : mutable list (pr_level 'a) }
    and pr_level 'a =
      { pr_label : string;
        pr_box : 'a -> Stream.t pretty -> pretty;
        pr_rules : mutable pr_rule 'a }
    and pr_rule 'a =
      Extfun.t 'a (curr 'a -> next 'a -> string -> kont -> Stream.t pretty)
    and curr 'a = 'a -> string -> kont -> Stream.t pretty
    and next 'a = 'a -> string -> kont -> pretty
    and kont = Stream.t pretty;
    value pr_str_item = {pr_fun = fun []; pr_levels = []};
    value pr_sig_item = {pr_fun = fun []; pr_levels = []};
    value pr_module_type = {pr_fun = fun []; pr_levels = []};
    value pr_module_expr = {pr_fun = fun []; pr_levels = []};
    value pr_expr = {pr_fun = fun []; pr_levels = []};
    value pr_patt = {pr_fun = fun []; pr_levels = []};
    value pr_ctyp = {pr_fun = fun []; pr_levels = []};
    value pr_class_sig_item = {pr_fun = fun []; pr_levels = []};
    value pr_class_str_item = {pr_fun = fun []; pr_levels = []};
    value pr_class_type = {pr_fun = fun []; pr_levels = []};
    value pr_class_expr = {pr_fun = fun []; pr_levels = []};
    value pr_expr_fun_args = ref Extfun.empty;
    value pr_fun name pr lab =
      loop False pr.pr_levels where rec loop app =
        fun
        [ [] -> fun x dg k -> failwith ("unable to print " ^ name)
        | [lev :: levl] ->
            if app || lev.pr_label = lab then
              let next = loop True levl in
              let rec curr x dg k =
                Extfun.apply lev.pr_rules x curr next dg k
              in
              fun x dg k -> lev.pr_box x (curr x dg k)
            else loop app levl ]
    ;
    pr_str_item.pr_fun := pr_fun "str_item" pr_str_item;
    pr_sig_item.pr_fun := pr_fun "sig_item" pr_sig_item;
    pr_module_type.pr_fun := pr_fun "module_type" pr_module_type;
    pr_module_expr.pr_fun := pr_fun "module_expr" pr_module_expr;
    pr_expr.pr_fun := pr_fun "expr" pr_expr;
    pr_patt.pr_fun := pr_fun "patt" pr_patt;
    pr_ctyp.pr_fun := pr_fun "ctyp" pr_ctyp;
    pr_class_sig_item.pr_fun := pr_fun "class_sig_item" pr_class_sig_item;
    pr_class_str_item.pr_fun := pr_fun "class_str_item" pr_class_str_item;
    pr_class_type.pr_fun := pr_fun "class_type" pr_class_type;
    pr_class_expr.pr_fun := pr_fun "class_expr" pr_class_expr;
    value rec find_pr_level lab =
      fun
      [ [] -> failwith ("level " ^ lab ^ " not found")
      | [lev :: levl] ->
          if lev.pr_label = lab then lev else find_pr_level lab levl ]
    ;
    value top_printer pr x = do {
      Format.force_newline ();
      Spretty.print_pretty Format.print_char Format.print_string
        Format.print_newline "<< " "   " 78 (fun _ _ _ -> ("", 0, 0, 0)) 0
        (pr.pr_fun "top" x "" [: :]);
      Format.print_string " >>"
    };
    value buff = Buffer.create 73;
    value buffer_char = Buffer.add_char buff;
    value buffer_string = Buffer.add_string buff;
    value buffer_newline () = Buffer.add_char buff '\n';
    value string_of pr x = do {
      Buffer.clear buff;
      Spretty.print_pretty buffer_char buffer_string buffer_newline "" "" 78
        (fun _ _ _ -> ("", 0, 0, 0)) 0 (pr.pr_fun "top" x "" [: :]);
      Buffer.contents buff
    };
    value inter_phrases = ref None;
  end
;

(* Directives *)

type directive_fun = option MLast.expr -> unit;
value directives = ref [];
value add_directive d f = directives.val := [(d, f) :: directives.val];
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
