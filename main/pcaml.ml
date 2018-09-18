(* camlp5r *)
(* pcaml.ml,v *)
(* Copyright (c) INRIA 2007-2018 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";

open Printf;

value version = "7.07-exp";
value syntax_name = ref "";

value ocaml_version =
  loop 0 where rec loop i =
    if i = String.length Versdep.sys_ocaml_version then
      Versdep.sys_ocaml_version
    else
      match Versdep.sys_ocaml_version.[i] with
      | ' ' | '+' -> String.sub Versdep.sys_ocaml_version 0 i
      | _ -> loop (i + 1)
      end
;

value gram =
  Grammar.gcreate
    {Plexing.tok_func _ = failwith "no loaded parsing module";
     Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
     Plexing.tok_match = fun []; Plexing.tok_text _ = "";
     Plexing.tok_comm = None}
;

(*
Camlp5 can be parsed with limited or full backtracking:
Grammar.set_algorithm gram Grammar.Functional;
Grammar.set_algorithm gram Grammar.Backtracking;
or without any change in the code, by setting the environment
variable CAMLP5PARAM to f or b.
*)

type status = option Ploc.t;

value interf = Grammar.Entry.create gram "interf";
value implem = Grammar.Entry.create gram "implem";
value top_phrase = Grammar.Entry.create gram "top_phrase";
value use_file = Grammar.Entry.create gram "use_file";
value signature = Grammar.Entry.create gram "signature";
value structure = Grammar.Entry.create gram "structure";
value sig_item = Grammar.Entry.create gram "sig_item";
value str_item = Grammar.Entry.create gram "str_item";
value module_type = Grammar.Entry.create gram "module_type";
value module_expr = Grammar.Entry.create gram "module_expr";
value expr = Grammar.Entry.create gram "expr";
value patt = Grammar.Entry.create gram "patt";
value ipatt = Grammar.Entry.create gram "ipatt";
value ctyp = Grammar.Entry.create gram "ctyp";
value let_binding = Grammar.Entry.create gram "let_binding";
value type_decl = Grammar.Entry.create gram "type_declaration";
value match_case = Grammar.Entry.create gram "match_case";
value constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration";
value label_declaration =
  Grammar.Entry.create gram "label_declaration";
value with_constr = Grammar.Entry.create gram "with_constr";
value poly_variant = Grammar.Entry.create gram "poly_variant";

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

value input_file = Plexing.input_file;
value output_file = ref None;

value warning_default_function loc txt = do {
  let (bp, ep) = (Ploc.first_pos loc, Ploc.last_pos loc) in
  eprintf "<W> loc %d %d: %s\n" bp ep txt;
  flush stderr
};

value warning = ref warning_default_function;
value quotation_loc = ref None;

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

value quotation_location () =
  match quotation_loc.val with
  [ Some loc -> loc
  | None -> failwith "Pcaml.quotation_location: not in quotation context" ]
;

value expand_quotation gloc expander shift name str = do {
  let new_warning =
    let warn = warning.val in
    fun loc txt ->
      let bp = Ploc.first_pos loc in
      let ep = Ploc.last_pos loc in
      let loc = Ploc.sub gloc (shift + bp) (ep - bp) in
      warn loc txt
  in
  let restore =
    let old_warning = warning.val in
    let old_loc = quotation_loc.val in
    fun () -> do {
      warning.val := old_warning;
      quotation_loc.val := old_loc;
    }
  in
  warning.val := new_warning;
  quotation_loc.val := Some (Ploc.shift shift gloc);
  let r =
     try
       try expander str with
       [ Ploc.Exc loc exc ->
           let exc1 = Qerror name Expanding exc in
           let shift = Ploc.first_pos gloc + shift in
           let loc =
             let gloc_line_nb = Ploc.line_nb gloc in
             let loc_line_nb = Ploc.line_nb loc in
             if gloc_line_nb < 0 || loc_line_nb < 0 then
               Ploc.make_unlined
                 (shift + Ploc.first_pos loc, shift + Ploc.last_pos loc)
             else
               Ploc.make_loc (Ploc.file_name loc)
                 (gloc_line_nb + loc_line_nb - 1)
                 (if loc_line_nb = 1 then Ploc.bol_pos gloc
                  else shift + Ploc.bol_pos loc)
                 (shift + Ploc.first_pos loc, shift + Ploc.last_pos loc) ""
           in
           raise (Ploc.Exc loc exc1)
       | exc ->
           let exc1 = Qerror name Expanding exc in
           Ploc.raise gloc exc1 ]
    with
    [ exn -> do { restore (); raise exn } ]
  in
  restore ();
  r;
};

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

value handle_quotation loc proj proj2 in_expr entry reloc (name, str) =
  let (name, locate) =
    let len = String.length name in
    if len = 0 then (name, False)
    else if name.[len-1] = ':' then (String.sub name 0 (len - 1), False)
    else if name.[len-1] = '@' then (String.sub name 0 (len - 1), True)
    else (name, False)
  in
  let shift =
    match name with
    [ "" -> String.length "<<"
    | _ ->
        if locate then
          String.length "<:" + String.length name + String.length ":<"
        else
          String.length "<:" + String.length name + String.length "<" ]
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
        let str = if locate then "@" ^ str else str in
        expand_quotation loc (proj fe_fp) shift name str ]
  in
  let floc =
    let evaluated = ref None in
    fun _ ->
      match evaluated.val with
      [ Some loc -> loc
      | None -> do {
          evaluated.val := Some (Ploc.with_comment loc "");
          loc
        } ]
  in
  reloc floc shift ast
;

value expr_eoi = Grammar.Entry.create gram "expr_eoi";
value patt_eoi = Grammar.Entry.create gram "patt_eoi";
EXTEND
  expr_eoi:
    [ [ x = expr; EOI -> x ] ]
  ;
  patt_eoi:
    [ [ x = patt; EOI -> x ] ]
  ;
END;

value handle_expr_quotation loc x =
  handle_quotation loc fst fst True expr_eoi Reloc.expr x
;

value handle_patt_quotation loc x =
  handle_quotation loc snd snd False patt_eoi Reloc.patt x
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

value string_of_loc fname line bp ep =
  match Sys.os_type with
  [ "MacOS" ->
      sprintf "File \"%s\"; line %d; characters %d to %d\n### " fname line
        bp ep
  | _ ->
      sprintf "File \"%s\", line %d, characters %d-%d:\n" fname line bp ep ]
;

value report_quotation_error name ctx = do {
  let name = if name = "" then Quotation.default.val else name in
  Format.print_flush ();
  Format.open_hovbox 2;
  eprintf "While %s \"%s\":"
    (match ctx with
     [ Finding -> "finding quotation"
     | Expanding -> "expanding quotation"
     | ParsingResult _ _ -> "parsing result of quotation" ])
    name;
  match ctx with
  [ ParsingResult loc str ->
      match quotation_dump_file.val with
      [ Some dump_file -> do {
          eprintf " dumping result...\n";
          flush stderr;
          try do {
            let (line, c1, c2) = find_line loc str in
            let oc = open_out_bin dump_file in
            output_string oc str;
            output_string oc "\n";
            flush oc;
            close_out oc;
            eprintf "%s" (string_of_loc dump_file line c1 c2);
            flush stderr
          }
          with _ -> do {
            eprintf "Error while dumping result in file \"%s\"" dump_file;
            eprintf "; dump aborted.\n";
            flush stderr
          }
        }
      | None -> do {
          if input_file.val = "" then
            eprintf
              "\n(consider setting variable Pcaml.quotation_dump_file)\n"
          else eprintf " (consider using option -QD)\n";
          flush stderr
        } ]
  | _ -> do { eprintf "\n"; flush stderr } ]
};

value print_format str = do {
  let flush ini cnt =
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
  | Stream.Error str ->
      if str = "" then Format.print_string "Parse error"
      else print_format ("Parse error: " ^ str)
  | Stream.Failure -> Format.print_string "Parse failure"
  | Plexing.Error str -> do {
      Format.print_string "Lexing error";
      if str <> "" then do {
        Format.print_string ": ";
        Format.print_string str
      }
      else Format.print_string ".";
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
      Format.print_string (Printexc.to_string x);
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

value no_constructors_arity = Prtools.no_constructors_arity;

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

value flag_comments_in_phrases = ref True;
value flag_equilibrate_cases = ref False;
value flag_compatible_old_versions_of_ocaml = ref False;

value inter_phrases = ref None;

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

(* Greek Ascii equivalence for type parameters *)

value start_with s s_ini =
  let len = String.length s_ini in
  String.length s >= len && String.sub s 0 len = s_ini
;

value greek_tab =
  ["α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ";
   "ο"; "π"; "ρ"; "σ"; "τ"; "υ"; "φ"; "χ"; "ψ"; "ω"]
;
value index_tab = [""; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"];
value greek_ascii_equiv s =
  loop 0 greek_tab where rec loop i =
    fun
    [ [g :: gl] -> do {
        if start_with s g then do {
          let c1 = Char.chr (Char.code 'a' + i) in
          let glen = String.length g in
          let rest = String.sub s glen (String.length s - glen) in
          loop 0 index_tab where rec loop i =
            fun
            [ [k :: kl] -> do {
                if rest = k then do {
                  let s2 = if i = 0 then "" else string_of_int i in
                  String.make 1 c1 ^ s2
                }
                else loop (i + 1) kl
              }
            | [] -> String.make 1 c1 ^ rest ]
        }
        else loop (i + 1) gl
      }
    | [] -> s ]
;

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
