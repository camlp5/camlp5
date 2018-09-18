(* camlp5r *)
(* pcaml.ml,v *)
(* Copyright (c) INRIA 2007-2018 *)

(* #load "pa_macro.cmo" *)
(* #load "pa_extend.cmo" *)

open Printf;;

let version = "7.07-exp";;
let syntax_name = ref "";;

let ocaml_version =
  let rec loop i =
    if i = String.length Versdep.sys_ocaml_version then
      Versdep.sys_ocaml_version
    else
      match Versdep.sys_ocaml_version.[i] with
        ' ' | '+' -> String.sub Versdep.sys_ocaml_version 0 i
      | _ -> loop (i + 1)
  in
  loop 0
;;

let gram =
  Grammar.gcreate
    {Plexing.tok_func = (fun _ -> failwith "no loaded parsing module");
     Plexing.tok_using = (fun _ -> ()); Plexing.tok_removing = (fun _ -> ());
     Plexing.tok_match =
       (fun _ -> raise (Match_failure ("pcaml.ml", 28, 25)));
     Plexing.tok_text = (fun _ -> ""); Plexing.tok_comm = None}
;;

(*
Camlp5 can be parsed with limited or full backtracking:
Grammar.set_algorithm gram Grammar.Functional;
Grammar.set_algorithm gram Grammar.Backtracking;
or without any change in the code, by setting the environment
variable CAMLP5PARAM to f or b.
*)

type status = Ploc.t option;;

let interf = Grammar.Entry.create gram "interf";;
let implem = Grammar.Entry.create gram "implem";;
let top_phrase = Grammar.Entry.create gram "top_phrase";;
let use_file = Grammar.Entry.create gram "use_file";;
let signature = Grammar.Entry.create gram "signature";;
let structure = Grammar.Entry.create gram "structure";;
let sig_item = Grammar.Entry.create gram "sig_item";;
let str_item = Grammar.Entry.create gram "str_item";;
let module_type = Grammar.Entry.create gram "module_type";;
let module_expr = Grammar.Entry.create gram "module_expr";;
let expr = Grammar.Entry.create gram "expr";;
let patt = Grammar.Entry.create gram "patt";;
let ipatt = Grammar.Entry.create gram "ipatt";;
let ctyp = Grammar.Entry.create gram "ctyp";;
let let_binding = Grammar.Entry.create gram "let_binding";;
let type_decl = Grammar.Entry.create gram "type_declaration";;
let match_case = Grammar.Entry.create gram "match_case";;
let constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration"
;;
let label_declaration = Grammar.Entry.create gram "label_declaration";;
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

let input_file = Plexing.input_file;;
let output_file = ref None;;

let warning_default_function loc txt =
  let (bp, ep) = Ploc.first_pos loc, Ploc.last_pos loc in
  eprintf "<W> loc %d %d: %s\n" bp ep txt; flush stderr
;;

let warning = ref warning_default_function;;
let quotation_loc = ref None;;

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

let quotation_location () =
  match !quotation_loc with
    Some loc -> loc
  | None -> failwith "Pcaml.quotation_location: not in quotation context"
;;

let expand_quotation gloc expander shift name str =
  let new_warning =
    let warn = !warning in
    fun loc txt ->
      let bp = Ploc.first_pos loc in
      let ep = Ploc.last_pos loc in
      let loc = Ploc.sub gloc (shift + bp) (ep - bp) in warn loc txt
  in
  let restore =
    let old_warning = !warning in
    let old_loc = !quotation_loc in
    fun () -> warning := old_warning; quotation_loc := old_loc
  in
  warning := new_warning;
  quotation_loc := Some (Ploc.shift shift gloc);
  let r =
    try
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
              Ploc.make_loc (Ploc.file_name loc)
                (gloc_line_nb + loc_line_nb - 1)
                (if loc_line_nb = 1 then Ploc.bol_pos gloc
                 else shift + Ploc.bol_pos loc)
                (shift + Ploc.first_pos loc, shift + Ploc.last_pos loc) ""
          in
          raise (Ploc.Exc (loc, exc1))
      | exc ->
          let exc1 = Qerror (name, Expanding, exc) in Ploc.raise gloc exc1
    with exn -> restore (); raise exn
  in
  restore (); r
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

let handle_quotation loc proj proj2 in_expr entry reloc (name, str) =
  let (name, locate) =
    let len = String.length name in
    if len = 0 then name, false
    else if name.[len-1] = ':' then String.sub name 0 (len - 1), false
    else if name.[len-1] = '@' then String.sub name 0 (len - 1), true
    else name, false
  in
  let shift =
    match name with
      "" -> String.length "<<"
    | _ ->
        if locate then
          String.length "<:" + String.length name + String.length ":<"
        else String.length "<:" + String.length name + String.length "<"
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
        let str = if locate then "@" ^ str else str in
        expand_quotation loc (proj fe_fp) shift name str
  in
  let floc =
    let evaluated = ref None in
    fun _ ->
      match !evaluated with
        Some loc -> loc
      | None -> evaluated := Some (Ploc.with_comment loc ""); loc
  in
  reloc floc shift ast
;;

let expr_eoi = Grammar.Entry.create gram "expr_eoi";;
let patt_eoi = Grammar.Entry.create gram "patt_eoi";;
Grammar.safe_extend
  [Grammar.extension (expr_eoi : 'expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'expr) (loc : Ploc.t) -> (x : 'expr_eoi)))]];
   Grammar.extension (patt_eoi : 'patt_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'patt) (loc : Ploc.t) -> (x : 'patt_eoi)))]]];;

let handle_expr_quotation loc x =
  handle_quotation loc fst fst true expr_eoi Reloc.expr x
;;

let handle_patt_quotation loc x =
  handle_quotation loc snd snd false patt_eoi Reloc.patt x
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

let string_of_loc fname line bp ep =
  match Sys.os_type with
    "MacOS" ->
      sprintf "File \"%s\"; line %d; characters %d to %d\n### " fname line bp
        ep
  | _ -> sprintf "File \"%s\", line %d, characters %d-%d:\n" fname line bp ep
;;

let report_quotation_error name ctx =
  let name = if name = "" then !(Quotation.default) else name in
  Format.print_flush ();
  Format.open_hovbox 2;
  eprintf "While %s \"%s\":"
    (match ctx with
       Finding -> "finding quotation"
     | Expanding -> "expanding quotation"
     | ParsingResult (_, _) -> "parsing result of quotation")
    name;
  match ctx with
    ParsingResult (loc, str) ->
      begin match !quotation_dump_file with
        Some dump_file ->
          eprintf " dumping result...\n";
          flush stderr;
          begin try
            let (line, c1, c2) = find_line loc str in
            let oc = open_out_bin dump_file in
            output_string oc str;
            output_string oc "\n";
            flush oc;
            close_out oc;
            eprintf "%s" (string_of_loc dump_file line c1 c2);
            flush stderr
          with _ ->
            eprintf "Error while dumping result in file \"%s\"" dump_file;
            eprintf "; dump aborted.\n";
            flush stderr
          end
      | None ->
          if !input_file = "" then
            eprintf
              "\n(consider setting variable Pcaml.quotation_dump_file)\n"
          else eprintf " (consider using option -QD)\n";
          flush stderr
      end
  | _ -> eprintf "\n"; flush stderr
;;

let print_format str =
  let flush ini cnt =
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
  | Stream.Error str ->
      if str = "" then Format.print_string "Parse error"
      else print_format ("Parse error: " ^ str)
  | Stream.Failure -> Format.print_string "Parse failure"
  | Plexing.Error str ->
      Format.print_string "Lexing error";
      if str <> "" then
        begin Format.print_string ": "; Format.print_string str end
      else Format.print_string "."
  | Failure str -> Format.print_string "Failure: "; Format.print_string str
  | Invalid_argument str ->
      Format.print_string "Invalid argument: "; Format.print_string str
  | Sys_error msg ->
      Format.print_string "I/O error: "; Format.print_string msg
  | x ->
      Format.print_string "Uncaught exception: ";
      Format.print_string (Printexc.to_string x)
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

let no_constructors_arity = Prtools.no_constructors_arity;;

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

let flag_comments_in_phrases = ref true;;
let flag_equilibrate_cases = ref false;;
let flag_compatible_old_versions_of_ocaml = ref false;;

let inter_phrases = ref None;;

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

(* Greek Ascii equivalence for type parameters *)

let start_with s s_ini =
  let len = String.length s_ini in
  String.length s >= len && String.sub s 0 len = s_ini
;;

let greek_tab =
  ["α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ"; "ο";
   "π"; "ρ"; "σ"; "τ"; "υ"; "φ"; "χ"; "ψ"; "ω"]
;;
let index_tab = [""; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"];;
let greek_ascii_equiv s =
  let rec loop i =
    function
      g :: gl ->
        if start_with s g then
          let c1 = Char.chr (Char.code 'a' + i) in
          let glen = String.length g in
          let rest = String.sub s glen (String.length s - glen) in
          let rec loop i =
            function
              k :: kl ->
                if rest = k then
                  let s2 = if i = 0 then "" else string_of_int i in
                  String.make 1 c1 ^ s2
                else loop (i + 1) kl
            | [] -> String.make 1 c1 ^ rest
          in
          loop 0 index_tab
        else loop (i + 1) gl
    | [] -> s
  in
  loop 0 greek_tab
;;

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
