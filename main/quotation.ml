(* camlp5r *)
(* quotation.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";

open Printf ;
open Pcamlbase ;

type expander =
  [ ExStr of bool -> string -> string
  | ExAst of (string -> MLast.expr * string -> MLast.patt) ]
;

value expanders_table = ref [];

value default = ref "";
value translate = ref (fun x -> x);

value expander_name name =
  match translate.val name with
  [ "" -> default.val
  | name -> name ]
;

value find name = List.assoc (expander_name name) expanders_table.val;

value add name f =
  if List.mem_assoc name expanders_table.val then do {
    Printf.fprintf stderr "Failure: Quotation.add: cannot add the quotation \"%s\" twice\n%!" name ;
    Ploc.raise Ploc.dummy (Failure Printf.(sprintf"Quotation.add: cannot add the quotation \"%s\" twice" name))
  }
  else
    expanders_table.val := [(name, f) :: expanders_table.val]
;

value upsert name f = do {
  if List.mem_assoc name expanders_table.val then
    Printf.fprintf stderr "Warning: Quotation.upsert: overwriting the quotation \"%s\"\n%!" name
  else () ;
  expanders_table.val := [(name, f) :: expanders_table.val]
}
;
module type QUOTATION_EXPANSION = sig
  value quotation_dump_file : ref (option string);
  (** [quotation_dump_file] optionally tells the compiler to dump the
      result of an expander (of kind "generating a string") if this
      result is syntactically incorrect.
      If [None] (default), this result is not dumped. If [Some fname], the
      result is dumped in the file [fname]. *)
  value quotation_location : unit -> Ploc.t;
  (** while expanding a quotation, returns the location of the quotation
      text (between the quotation quotes) in the source; raises
      [Failure] if not in the context of a quotation expander. *)
  value expand_quotation : Ploc.t -> (string -> 'b) -> int -> string -> string -> 'b ;
  value handle_expr_quotation : MLast.loc -> (string * string) -> MLast.expr;
  value handle_patt_quotation : MLast.loc -> (string * string) -> MLast.patt;
  value expr_eoi : Grammar.Entry.e MLast.expr;
  value patt_eoi : Grammar.Entry.e MLast.patt;
  value pp_report_quotation_error :
    Format.formatter -> string -> string -> err_ctx -> unit ;
end ;

open Mlsyntax ;
module QuotationExpansion(PB : PARSEBASESIG) : QUOTATION_EXPANSION = struct
module PA = PB.Parsers ;
value quotation_loc = ref None;

List.iter (fun (n, f) -> add n f)
  [("id", ExStr (fun _ s -> "$0:" ^ s ^ "$"));
   ("string", ExStr (fun _ s -> "\"" ^ String.escaped s ^ "\""))];

value quotation_dump_file = ref (None : option string);

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
           let exc1 = Qerror name str Expanding exc in
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
           let exc1 = Qerror name str Expanding exc in
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
  [ Ploc.Exc iloc (Qerror _ _ Expanding exc) ->
      let ctx = ParsingResult iloc str in
      let exc1 = Qerror name str ctx exc in
      Ploc.raise loc exc1
  | Ploc.Exc _ (Qerror _ _ _ _ as exc) ->
      Ploc.raise loc exc
  | Ploc.Exc iloc exc ->
      let ctx = ParsingResult iloc str in
      let exc1 = Qerror name str ctx exc in
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
    try find name with exc ->
      let exc1 = Qerror name str Finding exc in
      raise (Ploc.Exc (Ploc.sub loc 0 shift) exc1)
  in
  let ast =
    match expander with
    [ ExStr f ->
        let new_str = expand_quotation loc (f in_expr) shift name str in
        parse_quotation_result entry loc shift name new_str
    | ExAst fe_fp ->
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

value expr_eoi = Grammar.Entry.create PA.gram "expr_eoi";
value patt_eoi = Grammar.Entry.create PA.gram "patt_eoi";
EXTEND
  expr_eoi:
    [ [ x = PA.expr; EOI -> x ] ]
  ;
  patt_eoi:
    [ [ x = PA.patt; EOI -> x ] ]
  ;
END;

value handle_expr_quotation loc x =
  handle_quotation loc fst fst True expr_eoi Reloc.expr x
;

value handle_patt_quotation loc x =
  handle_quotation loc snd snd False patt_eoi Reloc.patt x
;


value find_line loc str =
  let (bp, ep) = (Ploc.first_pos loc, Ploc.last_pos loc) in
  find 0 1 0 where rec find i line col =
    if i == String.length str then (line, 0, col)
    else if i == bp then (line, col, col + ep - bp)
    else if str.[i] == '\n' then find (succ i) (succ line) 0
    else find (succ i) line (succ col)
;


value pp_report_quotation_error pps name str ctx = do {
  let name = if name = "" then default.val else name in
  Format.pp_print_flush pps ();
  Format.pp_open_hovbox pps 2;
  eprintf "While %s \"%s\" for string \"%s\":"
    (match ctx with
     [ Finding -> "finding quotation"
     | Expanding -> "expanding quotation"
     | ParsingResult _ _ -> "parsing result of quotation" ])
    name str;
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
          if PB.input_file.val = "" then
            eprintf
              "\n(consider setting variable Pcaml.quotation_dump_file)\n"
          else eprintf " (consider using option -QD)\n";
          flush stderr
        } ]
  | _ -> do { eprintf "\n"; flush stderr } ]
};
end ;
