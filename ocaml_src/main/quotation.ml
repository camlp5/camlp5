(* camlp5r *)
(* quotation.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)
(* #load "pa_extend.cmo" *)

open Printf;;
open Pcamlbase;;

type expander =
    ExStr of (bool -> string -> string)
  | ExAst of ((string -> MLast.expr) * (string -> MLast.patt))
;;

let expanders_table = ref [];;

let default = ref "";;
let translate = ref (fun x -> x);;

let expander_name name =
  match !translate name with
    "" -> !default
  | name -> name
;;

let find name = List.assoc (expander_name name) !expanders_table;;

let add name f =
  if List.mem_assoc name !expanders_table then
    begin
      Printf.fprintf stderr
        "Failure: Quotation.add: cannot add the quotation \"%s\" twice\n%!"
        name;
      Ploc.raise Ploc.dummy
        (Failure
           Printf.
           (sprintf "Quotation.add: cannot add the quotation \"%s\" twice"
             name))
    end
  else expanders_table := (name, f) :: !expanders_table
;;

let upsert name f =
  if List.mem_assoc name !expanders_table then
    Printf.fprintf stderr
      "Warning: Quotation.upsert: overwriting the quotation \"%s\"\n%!" name;
  expanders_table := (name, f) :: !expanders_table
;;
module type QUOTATION_EXPANSION =
  sig
    val quotation_dump_file : string option ref;;
    val quotation_location : unit -> Ploc.t;;
    val expand_quotation :
      Ploc.t -> (string -> 'b) -> int -> string -> string -> 'b;;
    val handle_expr_quotation : MLast.loc -> string * string -> MLast.expr;;
    val handle_patt_quotation : MLast.loc -> string * string -> MLast.patt;;
    val expr_eoi : MLast.expr Grammar.Entry.e;;
    val patt_eoi : MLast.patt Grammar.Entry.e;;
    val pp_report_quotation_error :
      Format.formatter -> string -> string -> err_ctx -> unit;;
  end
;;

open Mlsyntax;;
module QuotationExpansion (PB : PARSEBASESIG) : QUOTATION_EXPANSION =
  struct
    module PA = PB.Parsers;;
    let quotation_loc = ref None;;
    List.iter (fun (n, f) -> add n f)
      ["id", ExStr (fun _ s -> "$0:" ^ s ^ "$");
       "string", ExStr (fun _ s -> "\"" ^ String.escaped s ^ "\"")];;
    let quotation_dump_file = ref (None : string option);;
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
              let exc1 = Qerror (name, str, Expanding, exc) in
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
              let exc1 = Qerror (name, str, Expanding, exc) in
              Ploc.raise gloc exc1
        with exn -> restore (); raise exn
      in
      restore (); r
    ;;
    let parse_quotation_result entry loc shift name str =
      let cs = Stream.of_string str in
      try Grammar.Entry.parse entry cs with
        Ploc.Exc (iloc, Qerror (_, _, Expanding, exc)) ->
          let ctx = ParsingResult (iloc, str) in
          let exc1 = Qerror (name, str, ctx, exc) in Ploc.raise loc exc1
      | Ploc.Exc (_, (Qerror (_, _, _, _) as exc)) -> Ploc.raise loc exc
      | Ploc.Exc (iloc, exc) ->
          let ctx = ParsingResult (iloc, str) in
          let exc1 = Qerror (name, str, ctx, exc) in Ploc.raise loc exc1
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
        try find name with
          exc ->
            let exc1 = Qerror (name, str, Finding, exc) in
            raise (Ploc.Exc (Ploc.sub loc 0 shift, exc1))
      in
      let ast =
        match expander with
          ExStr f ->
            let new_str = expand_quotation loc (f in_expr) shift name str in
            parse_quotation_result entry loc shift name new_str
        | ExAst fe_fp ->
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
    let expr_eoi = Grammar.Entry.create PA.gram "expr_eoi";;
    let patt_eoi = Grammar.Entry.create PA.gram "patt_eoi";;
    Grammar.safe_extend
      [Grammar.extension (expr_eoi : 'expr_eoi Grammar.Entry.e) None
         [None, None,
          [Grammar.production
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (PA.expr : 'PA__expr Grammar.Entry.e)))
                (Grammar.s_token ("EOI", "")),
              "194fe98d",
              (fun _ (x : 'PA__expr) (loc : Ploc.t) -> (x : 'expr_eoi)))]];
       Grammar.extension (patt_eoi : 'patt_eoi Grammar.Entry.e) None
         [None, None,
          [Grammar.production
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (PA.patt : 'PA__patt Grammar.Entry.e)))
                (Grammar.s_token ("EOI", "")),
              "194fe98d",
              (fun _ (x : 'PA__patt) (loc : Ploc.t) -> (x : 'patt_eoi)))]]];;
    let handle_expr_quotation loc x =
      handle_quotation loc fst fst true expr_eoi Reloc.expr x
    ;;
    let handle_patt_quotation loc x =
      handle_quotation loc snd snd false patt_eoi Reloc.patt x
    ;;
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
    let pp_report_quotation_error pps name str ctx =
      let name = if name = "" then !default else name in
      Format.pp_print_flush pps ();
      Format.pp_open_hovbox pps 2;
      eprintf "While %s \"%s\" for string \"%s\":"
        (match ctx with
           Finding -> "finding quotation"
         | Expanding -> "expanding quotation"
         | ParsingResult (_, _) -> "parsing result of quotation")
        name str;
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
              if !(PB.input_file) = "" then
                eprintf
                  "\n(consider setting variable Pcaml.quotation_dump_file)\n"
              else eprintf " (consider using option -QD)\n";
              flush stderr
          end
      | _ -> eprintf "\n"; flush stderr
    ;;
  end
;;
