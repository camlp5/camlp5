(* camlp5r *)
(* main.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "q_MLast.cmo" *)

open Printf;;
open Versdep;;

let print_location loc =
  let loc =
    if Ploc.file_name loc = "" then
      Ploc.make_loc !(Pcaml.input_file) 1 0 (0, 1) ""
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
  else eprintf "At location %d-%d\n" bp ep
;;

let print_warning loc s =
  print_location loc; eprintf "Warning: %s\n" s; flush stderr
;;

let report_error =
  function
    Odyl_main.Error (fname, msg) ->
      Format.print_string "Error while loading \"";
      Format.print_string fname;
      Format.print_string "\": ";
      Format.print_string msg
  | exc -> Pcaml.report_error exc
;;

let report_error_and_exit exc =
  Format.set_formatter_out_channel stderr;
  Format.open_vbox 0;
  let exc =
    match exc with
      Ploc.Exc (loc, exc) -> print_location loc; exc
    | _ -> exc
  in
  report_error exc; Format.close_box (); Format.print_newline (); exit 2
;;

Pcaml.add_directive "load"
  (function
     Some (MLast.ExStr (_, s)) -> Odyl_main.loadfile s
   | Some _ | None -> raise Not_found);;

Pcaml.add_directive "directory"
  (function
     Some (MLast.ExStr (_, s)) -> Odyl_main.directory s
   | Some _ | None -> raise Not_found);;

let rec parse_file pa getdir useast =
  let name = !(Pcaml.input_file) in
  Pcaml.warning := print_warning;
  let ic = if name = "-" then stdin else open_in_bin name in
  let cs = Stream.of_channel ic in
  let clear () = if name = "-" then () else close_in ic in
  let phr =
    try
      let rec loop rev_pl =
        let (pl, status) = pa cs in
        match status with
          None ->
            let lexing_info = !(!(Plexing.line_nb)), !(!(Plexing.bol_pos)) in
            let pl =
              let rpl = List.rev pl in
              match getdir rpl with
                Some x ->
                  begin match x with
                    loc1, "use", Some (MLast.ExStr (_, s)) ->
                      let (pl, eloc) = use_file pa getdir useast s in
                      list_rev_append rpl [useast loc1 s pl, loc1]
                  | loc, x, eo ->
                      begin try Pcaml.find_directive x eo with
                        Not_found ->
                          begin let msg = sprintf "unknown directive #%s" x in
                            Ploc.raise loc (Stream.Error msg)
                          end
                      end;
                      pl
                  end
              | None -> pl
            in
            Plexing.restore_lexing_info := Some lexing_info;
            loop (list_rev_append pl rev_pl)
        | Some loc -> List.rev (list_rev_append pl rev_pl), loc
      in
      loop []
    with x -> clear (); raise x
  in
  clear (); phr
and use_file pa getdir useast s =
  let v_input_file = !(Pcaml.input_file) in
  Pcaml.input_file := s;
  try
    let r = parse_file pa getdir useast in Pcaml.input_file := v_input_file; r
  with e -> report_error_and_exit e
;;

let process pa pr getdir useast = pr (parse_file pa getdir useast);;

let gind =
  function
    (MLast.SgDir (loc, n, dp), _) :: _ ->
      Some (loc, Pcaml.unvala n, Pcaml.unvala dp)
  | _ -> None
;;

let gimd =
  function
    (MLast.StDir (loc, n, dp), _) :: _ ->
      Some (loc, Pcaml.unvala n, Pcaml.unvala dp)
  | _ -> None
;;

let usesig loc fname ast = MLast.SgUse (loc, fname, ast);;
let usestr loc fname ast = MLast.StUse (loc, fname, ast);;

let process_intf () =
  process !(Pcaml.parse_interf) !(Pcaml.print_interf) gind usesig
;;
let process_impl () =
  process !(Pcaml.parse_implem) !(Pcaml.print_implem) gimd usestr
;;

type file_kind = Intf | Impl;;
let file_kind = ref Intf;;
let file_kind_of_name name =
  if Filename.check_suffix name ".mli" then Intf
  else if Filename.check_suffix name ".ml" then Impl
  else raise (Arg.Bad ("don't know what to do with " ^ name))
;;

let print_version () =
  eprintf "Camlp5 version %s (ocaml %s)\n" Pcaml.version Pcaml.ocaml_version;
  flush stderr;
  exit 0
;;

let initial_spec_list =
  ["-intf", Arg.String (fun x -> file_kind := Intf; Pcaml.input_file := x),
   "<file>  Parse <file> as an interface, whatever its extension.";
   "-impl", Arg.String (fun x -> file_kind := Impl; Pcaml.input_file := x),
   "<file>  Parse <file> as an implementation, whatever its extension.";
   "-unsafe", Arg.Set Ast2pt.fast,
   "Generate unsafe accesses to array and strings.";
   "-verbose", Arg.Set Grammar.error_verbose,
   "More verbose in parsing errors.";
   "-loc", Arg.String (fun x -> Ploc.name := x),
   "<name>   Name of the location variable (default: " ^ !(Ploc.name) ^ ")";
   "-QD", Arg.String (fun x -> Pcaml.quotation_dump_file := Some x),
   "<file> Dump quotation expander result in case of syntax error.";
   "-o", Arg.String (fun x -> Pcaml.output_file := Some x),
   "<file> Output on <file> instead of standard output.";
   "-v", Arg.Unit print_version, "Print Camlp5 version and exit."]
;;

let anon_fun x = Pcaml.input_file := x; file_kind := file_kind_of_name x;;

let parse_options sl =
  let ext_spec_list = Pcaml.arg_spec_list () in
  let arg_spec_list = initial_spec_list @ ext_spec_list in
  match Argl.parse arg_spec_list anon_fun sl with
    [] -> None
  | ["-help"] -> Argl.usage initial_spec_list ext_spec_list; Some 0
  | s :: sl ->
      eprintf "%s: unknown or misused option\n" s;
      eprintf "Use option -help for usage\n";
      Some 2
;;

Pcaml.add_directive "option"
  (function
     Some (MLast.ExStr (_, s)) ->
       begin match parse_options [s] with
         Some 0 | None -> ()
       | Some x -> failwith "bad option"
       end
   | Some (MLast.ExApp (_, MLast.ExStr (_, s1), MLast.ExStr (_, s2))) ->
       begin match parse_options [s1; s2] with
         Some 0 | None -> ()
       | Some x -> failwith "bad option"
       end
   | Some _ | None -> raise Not_found);;

let remaining_args =
  let rec loop l i =
    if i == Array.length Sys.argv then l else loop (Sys.argv.(i) :: l) (i + 1)
  in
  List.rev (loop [] (!(Arg.current) + 1))
;;

let go () =
  begin try
    match parse_options remaining_args with
      Some code -> exit code
    | None -> ()
  with Arg.Bad s ->
    eprintf "Error: %s\n" s;
    eprintf "Use option -help for usage\n";
    flush stderr;
    exit 2
  end;
  try
    if !(Pcaml.input_file) <> "" then
      match !file_kind with
        Intf -> process_intf ()
      | Impl -> process_impl ()
  with exc -> report_error_and_exit exc
;;

Odyl_main.name := "camlp5";;
Odyl_main.go := go;;
