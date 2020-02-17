(* camlp5r pa_macro.cmo *)
(* pr_official.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Versdep;

value error loc msg = Ploc.raise loc (Failure msg);

value open_out_file () =
  match Pcaml.output_file.val with
  [ Some f -> open_out_bin f
  | None -> do { pervasives_set_binary_mode_out stdout True; stdout } ]
;

value first_loc_of_ast =
  fun
  [ [(_, loc) :: _] -> loc
  | [] -> Ploc.dummy ]
;

value interf (ast, eoi_loc) = do {
  let loc = first_loc_of_ast ast in
  let fname = Ploc.file_name loc in
  let pt = Ast2pt.interf fname (List.map fst ast) in
  let oc = open_out_file () in
  let fmt = Format.formatter_of_out_channel oc in
  IFDEF OCAML_VERSION < OCAML_4_05_0 THEN
    let _ = pt in
    ignore (error loc "compiler-libs not available in this version of ocaml")
  ELSE
    Pprintast.signature fmt pt
  END ;
  Format.(pp_print_flush fmt ()) ;
  flush oc;
  match Pcaml.output_file.val with
  [ Some _ -> close_out oc
  | None -> () ]
};

value implem (ast, eoi_loc) = do {
  let loc = first_loc_of_ast ast in
  let fname = Ploc.file_name loc in
  let pt = Ast2pt.implem fname (List.map fst ast) in
  let oc = open_out_file () in
  let fmt = Format.formatter_of_out_channel oc in
  IFDEF OCAML_VERSION < OCAML_4_05_0 THEN
    let _ = pt in
    ignore (error loc "compiler-libs not available in this version of ocaml")
  ELSE
    Pprintast.structure fmt pt
  END ;
  Format.(pp_print_flush fmt ()) ;
  flush oc;
  match Pcaml.output_file.val with
  [ Some _ -> close_out oc
  | None -> () ]
};

Pcaml.print_interf.val := interf;
Pcaml.print_implem.val := implem;
