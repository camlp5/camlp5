(* camlp5r *)
(* pr_dump.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Versdep;

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
  output_string oc Pconfig.ast_intf_magic_number;
  output_value oc (if fname = "-" then "" else fname);
  output_value oc pt;
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
  output_string oc Pconfig.ast_impl_magic_number;
  output_value oc (if fname = "-" then "" else fname);
  output_value oc pt;
  flush oc;
  match Pcaml.output_file.val with
  [ Some _ -> close_out oc
  | None -> () ]
};

Pcaml.print_interf.val := interf;
Pcaml.print_implem.val := implem;
