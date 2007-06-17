(* camlp4r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: pr_dump.ml,v 1.5 2007/06/17 00:43:39 deraugla Exp $ *)

value open_out_file () =
  match Pcaml.output_file.val with
  [ Some f -> open_out_bin f
  | None -> do { set_binary_mode_out stdout True; stdout } ]
;

value interf ast = do {
  let fname = Pcaml.input_file.val in
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

value implem ast = do {
  let fname = Pcaml.input_file.val in
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
