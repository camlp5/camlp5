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

value pp_interf fmt (ast, eoi_loc) = do {
  let loc = first_loc_of_ast ast in
  let fname = Ploc.file_name loc in
  IFDEF OCAML_VERSION < OCAML_4_05_0 THEN
    let _ = fname in
    ignore (error loc "compiler-libs not available in this version of ocaml")
  ELSE
    let pt = Ast2pt.interf fname (List.map fst ast) in
    Pprintast.signature fmt pt
  END ;
  Format.(pp_print_flush fmt ()) ;
};

value interf (ast, eoi_loc) = do {
  let oc = open_out_file () in
  let fmt = Format.formatter_of_out_channel oc in
  pp_interf fmt (ast, eoi_loc) ;
  flush oc;
  match Pcaml.output_file.val with
  [ Some _ -> close_out oc
  | None -> () ]
};

value pp_implem fmt (ast, eoi_loc) = do {
  let loc = first_loc_of_ast ast in
  let fname = Ploc.file_name loc in
  IFDEF OCAML_VERSION < OCAML_4_05_0 THEN
    let _ = fname in
    ignore (error loc "compiler-libs not available in this version of ocaml")
  ELSE
    let pt = Ast2pt.implem fname (List.map fst ast) in
    Pprintast.structure fmt pt
  END ;
  Format.(pp_print_flush fmt ()) ;
};

value implem (ast, eoi_loc) = do {
  let oc = open_out_file () in
  let fmt = Format.formatter_of_out_channel oc in
  pp_implem fmt (ast, eoi_loc) ;
  flush oc;
  match Pcaml.output_file.val with
  [ Some _ -> close_out oc
  | None -> () ]
};

Pcaml.print_interf.val := interf;
Pcaml.print_implem.val := implem;

value with_buffer_formatter f arg = do {
  let b = Buffer.create 23 in
  let bfmt = Format.formatter_of_buffer b in
  f bfmt arg ;
  Format.pp_print_flush bfmt () ;
  Buffer.contents b
}
;

value pr_sig_item ast =
  with_buffer_formatter (fun bfmt () -> pp_interf bfmt ([(ast, Ploc.dummy)],Ploc.dummy)) ()
;

value pr_str_item ast =
  with_buffer_formatter (fun bfmt () -> pp_implem bfmt ([(ast, Ploc.dummy)],Ploc.dummy)) ()
;
