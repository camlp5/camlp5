(* camlp5r q_MLast.cmo ./pa_extprint.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Pretty;
open Pcaml;
open Prtools;

do {
(*
  Eprinter.clear pr_expr;
  Eprinter.clear pr_patt;
  Eprinter.clear pr_ctyp;
*)
  Eprinter.clear pr_str_item;
  Eprinter.clear pr_sig_item;
(*
  Eprinter.clear pr_module_expr;
  Eprinter.clear pr_module_type;
  Eprinter.clear pr_class_sig_item;
  Eprinter.clear pr_class_str_item;
  Eprinter.clear pr_class_expr;
  Eprinter.clear pr_class_type;
*)
};

(* general functions *)

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_scheme_new, not impl: %s; %s\"%s" pc.bef name
    (String.escaped desc) pc.aft
;

value rec mod_ident pc sl =
  match sl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [s] -> sprintf "%s%s%s" pc.bef s pc.aft
  | [s :: sl] -> mod_ident {(pc) with bef = sprintf "%s%s." pc.bef s} sl ]
;

(*
 * Extensible printers
 *)

(*
value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value ctyp = Eprinter.apply pr_ctyp;
*)
value str_item = Eprinter.apply pr_str_item;
value sig_item = Eprinter.apply pr_sig_item;
(*
value module_expr = Eprinter.apply pr_module_expr;
value module_type = Eprinter.apply pr_module_type;
value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;
*)

EXTEND_PRINTER
  pr_sig_item:
    [ "top"
      [ (* <:sig_item< type $list:tdl$ >> ->
          match tdl with
          [ [td] -> sprintf "(%s" (type_decl (("type", td), ks ")" k))
          | tdl ->
              fprintf ppf "(@[<hv>type@ %a@]" (listwb "" type_decl)
                (tdl, ks ")" k) ]
      | <:sig_item< exception $uid:c$ of $list:tl$ >> ->
          fun ppf curr next dg k ->
            match tl with
            [ [] -> fprintf ppf "(@[exception@ %s%t@]" c (ks ")" k)
            | tl ->
                fprintf ppf "(@[@[exception@ %s@]@ %a@]" c
                  (list ctyp) (tl, ks ")" k) ]
      | <:sig_item< value $lid:i$ : $t$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[value %s@]@ %a@]" i ctyp (t, ks ")" k)
      | <:sig_item< external $lid:i$ : $t$ = $list:pd$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[external@ %s@]@ %a@ %a@]" i ctyp (t, nok)
              (list string) (pd, ks ")" k)
      | <:sig_item< module $uid:s$ : $mt$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[module@ %s@]@ %a@]" s
              module_type (mt, ks ")" k)
      | <:sig_item< module type $uid:s$ = $mt$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[moduletype@ %s@]@ %a@]" s
              module_type (mt, ks ")" k)
      | <:sig_item< declare $list:s$ end >> ->
          fun ppf curr next dg k ->
            if s = [] then fprintf ppf "; ..."
            else fprintf ppf "%a" (list sig_item) (s, k)
      | MLast.SgUse _ _ _ ->
          fun ppf curr next dg k -> ()
      | *) x ->
          not_impl "sig_item" pc x ] ]
  ;
  pr_str_item:
    [ "top"
      [ <:str_item< open $i$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(open %s)%s" pc.bef
                 (mod_ident {(pc) with bef = ""; aft = ""} i) pc.aft)
            (fun () ->
               not_impl "str_item open vertic" pc i)
(*
      | <:str_item< type $list:tdl$ >> ->
          fun ppf curr next dg k ->
            match tdl with
            [ [td] -> fprintf ppf "(%a" type_decl (("type", td), ks ")" k)
            | tdl ->
                fprintf ppf "(@[<hv>type@ %a@]" (listwb "" type_decl)
                  (tdl, ks ")" k) ]
      | <:str_item< exception $uid:c$ of $list:tl$ >> ->
          fun ppf curr next dg k ->
            match tl with
            [ [] -> fprintf ppf "(@[exception@ %s%t@]" c (ks ")" k)
            | tl ->
                fprintf ppf "(@[@[exception@ %s@]@ %a@]" c
                  (list ctyp) (tl, ks ")" k) ]
      | <:str_item< value $flag:rf$ $list:pel$ >> ->
          fun ppf curr next dg k ->
            let b = if rf then "definerec" else "define" in
            match pel with
            [ [(p, e)] ->
                fprintf ppf "%a" let_binding ((b, (p, e)), k)
            | pel ->
                fprintf ppf "(@[<hv 1>%s*@ %a@]" b (listwb "" let_binding)
                  (pel, ks ")" k) ]
      | <:str_item< module $uid:s$ = $me$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(%a" module_binding (("module", s, me), ks ")" k)
      | <:str_item< module type $uid:s$ = $mt$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[moduletype@ %s@]@ %a@]" s
              module_type (mt, ks ")" k)
      | <:str_item< external $lid:i$ : $t$ = $list:pd$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[external@ %s@ %a@ %a@]" i ctyp (t, nok)
              (list string) (pd, ks ")" k)
      | <:str_item< $exp:e$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "%a" expr (e, k)
      | <:str_item< # $lid:s$ $opt:x$ >> ->
          fun ppf curr next dg k ->
            match x with
            [ Some e -> fprintf ppf "; # (%s %a" s expr (e, ks ")" k)
            | None -> fprintf ppf "; # (%s%t" s (ks ")" k) ]
      | <:str_item< declare $list:s$ end >> ->
          fun ppf curr next dg k ->
            if s = [] then fprintf ppf "; ..."
            else fprintf ppf "%a" (list str_item) (s, k)
      | MLast.StUse _ _ _ ->
          fun ppf curr next dg k -> ()
*)
      | x ->
          not_impl "str_item" pc x ] ]
  ;
END;

(* main part *)

value sep = ref None;

value output_string_eval oc s =
  loop 0 where rec loop i =
    if i == String.length s then ()
    else if i == String.length s - 1 then output_char oc s.[i]
    else
      match (s.[i], s.[i + 1]) with
      [ ('\\', 'n') -> do { output_char oc '\n'; loop (i + 2) }
      | (c, _) -> do { output_char oc c; loop (i + 1) } ]
;

value input_source src bp len =
  let len = min (max 0 len) (String.length src) in
  String.sub src bp len
;

value copy_source src oc first bp ep =
  match sep.val with
  [ Some str ->
      if first then ()
      else if ep == String.length src then output_string oc "\n"
      else output_string_eval oc str
  | None ->
      let s = input_source src bp (ep - bp) in
      output_string oc s ]
;

value copy_to_end src oc first bp =
  let ilen = String.length src in
  if bp < ilen then copy_source src oc first bp ilen
  else output_string oc "\n"
;

module Buff =
  struct
    value buff = ref (String.create 80);
    value store len x = do {
      if len >= String.length buff.val then
        buff.val := buff.val ^ String.create (String.length buff.val)
      else ();
      buff.val.[len] := x;
      succ len
    };
    value mstore len s =
      add_rec len 0 where rec add_rec len i =
        if i == String.length s then len
        else add_rec (store len s.[i]) (succ i)
    ;
    value get len = String.sub buff.val 0 len;
  end
;

value apply_printer f ast = do {
  if Pcaml.input_file.val = "-" then sep.val := Some "\n"
  else do {
    let ic = open_in_bin Pcaml.input_file.val in
    let src =
      loop 0 where rec loop len =
        match try Some (input_char ic) with [ End_of_file -> None ] with
        [ Some c -> loop (Buff.store len c)
        | None -> Buff.get len ]
    in
    Prtools.source.val := src;
    close_in ic
  };
  let oc =
    match Pcaml.output_file.val with
    [ Some f -> open_out_bin f
    | None -> stdout ]
  in
  let cleanup () =
    match Pcaml.output_file.val with
    [ Some f -> close_out oc
    | None -> () ]
  in
  try do {
    let (first, last_pos) =
      List.fold_left
        (fun (first, last_pos) (si, loc) -> do {
           let bp = Ploc.first_pos loc in
           let ep = Ploc.last_pos loc in
           copy_source Prtools.source.val oc first last_pos bp;
           flush oc;
           output_string oc (f {ind = 0; bef = ""; aft = ""; dang = ""} si);
           (False, ep)
         })
        (True, 0) ast
    in
    copy_to_end Prtools.source.val oc first last_pos;
    flush oc
  }
  with exn -> do {
    cleanup ();
    raise exn
  };
  cleanup ();
};

Pcaml.print_interf.val := apply_printer sig_item;
Pcaml.print_implem.val := apply_printer str_item;

Pcaml.add_option "-l" (Arg.Int (fun x -> Pretty.line_length.val := x))
  ("<length> Maximum line length for pretty printing (default " ^
     string_of_int Pretty.line_length.val ^ ")");

Pcaml.add_option "-sep_src" (Arg.Unit (fun () -> sep.val := None))
  "Read source file for text between phrases (default).";

Pcaml.add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";
