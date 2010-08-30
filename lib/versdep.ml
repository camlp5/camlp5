(* camlp5r pa_macro.cmo *)
(* $Id: versdep.ml,v 1.7 2010/08/30 00:45:14 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

open Parsetree;
open Longident;
open Asttypes;

IFDEF OCAML_3_00 OR OCAML_3_01 OR OCAML_3_02 THEN
  DEFINE OCAML_3_02_OR_BEFORE
END;
IFDEF OCAML_3_02_OR_BEFORE OR OCAML_3_03 OR OCAML_3_04 THEN
  DEFINE OCAML_3_04_OR_BEFORE
END;
IFDEF OCAML_3_04_OR_BEFORE OR OCAML_3_05 OR OCAML_3_06 THEN
  DEFINE OCAML_3_06_OR_BEFORE
END;
IFDEF
  OCAML_3_06_OR_BEFORE OR OCAML_3_07 OR
  OCAML_3_08_0 OR OCAML_3_08_1 OR OCAML_3_08_2 OR OCAML_3_08_3 OR OCAML_3_08_4
THEN
  DEFINE OCAML_3_08_OR_BEFORE
END;
IFDEF OCAML_3_12_0 OR OCAML_3_12_1 OR OCAML_3_13_0 THEN
  DEFINE OCAML_3_12_OR_AFTER
END;
IFDEF
  OCAML_3_11 OR OCAML_3_11_0 OR OCAML_3_11_1 OR OCAML_3_11_2 OR
  OCAML_3_11_3 OR OCAML_3_12_OR_AFTER
THEN
  DEFINE OCAML_3_11_OR_AFTER
END;
IFDEF
  OCAML_3_10 OR OCAML_3_10_0 OR OCAML_3_10_1 OR OCAML_3_10_2 OR
  OCAML_3_10_3 OR OCAML_3_11_OR_AFTER
THEN
  DEFINE OCAML_3_10_OR_AFTER
END;

type choice 'a 'b =
  [ Left of 'a
  | Right of 'b ]
;

value sys_ocaml_version =
  IFDEF OCAML_3_00 THEN "3.00"
  ELSIFDEF OCAML_3_01 THEN "3.01"
  ELSIFDEF OCAML_3_02 THEN "3.02"
  ELSIFDEF OCAML_3_03 THEN "3.03"
  ELSIFDEF OCAML_3_04 THEN "3.04"
  ELSE Sys.ocaml_version END
;

value ocaml_location (fname, lnum, bolp, bp, ep) =
  IFDEF OCAML_3_06_OR_BEFORE THEN
    {Location.loc_start = bp; Location.loc_end = ep;
     Location.loc_ghost = bp = 0 && ep = 0}
  ELSE
    let loc_at n =
      {Lexing.pos_fname = if lnum = -1 then "" else fname;
       Lexing.pos_lnum = lnum; Lexing.pos_bol = bolp; Lexing.pos_cnum = n}
    in
    {Location.loc_start = loc_at bp; Location.loc_end = loc_at ep;
     Location.loc_ghost = bp = 0 && ep = 0}
  END
;

value ocaml_ptyp_poly =
  IFDEF OCAML_3_04_OR_BEFORE THEN None
  ELSE Some (fun cl t -> Ptyp_poly cl t) END
;

value ocaml_type_declaration params cl tk pf tm loc variance =
  IFDEF OCAML_3_11_OR_AFTER THEN
    {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
     ptype_private = pf; ptype_manifest = tm; ptype_loc = loc;
     ptype_variance = variance}
  ELSIFDEF OCAML_3_00 THEN
    {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
     ptype_manifest = tm; ptype_loc = loc}
  ELSE
    {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
     ptype_manifest = tm; ptype_loc = loc; ptype_variance = variance}
  END
;

value ocaml_ptype_record ltl priv =
  IFDEF OCAML_3_08_OR_BEFORE THEN
    let ltl = List.map (fun (n, m, t, _) -> (n, m, t)) ltl in
    IFDEF OCAML_3_06_OR_BEFORE THEN
      Ptype_record ltl
    ELSE
      Ptype_record ltl priv
    END
  ELSIFDEF OCAML_3_11_OR_AFTER THEN
    Ptype_record ltl
  ELSE
    Ptype_record ltl priv
  END
;

value ocaml_ptype_variant ctl priv =
  IFDEF OCAML_3_08_OR_BEFORE THEN
    let ctl = List.map (fun (c, tl, _) -> (c, tl)) ctl in
    IFDEF OCAML_3_06_OR_BEFORE THEN
      Ptype_variant ctl
    ELSE
      Ptype_variant ctl priv
    END
  ELSIFDEF OCAML_3_11_OR_AFTER THEN
    Ptype_variant ctl
  ELSE
    Ptype_variant ctl priv
  END
;

value ocaml_ptyp_variant catl clos sl_opt =
  IFDEF OCAML_3_02_OR_BEFORE THEN
    try
      let catl =
        List.map
          (fun
           [ Left (c, a, tl) -> (c, a, tl)
           | Right t -> raise Exit ])
          catl
      in
      let sl = match sl_opt with [ Some sl -> sl | None -> [] ] in
      Some (Ptyp_variant catl clos sl)
    with
    [ Exit -> None ]
  ELSE
    let catl =
      List.map
        (fun
         [ Left (c, a, tl) -> Rtag c a tl
         | Right t -> Rinherit t ])
        catl
    in
    Some (Ptyp_variant catl clos sl_opt)
  END
;

value ocaml_ptype_private =
  IFDEF OCAML_3_08_OR_BEFORE OR OCAML_3_11_OR_AFTER THEN Ptype_abstract
  ELSE Ptype_private END
;

value ocaml_class_infos virt params name expr loc variance =
  IFDEF OCAML_3_00 THEN
    {pci_virt = virt; pci_params = params; pci_name = name; pci_expr = expr;
     pci_loc = loc}
  ELSE
    {pci_virt = virt; pci_params = params; pci_name = name; pci_expr = expr;
     pci_loc = loc; pci_variance = variance}
  END
;

value ocaml_pexp_assertfalse fname loc =
  IFDEF OCAML_3_00 THEN
    let ghexp d = {pexp_desc = d; pexp_loc = loc} in
    let triple =
      ghexp (Pexp_tuple
             [ghexp (Pexp_constant (Const_string fname));
              ghexp (Pexp_constant (Const_int loc.Location.loc_start));
              ghexp (Pexp_constant (Const_int loc.Location.loc_end))])
    in
    let excep = Ldot (Lident "Pervasives", "Assert_failure") in
    let bucket = ghexp (Pexp_construct (excep, Some triple, false)) in
    let raise_ = ghexp (Pexp_ident (Ldot (Lident "Pervasives", "raise"))) in
    Pexp_apply (raise_, [("", bucket)])
  ELSE Pexp_assertfalse END
;

value ocaml_pexp_assert fname loc e =
  IFDEF OCAML_3_00 THEN
    let ghexp d = {pexp_desc = d; pexp_loc = loc} in
    let ghpat d = {ppat_desc = d; ppat_loc = loc} in
    let triple =
      ghexp (Pexp_tuple
             [ghexp (Pexp_constant (Const_string fname));
              ghexp (Pexp_constant (Const_int loc.Location.loc_start));
              ghexp (Pexp_constant (Const_int loc.Location.loc_end))])
    in
    let excep = Ldot (Lident "Pervasives", "Assert_failure") in
    let bucket = ghexp (Pexp_construct (excep, Some triple, false)) in
    let raise_ = ghexp (Pexp_ident (Ldot (Lident "Pervasives", "raise"))) in
    let raise_af = ghexp (Pexp_apply (raise_, [("", bucket)])) in
    let under = ghpat Ppat_any in
    let false_ = ghexp (Pexp_construct (Lident "false", None, false)) in
    let try_e = ghexp (Pexp_try (e, [(under, false_)])) in

    let not_ = ghexp (Pexp_ident (Ldot (Lident "Pervasives", "not"))) in
    let not_try_e = ghexp (Pexp_apply (not_, [("", try_e)])) in
    Pexp_ifthenelse (not_try_e, raise_af, None)
  ELSE Pexp_assert e END
;

value ocaml_pexp_lazy =
  IFDEF OCAML_3_04_OR_BEFORE THEN None ELSE Some (fun e -> Pexp_lazy e) END
;

value ocaml_const_int32 =
  IFDEF OCAML_3_06_OR_BEFORE THEN None
  ELSE Some (fun s -> Const_int32 (Int32.of_string s)) END
;

value ocaml_const_int64 =
  IFDEF OCAML_3_06_OR_BEFORE THEN None
  ELSE Some (fun s -> Const_int64 (Int64.of_string s)) END
;

value ocaml_const_nativeint =
  IFDEF OCAML_3_06_OR_BEFORE THEN None
  ELSE Some (fun s -> Const_nativeint (Nativeint.of_string s)) END
;

value ocaml_pexp_object =
  IFDEF OCAML_3_06_OR_BEFORE OR OCAML_3_07 THEN None
  ELSE Some (fun cs -> Pexp_object cs) END
;

value module_prefix_can_be_in_first_record_label_only =
  IFDEF OCAML_3_06_OR_BEFORE OR OCAML_3_07 THEN False ELSE True END
;

value ocaml_ppat_lazy =
  IFDEF OCAML_3_11_OR_AFTER THEN Some (fun p -> Ppat_lazy p) ELSE None END
;

value ocaml_ppat_record lpl =
  IFDEF OCAML_3_12_OR_AFTER THEN Ppat_record lpl Closed
  ELSE Ppat_record lpl END
;

value ocaml_psig_recmodule =
  IFDEF OCAML_3_06_OR_BEFORE THEN None
  ELSE Some (fun ntl -> Psig_recmodule ntl) END
;

value ocaml_pstr_include =
  IFDEF OCAML_3_00 THEN None ELSE Some (fun me -> Pstr_include me) END
;

value ocaml_pstr_recmodule =
  IFDEF OCAML_3_06_OR_BEFORE THEN None
  ELSE Some (fun nel -> Pstr_recmodule nel) END
;

value ocaml_pctf_val (s, b, t, loc) =
  IFDEF OCAML_3_10_OR_AFTER THEN Pctf_val (s, b, Concrete, t, loc)
  ELSE Pctf_val (s, b, Some t, loc) END
;

value ocaml_pcf_inher ce pb =
  IFDEF OCAML_3_12_OR_AFTER THEN Pcf_inher Fresh ce pb
  ELSE Pcf_inher ce pb END
;

value ocaml_pcf_meth (s, b, e, loc) =
  IFDEF OCAML_3_12_OR_AFTER THEN Pcf_meth (s, b, Fresh, e, loc) 
  ELSE Pcf_meth (s, b, e, loc) END
;

value ocaml_pcf_val (s, b, e, loc) =
  IFDEF OCAML_3_12_OR_AFTER THEN Pcf_val (s, b, Fresh, e, loc)
  ELSE Pcf_val (s, b, e,  loc) END
;

value ocaml_pexp_poly =
  IFDEF OCAML_3_04_OR_BEFORE THEN None
  ELSE Some (fun e t -> Pexp_poly e t) END
;

value arg_set_string =
  fun
  [ IFNDEF OCAML_3_06_OR_BEFORE THEN Arg.Set_string r -> Some r END
  | _ -> None ]
;

value arg_set_int =
  fun
  [ IFNDEF OCAML_3_06_OR_BEFORE THEN Arg.Set_int r -> Some r END
  | _ -> None ]
;

value arg_set_float =
  fun
  [ IFNDEF OCAML_3_06_OR_BEFORE THEN Arg.Set_float r -> Some r END
  | _ -> None ]
;

value arg_symbol =
  fun
  [ IFNDEF OCAML_3_06_OR_BEFORE THEN Arg.Symbol s f -> Some (s, f) END
  | _ -> None ]
;

value arg_tuple =
  fun
  [ IFNDEF OCAML_3_06_OR_BEFORE THEN Arg.Tuple t -> Some t END
  | _ -> None ]
;

value arg_bool =
  fun
  [ IFNDEF OCAML_3_06_OR_BEFORE THEN Arg.Bool f -> Some f END
  | _ -> None ]
;

IFDEF OCAML_3_04_OR_BEFORE THEN
  declare
    value scan_format fmt i kont =
      match fmt.[i+1] with
      [ 'c' -> Obj.magic (fun (c : char) -> kont (String.make 1 c) (i + 2))
      | 'd' -> Obj.magic (fun (d : int) -> kont (string_of_int d) (i + 2))
      | 's' -> Obj.magic (fun (s : string) -> kont s (i + 2))
      | c ->
          failwith
            (Printf.sprintf "Pretty.sprintf \"%s\" '%%%c' not impl" fmt c) ]
    ;
    value printf_ksprintf kont fmt =
      let fmt = (Obj.magic fmt : string) in
      let len = String.length fmt in
      doprn [] 0 where rec doprn rev_sl i =
        if i >= len then do {
          let s = String.concat "" (List.rev rev_sl) in
          Obj.magic (kont s)
        }
        else do {
          match fmt.[i] with
          [ '%' -> scan_format fmt i (fun s -> doprn [s :: rev_sl])
          | c -> doprn [String.make 1 c :: rev_sl] (i + 1)  ]
        }
    ;
  end
ELSE
  value printf_ksprintf = Printf.kprintf
END;
