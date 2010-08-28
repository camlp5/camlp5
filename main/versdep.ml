(* camlp5r pa_macro.cmo *)
(* $Id: versdep.ml,v 1.10 2010/08/28 17:22:20 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

open Parsetree;
open Longident;
open Asttypes;

IFDEF
  OCAML_3_02 OR OCAML_3_04 OR OCAML_3_05 OR OCAML_3_06
THEN
  DEFINE OCAML_3_06_OR_BEFORE
END;

IFDEF
  OCAML_3_06_OR_BEFORE OR OCAML_3_07 OR
  OCAML_3_08_0 OR OCAML_3_08_1 OR OCAML_3_08_2 OR OCAML_3_08_3 OR OCAML_3_08_4
THEN
  DEFINE OCAML_3_08_OR_BEFORE
END;

IFDEF
  OCAML_3_12_0 OR OCAML_3_12_1 OR OCAML_3_13_0
THEN
  DEFINE AFTER_OCAML_3_12
END;

IFDEF
  OCAML_3_11 OR OCAML_3_11_0 OR OCAML_3_11_1 OR OCAML_3_11_2 OR
  OCAML_3_11_3 OR AFTER_OCAML_3_12
THEN
  DEFINE AFTER_OCAML_3_11
END;

IFDEF
  OCAML_3_10 OR OCAML_3_10_0 OR OCAML_3_10_1 OR OCAML_3_10_2 OR
  OCAML_3_10_3 OR AFTER_OCAML_3_11
THEN
  DEFINE AFTER_OCAML_3_10
END;

value sys_ocaml_version =
  IFDEF OCAML_3_04 THEN "3.04" ELSE Sys.ocaml_version END
;

let ov = sys_ocaml_version in
let oi =
  loop 0 where rec loop i =
    if i = String.length ov then i
    else
      match ov.[i] with
      [ ' ' | '+' -> i
      | _ -> loop (i + 1) ]
in
let ov = String.sub ov 0 oi in
if ov <> Pconfig.ocaml_version then do {
  flush stdout;
  Printf.eprintf "\n";
  Printf.eprintf "This ocaml and this camlp5 are not compatible:\n";
  Printf.eprintf "- OCaml version is %s\n" sys_ocaml_version;
  Printf.eprintf "- Camlp5 compiled with ocaml %s\n" Pconfig.ocaml_version;
  Printf.eprintf "\n";
  Printf.eprintf "You need to recompile camlp5.\n";
  Printf.eprintf "\n";
  flush stderr;
  failwith "bad version"
}
else ();

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
  IFDEF OCAML_3_04 THEN None ELSE Some (fun cl t -> Ptyp_poly cl t) END
;

value ocaml_type_declaration params cl tk pf tm loc variance =
  IFDEF AFTER_OCAML_3_11 THEN
    {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
     ptype_private = pf; ptype_manifest = tm; ptype_loc = loc;
     ptype_variance = variance}
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
  ELSE IFDEF AFTER_OCAML_3_11 THEN
    Ptype_record ltl
  ELSE
    Ptype_record ltl priv
  END END
;

value ocaml_ptype_variant ctl priv =
  IFDEF OCAML_3_08_OR_BEFORE THEN
    let ctl = List.map (fun (c, tl, _) -> (c, tl)) ctl in
    IFDEF OCAML_3_06_OR_BEFORE THEN
      Ptype_variant ctl
    ELSE
      Ptype_variant ctl priv
    END
  ELSE IFDEF AFTER_OCAML_3_11 THEN
    Ptype_variant ctl
  ELSE
    Ptype_variant ctl priv
  END END
;

value ocaml_ptype_private =
  IFDEF OCAML_3_08_OR_BEFORE OR AFTER_OCAML_3_11 THEN Ptype_abstract
  ELSE Ptype_private END
;

value ocaml_pwith_type params tk pf ct variance loc =
  IFDEF AFTER_OCAML_3_11 THEN
    let pf = if pf then Private else Public in
    Pwith_type
      {ptype_params = params; ptype_cstrs = [];
       ptype_kind = tk; ptype_private = pf;
       ptype_manifest = ct; ptype_variance = variance;
       ptype_loc = loc}
  ELSE
    Pwith_type
      {ptype_params = params; ptype_cstrs = [];
       ptype_kind = tk; ptype_manifest = ct;
       ptype_variance = variance; ptype_loc = loc}
  END
;

value ocaml_pexp_lazy =
  IFDEF OCAML_3_04 THEN None ELSE Some (fun e -> Pexp_lazy e) END
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
  IFDEF AFTER_OCAML_3_11 THEN Some (fun p -> Ppat_lazy p) ELSE None END
;

value ocaml_ppat_record lpl =
  IFDEF AFTER_OCAML_3_12 THEN Ppat_record lpl Closed ELSE Ppat_record lpl END
;

value ocaml_psig_recmodule =
  IFDEF OCAML_3_06_OR_BEFORE THEN None
  ELSE Some (fun ntl -> Psig_recmodule ntl) END
;

value ocaml_pstr_recmodule =
  IFDEF OCAML_3_06_OR_BEFORE THEN None
  ELSE Some (fun nel -> Pstr_recmodule nel) END
;

value ocaml_pctf_val (s, b, t, loc) =
  IFDEF AFTER_OCAML_3_10 THEN Pctf_val (s, b, Concrete, t, loc)
  ELSE Pctf_val (s, b, Some t, loc) END
;

value ocaml_pcf_inher ce pb =
  IFDEF AFTER_OCAML_3_12 THEN Pcf_inher Fresh ce pb ELSE Pcf_inher ce pb END
;

value ocaml_pcf_meth (s, b, e, loc) =
  IFDEF AFTER_OCAML_3_12 THEN Pcf_meth (s, b, Fresh, e, loc) 
  ELSE Pcf_meth (s, b, e, loc) END
;

value ocaml_pcf_val (s, b, e, loc) =
  IFDEF AFTER_OCAML_3_12 THEN Pcf_val (s, b, Fresh, e, loc)
  ELSE Pcf_val (s, b, e,  loc) END
;

value ocaml_pexp_poly =
  IFDEF OCAML_3_04 THEN None ELSE Some (fun e t -> Pexp_poly e t) END
;

(**)

value action_arg s sl =
  fun
  [ Arg.Unit f -> if s = "" then do { f (); Some sl } else None
  | Arg.Set r -> if s = "" then do { r.val := True; Some sl } else None
  | Arg.Clear r -> if s = "" then do { r.val := False; Some sl } else None
  | Arg.Rest f -> do { List.iter f [s :: sl]; Some [] }
  | Arg.String f ->
      if s = "" then
        match sl with
        [ [s :: sl] -> do { f s; Some sl }
        | [] -> None ]
      else do { f s; Some sl }
  | Arg.Int f ->
      if s = "" then
        match sl with
        [ [s :: sl] ->
            try do { f (int_of_string s); Some sl } with
            [ Failure "int_of_string" -> None ]
        | [] -> None ]
      else
        try do { f (int_of_string s); Some sl } with
        [ Failure "int_of_string" -> None ]
  | Arg.Float f ->
      if s = "" then
        match sl with
        [ [s :: sl] -> do { f (float_of_string s); Some sl }
        | [] -> None ]
      else do { f (float_of_string s); Some sl }
  | IFNDEF OCAML_3_06_OR_BEFORE THEN
      Arg.Set_string r ->
          if s = "" then
            match sl with
            [ [s :: sl] -> do { r.val := s; Some sl }
            | [] -> None ]
          else do { r.val := s; Some sl }
      END
  | IFNDEF OCAML_3_06_OR_BEFORE THEN
      Arg.Set_int r ->
        if s = "" then
          match sl with
          [ [s :: sl] ->
              try do { r.val := int_of_string s; Some sl } with
              [ Failure "int_of_string" -> None ]
          | [] -> None ]
        else
          try do { r.val := int_of_string s; Some sl } with
          [ Failure "int_of_string" -> None ]
    END
  | IFNDEF OCAML_3_06_OR_BEFORE THEN
      Arg.Set_float r ->
        if s = "" then
          match sl with
          [ [s :: sl] -> do { r.val := float_of_string s; Some sl }
          | [] -> None ]
        else do { r.val := float_of_string s; Some sl }
    END
  | IFNDEF OCAML_3_06_OR_BEFORE THEN
      Arg.Symbol syms f ->
        match if s = "" then sl else [s :: sl] with
        [ [s :: sl] when List.mem s syms -> do { f s; Some sl }
        | _ -> None ]
    END
  | IFNDEF OCAML_3_06_OR_BEFORE THEN
      Arg.Tuple _ -> failwith "Arg.Tuple not implemented"
    END
  | IFNDEF OCAML_3_06_OR_BEFORE THEN
      Arg.Bool _ -> failwith "Arg.Bool not implemented"
    END ]
;

value arg_symbol =
  IFDEF OCAML_3_06_OR_BEFORE THEN fun _ -> None
  ELSE
    fun
    [ Arg.Symbol symbs _ -> Some symbs
    | _ -> None ]
  END
;
