(* camlp5r pa_macro.cmo *)
(* versdep.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Parsetree;;
open Longident;;
open Asttypes;;

type ('a, 'b) choice =
    Left of 'a
  | Right of 'b
;;

let option_map f x =
  match x with
    Some x -> Some (f x)
  | None -> None
;;
let mustSome symbol =
  function
    Some x -> x
  | None -> failwith ("Some: " ^ symbol)
;;

let mustLeft symbol =
  function
    Left x -> x
  | Right _ -> failwith ("choice: " ^ symbol)
;;

let mustRight symbol =
  function
    Left _ -> failwith ("choice: " ^ symbol)
  | Right x -> x
;;

let ocaml_name = "ocaml";;

let sys_ocaml_version = Sys.ocaml_version;;

let to_ghost_loc loc = {loc with Location.loc_ghost = true};;

let ocaml_location (fname, lnum, bolp, lnuml, bolpl, bp, ep) =
  let loc_at n lnum bolp =
    {Lexing.pos_fname = if lnum = -1 then "" else fname;
     Lexing.pos_lnum = lnum; Lexing.pos_bol = bolp; Lexing.pos_cnum = n}
  in
  {Location.loc_start = loc_at bp lnum bolp;
   Location.loc_end = loc_at ep lnuml bolpl;
   Location.loc_ghost = bp = 0 && ep = 0}
;;

let loc_none =
  let loc =
    {Lexing.pos_fname = "_none_"; pos_lnum = 1; pos_bol = 0; pos_cnum = -1}
  in
  {Location.loc_start = loc; Location.loc_end = loc;
   Location.loc_ghost = true}
;;

let mkloc loc txt = {Location.txt = txt; loc = loc};;
let mknoloc txt = mkloc loc_none txt;;

let ocaml_id_or_li_of_string_list loc sl =
  let mkli s =
    let rec loop f =
      function
        i :: il -> loop (fun s -> Ldot (f i, s)) il
      | [] -> f s
    in
    loop (fun s -> Lident s)
  in
  match List.rev sl with
    [] -> None
  | s :: sl -> Some (mkli s (List.rev sl))
;;

let not_extended_longident =
  let rec not_extended =
    function
      Lident _ -> true
    | Ldot (li, _) -> not_extended li
    | Lapply (_, _) -> false
  in
  not_extended
;;

let list_map_check f l =
  let rec loop rev_l =
    function
      x :: l ->
        begin match f x with
          Some s -> loop (s :: rev_l) l
        | None -> None
        end
    | [] -> Some (List.rev rev_l)
  in
  loop [] l
;;

let split_on_char = String.split_on_char;;

let labelled lab =
  if lab = "" then Nolabel
  else if lab.[0] = '?' then
    Optional (String.sub lab 1 (String.length lab - 1))
  else Labelled lab
;;

(* *)

let ocaml_value_description ?(item_attributes = []) vn t p =
  {pval_type = t; pval_prim = p; pval_loc = t.ptyp_loc;
   pval_name = mkloc t.ptyp_loc vn; pval_attributes = item_attributes}
;;

let ocaml_class_type_field ?(item_attributes = []) loc ctfd =
  {pctf_desc = ctfd; pctf_loc = loc; pctf_attributes = item_attributes}
;;

let ocaml_class_field ?(item_attributes = []) loc cfd =
  {pcf_desc = cfd; pcf_loc = loc; pcf_attributes = item_attributes}
;;

let ocaml_mktyp ?(alg_attributes = []) loc x =
  {ptyp_desc = x; ptyp_loc = loc; ptyp_loc_stack = [];
   ptyp_attributes = alg_attributes}
;;
let ocaml_mkpat loc x =
  {ppat_desc = x; ppat_loc = loc; ppat_loc_stack = []; ppat_attributes = []}
;;

let ocaml_attribute_implem loc (nameloc, name) sl =
  Parsetree.
  {attr_name = mkloc nameloc name; attr_payload = PStr sl; attr_loc = loc}
;;
let ocaml_attribute_interf loc (nameloc, name) si =
  Parsetree.
  {attr_name = mkloc nameloc name; attr_payload = PSig si; attr_loc = loc}
;;
let ocaml_attribute_type loc (nameloc, name) ty =
  Parsetree.
  {attr_name = mkloc nameloc name; attr_payload = PTyp ty; attr_loc = loc}
;;
let ocaml_attribute_patt loc (nameloc, name) p eopt =
  Parsetree.
  {attr_name = mkloc nameloc name; attr_payload = PPat (p, eopt);
   attr_loc = loc}
;;
let ocaml_expr_addattr attr
    {pexp_desc = pexp_desc; pexp_loc = pexp_loc;
     pexp_loc_stack = pexp_loc_stack; pexp_attributes = pexp_attributes} =
  {pexp_desc = pexp_desc; pexp_loc = pexp_loc;
   pexp_loc_stack = pexp_loc_stack;
   pexp_attributes = pexp_attributes @ [attr]}
;;
let ocaml_coretype_addattr attr
    {ptyp_desc = ptyp_desc; ptyp_loc = ptyp_loc;
     ptyp_loc_stack = ptyp_loc_stack; ptyp_attributes = ptyp_attributes} =
  {ptyp_desc = ptyp_desc; ptyp_loc = ptyp_loc;
   ptyp_loc_stack = ptyp_loc_stack;
   ptyp_attributes = ptyp_attributes @ [attr]}
;;
let ocaml_patt_addattr attr
    {ppat_desc = ppat_desc; ppat_loc = ppat_loc;
     ppat_loc_stack = ppat_loc_stack; ppat_attributes = ppat_attributes} =
  {ppat_desc = ppat_desc; ppat_loc = ppat_loc;
   ppat_loc_stack = ppat_loc_stack;
   ppat_attributes = ppat_attributes @ [attr]}
;;
let ocaml_pmty_addattr attr
    {pmty_desc = pmty_desc; pmty_loc = pmty_loc;
     pmty_attributes = pmty_attributes} =
  {pmty_desc = pmty_desc; pmty_loc = pmty_loc;
   pmty_attributes = pmty_attributes @ [attr]}
;;
let ocaml_pmod_addattr attr
    {pmod_desc = module_expr_desc; pmod_loc = pmod_loc;
     pmod_attributes = pmod_attributes} =
  {pmod_desc = module_expr_desc; pmod_loc = pmod_loc;
   pmod_attributes = pmod_attributes @ [attr]}
;;
let ocaml_pcty_addattr attr
    {pcty_desc = pcty_desc; pcty_loc = pcty_loc;
     pcty_attributes = pcty_attributes} =
  {pcty_desc = pcty_desc; pcty_loc = pcty_loc;
   pcty_attributes = pcty_attributes @ [attr]}
;;
let ocaml_pcl_addattrs attrs
    {pcl_desc = pcl_desc; pcl_loc = pcl_loc;
     pcl_attributes = pcl_attributes} =
  {pcl_desc = pcl_desc; pcl_loc = pcl_loc;
   pcl_attributes = pcl_attributes @ attrs}
;;
let ocaml_psig_attribute attr = Psig_attribute attr;;
let ocaml_pstr_attribute attr = Pstr_attribute attr;;
let ocaml_pctf_attribute attr = Pctf_attribute attr;;
let ocaml_pcf_attribute attr = Pcf_attribute attr;;
let ocaml_extension_implem (idloc, id) pay = mkloc idloc id, PStr pay;;
let ocaml_extension_interf (idloc, id) pay = mkloc idloc id, PSig pay;;
let ocaml_extension_type (idloc, id) pay = mkloc idloc id, PTyp pay;;
let ocaml_extension_patt (idloc, id) p eopt = mkloc idloc id, PPat (p, eopt);;
let ocaml_ptyp_extension e = Ptyp_extension e;;
let ocaml_pexp_extension e = Pexp_extension e;;
let ocaml_ppat_extension e = Ppat_extension e;;
let ocaml_pmty_extension e = Pmty_extension e;;
let ocaml_pmod_extension e = Pmod_extension e;;
let ocaml_psig_extension ?(item_attributes = []) e =
  Psig_extension (e, item_attributes)
;;
let ocaml_pstr_extension ?(item_attributes = []) e =
  Pstr_extension (e, item_attributes)
;;
let ocaml_pcl_extension e = Pcl_extension e;;
let ocaml_pcty_extension e = Pcty_extension e;;
let ocaml_pctf_extension e = Pctf_extension e;;
let ocaml_pcf_extension e = Pcf_extension e;;
let ocaml_extension_exception loc s ed alg_attributes =
  {pext_name = mkloc loc s; pext_kind = Pext_decl (Pcstr_tuple ed, None);
   pext_loc = loc; pext_attributes = alg_attributes}
;;
let ocaml_pexp_unreachable () = Pexp_unreachable;;
let ocaml_ptype_open () = Ptype_open;;
let ocaml_pstr_typext ext = Pstr_typext ext;;
let ocaml_psig_typext ext = Psig_typext ext;;
let ocaml_pexp_letexception exdef body = Pexp_letexception (exdef, body);;
let ocaml_ppat_exception p = Ppat_exception p;;

let ocaml_mkexp loc x =
  {pexp_desc = x; pexp_loc = loc; pexp_loc_stack = []; pexp_attributes = []}
;;
let ocaml_mkmty loc x =
  {pmty_desc = x; pmty_loc = loc; pmty_attributes = []}
;;
let ocaml_mkmod loc x =
  {pmod_desc = x; pmod_loc = loc; pmod_attributes = []}
;;

let ocaml_mkfield_inh ?(alg_attributes = []) loc x fl =
  {pof_desc = Oinherit x; pof_loc = loc; pof_attributes = alg_attributes} ::
  fl
;;

let ocaml_mkfield_tag ?(alg_attributes = []) loc (lab, x) fl =
  {pof_desc = Otag (mkloc loc lab, x); pof_loc = loc;
   pof_attributes = alg_attributes} ::
  fl
;;
let ocaml_mkfield_var loc = [];;

let convert_camlp5_variance (va, inj) =
  let va =
    match va with
      Some false -> Contravariant
    | Some true -> Covariant
    | _ -> NoVariance
  in
  let inj =
    match inj with
      true -> Injective
    | false -> NoInjectivity
  in
  va, inj
;;

let ocaml_ec_tuple ?(alg_attributes = []) loc s tyvars (x, rto) =
  assert ([] = tyvars);
  {pext_name = mkloc loc s; pext_kind = Pext_decl (Pcstr_tuple x, rto);
   pext_loc = loc; pext_attributes = alg_attributes}
;;

let ocaml_ec_record ?(alg_attributes = []) loc s (x, rto) =
  let x =
    match x with
      Ptype_record x -> Pcstr_record x
    | _ -> assert false
  in
  {pext_name = mkloc loc s; pext_kind = Pext_decl (x, rto); pext_loc = loc;
   pext_attributes = alg_attributes}
;;
let ocaml_ec_rebind loc s li =
  {pext_name = mkloc loc s; pext_kind = Pext_rebind (mkloc loc li);
   pext_loc = loc; pext_attributes = []}
;;
let ocaml_type_extension ?(item_attributes = []) loc pathlid params priv
    ecstrs =
  let params =
    List.map
      (fun (os, va) ->
         match os with
           None -> ocaml_mktyp loc Ptyp_any, convert_camlp5_variance va
         | Some s -> ocaml_mktyp loc (Ptyp_var s), convert_camlp5_variance va)
      params
  in
  {ptyext_path = mkloc loc pathlid; ptyext_params = params;
   ptyext_constructors = ecstrs; ptyext_private = priv; ptyext_loc = loc;
   ptyext_attributes = item_attributes}
;;
let ocaml_type_declaration tn params cl tk pf tm loc variance attrs =
  let _ =
    if List.length params <> List.length variance then
      failwith "internal error: ocaml_type_declaration"
  in
  let params =
    List.map2
      (fun os va ->
         match os with
           None -> ocaml_mktyp loc Ptyp_any, convert_camlp5_variance va
         | Some os ->
             ocaml_mktyp loc (Ptyp_var os), convert_camlp5_variance va)
      params variance
  in
  Right
    {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
     ptype_private = pf; ptype_manifest = tm; ptype_loc = loc;
     ptype_name = mkloc loc tn; ptype_attributes = attrs}
;;

let ocaml_class_type =
  Some (fun d loc -> {pcty_desc = d; pcty_loc = loc; pcty_attributes = []})
;;

let ocaml_class_expr =
  Some
    (fun ?(alg_attributes = []) d loc ->
       {pcl_desc = d; pcl_loc = loc; pcl_attributes = alg_attributes})
;;

let ocaml_class_structure p cil = {pcstr_self = p; pcstr_fields = cil};;

let ocaml_pmty_ident loc li = Pmty_ident (mkloc loc li);;

let ocaml_pmty_alias loc li = Pmty_alias (mkloc loc li);;

let ocaml_pmty_functor sloc mt1 mt2 =
  let mt1 =
    match mt1 with
      None -> Unit
    | Some (idopt, mt) -> Named (mknoloc idopt, mt)
  in
  Pmty_functor (mt1, mt2)
;;

let ocaml_pmty_typeof = Some (fun me -> Pmty_typeof me);;

let ocaml_pmty_with mt lcl =
  let lcl = List.map snd lcl in Pmty_with (mt, lcl)
;;

let ocaml_ptype_abstract = Ptype_abstract;;

let ocaml_ptype_record ltl priv =
  Ptype_record
    (List.map
       (fun (s, mf, ct, loc, attrs) ->
          {pld_name = mkloc loc s; pld_mutable = mf; pld_type = ct;
           pld_loc = loc; pld_attributes = attrs})
       ltl)
;;

let ocaml_ptype_variant ctl priv =
  try
    let ctl =
      List.map
        (fun (c, tl, loc, attrs) ->
           let (tl, rto) =
             match tl with
               Left (tyvars, x), rto ->
                 assert ([] = tyvars); Pcstr_tuple x, rto
             | Right (Ptype_record x), rto -> Pcstr_record x, rto
             | _ -> assert false
           in
           {pcd_name = mkloc loc c; pcd_args = tl; pcd_res = rto;
            pcd_loc = loc; pcd_attributes = attrs})
        ctl
    in
    Some (Ptype_variant ctl)
  with Exit -> None
;;

let ocaml_ptyp_arrow lab t1 t2 = Ptyp_arrow (labelled lab, t1, t2);;

let ocaml_ptyp_class li tl ll = Ptyp_class (mknoloc li, tl);;

let ocaml_ptyp_constr loc li tl = Ptyp_constr (mkloc loc li, tl);;

let ocaml_ptyp_object loc ml is_open =
  Ptyp_object (ml, (if is_open then Open else Closed))
;;

let ocaml_ptyp_package = Some (fun pt -> Ptyp_package pt);;

let ocaml_ptyp_poly =
  Some
    (fun loc cl t ->
       match cl with
         [] -> t.ptyp_desc, t.ptyp_attributes
       | _ -> Ptyp_poly (List.map (mkloc loc) cl, t), [])
;;

let ocaml_ptyp_variant loc catl clos sl_opt =
  let catl =
    List.map
      (fun c ->
         let (d, attrs) =
           match c with
             Left (c, a, tl, attrs) -> Rtag (mkloc loc c, a, tl), attrs
           | Right t -> Rinherit t, []
         in
         {prf_desc = d; prf_loc = loc; prf_attributes = attrs})
      catl
  in
  let clos = if clos then Closed else Open in
  Some (Ptyp_variant (catl, clos, sl_opt))
;;

let ocaml_package_type li ltl =
  mknoloc li, List.map (fun (li, t) -> mkloc t.ptyp_loc li, t) ltl
;;

let ocaml_pconst_char c = Pconst_char c;;
let ocaml_pconst_int i = Pconst_integer (string_of_int i, None);;
let ocaml_pconst_float s = Pconst_float (s, None);;

let ocaml_const_string s loc = Const_string (s, loc, None);;
let ocaml_pconst_string s loc so = Pconst_string (s, loc, so);;

let pconst_of_const =
  function
    Const_int i -> ocaml_pconst_int i
  | Const_char c -> ocaml_pconst_char c
  | Const_string (s, loc, so) -> ocaml_pconst_string s loc so
  | Const_float s -> ocaml_pconst_float s
  | Const_int32 i32 -> Pconst_integer (Int32.to_string i32, Some 'l')
  | Const_int64 i64 -> Pconst_integer (Int64.to_string i64, Some 'L')
  | Const_nativeint ni -> Pconst_integer (Nativeint.to_string ni, Some 'n')
;;

let ocaml_const_int32 = Some (fun s -> Const_int32 (Int32.of_string s));;

let ocaml_const_int64 = Some (fun s -> Const_int64 (Int64.of_string s));;

let ocaml_const_nativeint =
  Some (fun s -> Const_nativeint (Nativeint.of_string s))
;;

let ocaml_pexp_apply f lel =
  Pexp_apply (f, List.map (fun (l, e) -> labelled l, e) lel)
;;

let ocaml_pexp_assertfalse fname loc =
  Pexp_assert
    (ocaml_mkexp loc (Pexp_construct (mkloc loc (Lident "false"), None)))
;;

let ocaml_pexp_assert fname loc e = Pexp_assert e;;

let ocaml_pexp_constraint e ot1 ot2 =
  match ot2 with
    Some t2 -> Pexp_coerce (e, ot1, t2)
  | None ->
      match ot1 with
        Some t1 -> Pexp_constraint (e, t1)
      | None -> failwith "internal error: ocaml_pexp_constraint"
;;

let ocaml_pexp_construct loc li po chk_arity =
  Pexp_construct (mkloc loc li, po)
;;

let ocaml_pexp_construct_args =
  function
    Pexp_construct (li, po) -> Some (li.txt, li.loc, po, 0)
  | _ -> None
;;

let mkexp_ocaml_pexp_construct_arity loc li_loc li al =
  let a = ocaml_mkexp loc (Pexp_tuple al) in
  {pexp_desc = ocaml_pexp_construct li_loc li (Some a) true; pexp_loc = loc;
   pexp_loc_stack = [];
   pexp_attributes =
     [{attr_name = mkloc loc "ocaml.explicit_arity"; attr_payload = PStr [];
       attr_loc = loc}]}
;;

let ocaml_pexp_field loc e li = Pexp_field (e, mkloc loc li);;

let ocaml_pexp_for i e1 e2 df e = Pexp_for (i, e1, e2, df, e);;

let ocaml_case (p, wo, loc, e) =
  let e =
    match e with
      {pexp_desc = Pexp_unreachable; pexp_attributes = _ :: _} ->
        failwith
          "Internal error: Pexp_unreachable (parsed as '.') must not have attributes"
    | e -> e
  in
  {pc_lhs = p; pc_guard = wo; pc_rhs = e}
;;

let ocaml_pexp_function lab eo pel =
  match pel with
    [{pc_lhs = p; pc_guard = None; pc_rhs = {pexp_desc = Pexp_unreachable}}]
    when lab = "" && eo = None ->
      Pexp_function pel
  | [{pc_lhs = p; pc_guard = None; pc_rhs = e}] ->
      Pexp_fun (labelled lab, eo, p, e)
  | pel ->
      if lab = "" && eo = None then Pexp_function pel
      else failwith "internal error: bad ast in ocaml_pexp_function"
;;

let ocaml_pexp_lazy = Some (fun e -> Pexp_lazy e);;

let ocaml_pexp_ident loc li = Pexp_ident (mkloc loc li);;

let ocaml_pexp_letmodule =
  Some (fun i me e -> Pexp_letmodule (mknoloc i, me, e))
;;

let ocaml_pexp_new loc li = Pexp_new (mkloc loc li);;

let ocaml_pexp_newtype = Some (fun loc s e -> Pexp_newtype (mkloc loc s, e));;

let ocaml_pexp_object = Some (fun cs -> Pexp_object cs);;

let ocaml_pexp_open =
  Some
    (fun ovf me e ->
       Pexp_open
         ({popen_expr = me; popen_override = ovf; popen_loc = loc_none;
           popen_attributes = []},
          e))
;;

let ocaml_pexp_override sel =
  let sel = List.map (fun (s, e) -> mknoloc s, e) sel in Pexp_override sel
;;

let ocaml_pexp_pack : ('a -> 'b -> 'c, 'd) choice option =
  Some (Right ((fun me -> Pexp_pack me), (fun pt -> Ptyp_package pt)))
;;

let ocaml_pexp_poly = Some (fun e t -> Pexp_poly (e, t));;

let ocaml_pexp_record lel eo =
  let lel = List.map (fun (li, loc, e) -> mkloc loc li, e) lel in
  Pexp_record (lel, eo)
;;

let ocaml_pexp_send loc e s = Pexp_send (e, mkloc loc s);;

let ocaml_pexp_setinstvar s e = Pexp_setinstvar (mknoloc s, e);;

let ocaml_pexp_variant =
  let pexp_variant_pat =
    function
      Pexp_variant (lab, eo) -> Some (lab, eo)
    | _ -> None
  in
  let pexp_variant (lab, eo) = Pexp_variant (lab, eo) in
  Some (pexp_variant_pat, pexp_variant)
;;

let ocaml_value_binding ?(item_attributes = []) loc p e =
  let p =
    match p with
      {ppat_desc = Ppat_constraint (_, {ptyp_desc = Ptyp_poly (_, _)})} -> p
    | {ppat_desc = Ppat_constraint ({ppat_desc = Ppat_extension _}, _)} -> p
    | {ppat_desc = Ppat_constraint (p1, t)} as p0 ->
        let t =
          {ptyp_desc = Ptyp_poly ([], t); ptyp_loc = to_ghost_loc t.ptyp_loc;
           ptyp_loc_stack = []; ptyp_attributes = []}
        in
        {p0 with ppat_desc = Ppat_constraint (p1, t)}
    | p -> p
  in
  {pvb_pat = p; pvb_expr = e; pvb_loc = loc; pvb_attributes = item_attributes}
;;

let ocaml_ppat_open loc li p = Ppat_open (mkloc loc li, p);;

let ocaml_ppat_alias p i iloc = Ppat_alias (p, mkloc iloc i);;

let ocaml_ppat_array = Some (fun pl -> Ppat_array pl);;

let ocaml_ppat_construct loc li po chk_arity =
  Ppat_construct (mkloc loc li, po)
;;

let ocaml_ppat_construct_args =
  function
    Ppat_construct (li, po) -> Some (li.txt, li.loc, po, 0)
  | _ -> None
;;

let mkpat_ocaml_ppat_construct_arity loc li_loc li tyvl al =
  let a = ocaml_mkpat loc (Ppat_tuple al) in
  {ppat_desc = ocaml_ppat_construct li_loc li (Some (tyvl, a)) true;
   ppat_loc = loc; ppat_loc_stack = [];
   ppat_attributes =
     [{attr_name = mkloc loc "ocaml.explicit_arity"; attr_payload = PStr [];
       attr_loc = loc}]}
;;

let ocaml_ppat_lazy = Some (fun p -> Ppat_lazy p);;

let ocaml_ppat_record lpl is_closed =
  let lpl = List.map (fun (li, loc, p) -> mkloc loc li, p) lpl in
  Ppat_record (lpl, (if is_closed then Closed else Open))
;;

let ocaml_ppat_type = Some (fun loc li -> Ppat_type (mkloc loc li));;

let ocaml_ppat_unpack =
  Some ((fun loc s -> Ppat_unpack (mkloc loc s)), (fun pt -> Ptyp_package pt))
;;

let ocaml_ppat_var loc s = Ppat_var (mkloc loc s);;

let ocaml_ppat_variant =
  let ppat_variant_pat =
    function
      Ppat_variant (lab, po) -> Some (lab, po)
    | _ -> None
  in
  let ppat_variant (lab, po) = Ppat_variant (lab, po) in
  Some (ppat_variant_pat, ppat_variant)
;;

let ocaml_psig_class_type = Some (fun ctl -> Psig_class_type ctl);;

let ocaml_psig_exception ?(alg_attributes = []) ?(item_attributes = []) loc s
    (ed, rto) =
  let ec =
    match ed with
      Left (tyvars, x) ->
        ocaml_ec_tuple ~alg_attributes:alg_attributes loc s tyvars (x, rto)
    | Right x -> ocaml_ec_record ~alg_attributes:alg_attributes loc s (x, rto)
  in
  Psig_exception
    {ptyexn_constructor = ec; ptyexn_attributes = item_attributes;
     ptyexn_loc = loc}
;;

let ocaml_psig_include ?(item_attributes = []) loc mt =
  Psig_include
    {pincl_mod = mt; pincl_loc = loc; pincl_attributes = item_attributes}
;;

let ocaml_psig_module ?(item_attributes = []) loc (s : string option) mt =
  Psig_module
    {pmd_name = mkloc loc s; pmd_type = mt; pmd_attributes = item_attributes;
     pmd_loc = loc}
;;

let ocaml_psig_modsubst ?(item_attributes = []) loc s li =
  Psig_modsubst
    {pms_name = mkloc loc s; pms_manifest = mkloc loc li;
     pms_attributes = item_attributes;
     (* ... [@@id1] [@@id2] *)
     pms_loc = loc}
;;

let ocaml_psig_modtype ?(item_attributes = []) loc s mto =
  let pmtd =
    {pmtd_name = mkloc loc s; pmtd_type = mto;
     pmtd_attributes = item_attributes; pmtd_loc = loc}
  in
  Psig_modtype pmtd
;;

let ocaml_psig_modtypesubst ?(item_attributes = []) loc s mto =
  let pmtd =
    {pmtd_name = mkloc loc s; pmtd_type = mto;
     pmtd_attributes = item_attributes; pmtd_loc = loc}
  in
  Psig_modtypesubst pmtd
;;

let ocaml_psig_open ?(item_attributes = []) loc li =
  Psig_open
    {popen_expr = mknoloc li; popen_override = Fresh; popen_loc = loc;
     popen_attributes = item_attributes}
;;

let ocaml_psig_recmodule =
  let f ntl =
    let ntl =
      List.map
        (fun (s, mt, attrs) ->
           {pmd_name = mknoloc s; pmd_type = mt; pmd_attributes = attrs;
            pmd_loc = loc_none})
        ntl
    in
    Psig_recmodule ntl
  in
  Some f
;;

let ocaml_psig_type is_nonrec stl =
  let stl = List.map (fun (s, t) -> t) stl in
  Psig_type ((if is_nonrec then Nonrecursive else Recursive), stl)
;;

let ocaml_psig_typesubst stl =
  let stl = List.map (fun (s, t) -> t) stl in Psig_typesubst stl
;;

let ocaml_psig_value s vd = Psig_value vd;;

let ocaml_pstr_class_type = Some (fun ctl -> Pstr_class_type ctl);;

let ocaml_pstr_eval ?(item_attributes = []) e =
  Pstr_eval (e, item_attributes)
;;

let ocaml_pstr_exception ?(alg_attributes = []) ?(item_attributes = []) loc s
    (ed, rto) =
  let ec =
    match ed with
      Left (tyvars, x) ->
        ocaml_ec_tuple ~alg_attributes:alg_attributes loc s tyvars (x, rto)
    | Right x -> ocaml_ec_record ~alg_attributes:alg_attributes loc s (x, rto)
  in
  Pstr_exception
    {ptyexn_constructor = ec; ptyexn_attributes = item_attributes;
     ptyexn_loc = loc}
;;

let ocaml_pstr_exn_rebind =
  Some
    (fun loc s li ->
       Pstr_exception
         {ptyexn_constructor = ocaml_ec_rebind loc s li;
          ptyexn_attributes = []; ptyexn_loc = loc})
;;

let ocaml_pstr_include =
  Some
    (fun ?(item_attributes = []) loc me ->
       Pstr_include
         {pincl_mod = me; pincl_loc = loc;
          pincl_attributes = item_attributes})
;;

let ocaml_pstr_modtype ?(item_attributes = []) loc s mto =
  let pmtd =
    {pmtd_name = mkloc loc s; pmtd_type = mto;
     pmtd_attributes = item_attributes; pmtd_loc = loc}
  in
  Pstr_modtype pmtd
;;

let ocaml_pstr_module ?(item_attributes = []) loc (s : string option) me =
  let mb =
    {pmb_name = mkloc loc s; pmb_expr = me; pmb_attributes = item_attributes;
     pmb_loc = loc}
  in
  Pstr_module mb
;;

let ocaml_pstr_open ?(item_attributes = []) ovflag loc me =
  Pstr_open
    {popen_expr = me; popen_override = ovflag; popen_loc = loc;
     popen_attributes = item_attributes}
;;

let ocaml_pstr_primitive s vd = Pstr_primitive vd;;

let ocaml_pstr_recmodule =
  let f mel =
    Pstr_recmodule
      (List.map
         (fun ((s : string option), mt, me, attrs) ->
            {pmb_name = mknoloc s; pmb_expr = me; pmb_attributes = attrs;
             pmb_loc = loc_none})
         mel)
  in
  Some f
;;

let ocaml_pstr_type is_nonrec stl =
  let stl = List.map (fun (s, t) -> t) stl in
  Pstr_type ((if is_nonrec then Nonrecursive else Recursive), stl)
;;

let ocaml_class_infos =
  Some
    (fun ?(item_attributes = []) virt (sl, sloc) name expr loc variance ->
       let _ =
         if List.length sl <> List.length variance then
           failwith "internal error: ocaml_class_infos"
       in
       let params =
         List.map2
           (fun os va ->
              ocaml_mktyp loc (Ptyp_var os), convert_camlp5_variance va)
           sl variance
       in
       {pci_virt = virt; pci_params = params; pci_name = mkloc loc name;
        pci_expr = expr; pci_loc = loc; pci_attributes = item_attributes})
;;

let ocaml_pmod_constraint loc me mt =
  ocaml_mkmod loc (Pmod_constraint (me, mt))
;;

let ocaml_pmod_ident li = Pmod_ident (mknoloc li);;

let ocaml_pmod_functor mt me =
  let mt =
    match mt with
      None -> Unit
    | Some (idopt, mt) -> Named (mknoloc idopt, mt)
  in
  Pmod_functor (mt, me)
;;

let ocaml_pmod_unpack : ('a -> 'b -> 'c, 'd) choice option =
  Some (Right ((fun e -> Pmod_unpack e), (fun pt -> Ptyp_package pt)))
;;

let ocaml_pcf_cstr = Some (fun (t1, t2, loc) -> Pcf_constraint (t1, t2));;

let ocaml_pcf_inher loc ovflag ce pb =
  Pcf_inherit (ovflag, ce, option_map (mkloc loc) pb)
;;

let ocaml_pcf_init = Some (fun e -> Pcf_initializer e);;

let ocaml_pcf_meth (s, pf, ovf, e, loc) =
  let pf = if pf then Private else Public in
  let ovf = if ovf then Override else Fresh in
  Pcf_method (mkloc loc s, pf, Cfk_concrete (ovf, e))
;;

let ocaml_pcf_val (s, mf, ovf, e, loc) =
  let mf = if mf then Mutable else Immutable in
  let ovf = if ovf then Override else Fresh in
  Pcf_val (mkloc loc s, mf, Cfk_concrete (ovf, e))
;;

let ocaml_pcf_valvirt =
  let ocaml_pcf (s, mf, t, loc) =
    let mf = if mf then Mutable else Immutable in
    Pcf_val (mkloc loc s, mf, Cfk_virtual t)
  in
  Some ocaml_pcf
;;

let ocaml_pcf_virt (s, pf, t, loc) =
  Pcf_method (mkloc loc s, pf, Cfk_virtual t)
;;

let ocaml_pcl_apply =
  Some
    (fun ce lel -> Pcl_apply (ce, List.map (fun (l, e) -> labelled l, e) lel))
;;

let ocaml_pcl_constr = Some (fun li ctl -> Pcl_constr (mknoloc li, ctl));;

let ocaml_pcl_constraint = Some (fun ce ct -> Pcl_constraint (ce, ct));;

let ocaml_pcl_fun =
  Some (fun lab ceo p ce -> Pcl_fun (labelled lab, ceo, p, ce))
;;

let ocaml_pcl_let = Some (fun rf pel ce -> Pcl_let (rf, pel, ce));;

let ocaml_pcl_open loc li ovf ce =
  Pcl_open
    ({popen_expr = mknoloc li; popen_override = ovf; popen_loc = loc;
      popen_attributes = []},
     ce)
;;
let ocaml_pcty_open loc li ovf ct =
  Pcty_open
    ({popen_expr = mknoloc li; popen_override = ovf; popen_loc = loc;
      popen_attributes = []},
     ct)
;;

let ocaml_pcl_structure = Some (fun cs -> Pcl_structure cs);;

let ocaml_pctf_cstr = Some (fun (t1, t2, loc) -> Pctf_constraint (t1, t2));;

let ocaml_pctf_inher ct = Pctf_inherit ct;;

let ocaml_pctf_meth (s, pf, t, loc) =
  Pctf_method (mkloc loc s, pf, Concrete, t)
;;

let ocaml_pctf_val (s, mf, vf, t, loc) = Pctf_val (mkloc loc s, mf, vf, t);;

let ocaml_pctf_virt (s, pf, t, loc) =
  Pctf_method (mkloc loc s, pf, Virtual, t)
;;

let ocaml_pcty_constr = Some (fun li ltl -> Pcty_constr (mknoloc li, ltl));;

let ocaml_pcty_fun =
  Some (fun lab t ot ct -> Pcty_arrow (labelled lab, t, ct))
;;

let ocaml_pcty_signature =
  let f (t, ctfl) =
    let cs = {pcsig_self = t; pcsig_fields = ctfl} in Pcty_signature cs
  in
  Some f
;;

let ocaml_pdir_bool = Some (fun b -> Pdir_bool b);;
let ocaml_pdir_int i s = Pdir_int (i, None);;
let ocaml_pdir_some x = Some x;;
let ocaml_pdir_none = None;;
let ocaml_ptop_dir loc s da =
  Ptop_dir
    {pdir_name = mkloc loc s;
     pdir_arg =
       begin match da with
         Some da -> Some {pdira_desc = da; pdira_loc = loc}
       | None -> None
       end;
     pdir_loc = loc}
;;

  let (ocaml_pwith_modtype :
 (Location.t -> Longident.t -> module_type -> with_constraint) option) =
  Some (fun loc li mt -> Pwith_modtype (mkloc loc li, mt))
;;

let (ocaml_pwith_modtypesubst :
 (Location.t -> Longident.t -> module_type -> with_constraint) option) =
  Some (fun loc li mt -> Pwith_modtypesubst (mkloc loc li, mt))
;;

let ocaml_pwith_modsubst =
  Some (fun loc li me -> Pwith_modsubst (mkloc loc li, mkloc loc me))
;;

let ocaml_pwith_type loc (i, td) = Pwith_type (mkloc loc i, td);;

let ocaml_pwith_module loc mname me =
  Pwith_module (mkloc loc mname, mkloc loc me)
;;

let ocaml_pwith_typesubst =
  Some (fun loc lid td -> Pwith_typesubst (mkloc loc lid, td))
;;

let module_prefix_can_be_in_first_record_label_only = true;;

let split_or_patterns_with_bindings = false;;

let has_records_with_with = true;;

let arg_rest =
  function
    Arg.Rest r -> Some r
  | _ -> None
;;

let arg_set_string =
  function
    Arg.Set_string r -> Some r
  | _ -> None
;;

let arg_set_int =
  function
    Arg.Set_int r -> Some r
  | _ -> None
;;

let arg_set_float =
  function
    Arg.Set_float r -> Some r
  | _ -> None
;;

let arg_symbol =
  function
    Arg.Symbol (s, f) -> Some (s, f)
  | _ -> None
;;

let arg_tuple =
  function
    Arg.Tuple t -> Some t
  | _ -> None
;;

let arg_bool =
  function
    Arg.Bool f -> Some f
  | _ -> None
;;

let char_escaped = Char.escaped;;

let hashtbl_mem = Hashtbl.mem;;

let list_rev_append = List.rev_append;;

let list_rev_map = List.rev_map;;

let list_sort = List.sort;;

let pervasives_set_binary_mode_out = set_binary_mode_out;;

let printf_ksprintf = Printf.ksprintf;;

let char_uppercase = Char.uppercase_ascii;;

let bytes_modname = "Bytes";;

let bytes_of_string s = Bytes.of_string s;;

let bytes_to_string s = Bytes.to_string s;;

let string_capitalize = String.capitalize_ascii;;

let string_contains = String.contains;;

let string_cat s1 s2 = Bytes.cat s1 s2;;

let string_copy = Bytes.copy;;

let string_create = Bytes.create;;

let string_get = Bytes.get;;

let string_index = Bytes.index;;

let string_length = Bytes.length;;

let string_lowercase = String.lowercase_ascii;;

let string_unsafe_set = Bytes.unsafe_set;;

let string_uncapitalize = String.uncapitalize_ascii;;

let string_uppercase = String.uppercase_ascii;;

let string_set = Bytes.set;;

let string_sub = Bytes.sub;;

let array_create = Array.make;;
