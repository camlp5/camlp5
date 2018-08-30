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

let ocaml_name = "ocaml";;

let sys_ocaml_version = Sys.ocaml_version;;

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
    {Lexing.pos_fname = "_none_"; Lexing.pos_lnum = 1; Lexing.pos_bol = 0;
     Lexing.pos_cnum = -1}
  in
  {Location.loc_start = loc; Location.loc_end = loc;
   Location.loc_ghost = true}
;;

let mkloc loc txt = {Location.txt = txt; Location.loc = loc};;
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

let labelled lab =
  if lab = "" then Nolabel
  else if lab.[0] = '?' then
    Optional (String.sub lab 1 (String.length lab - 1))
  else Labelled lab
;;

(* *)

let ocaml_value_description vn t p =
  {pval_type = t; pval_prim = p; pval_loc = t.ptyp_loc;
   pval_name = mkloc t.ptyp_loc vn; pval_attributes = []}
;;

let ocaml_class_type_field loc ctfd =
  {pctf_desc = ctfd; pctf_loc = loc; pctf_attributes = []}
;;

let ocaml_class_field loc cfd =
  {pcf_desc = cfd; pcf_loc = loc; pcf_attributes = []}
;;

let ocaml_mktyp loc x =
  {ptyp_desc = x; ptyp_loc = loc; ptyp_attributes = []}
;;
let ocaml_mkpat loc x =
  {ppat_desc = x; ppat_loc = loc; ppat_attributes = []}
;;
let ocaml_mkexp loc x =
  {pexp_desc = x; pexp_loc = loc; pexp_attributes = []}
;;
let ocaml_mkmty loc x =
  {pmty_desc = x; pmty_loc = loc; pmty_attributes = []}
;;
let ocaml_mkmod loc x =
  {pmod_desc = x; pmod_loc = loc; pmod_attributes = []}
;;
let ocaml_mkfield loc (lab, x) fl = (lab, x) :: fl;;
let ocaml_mkfield_var loc = [];;

let variance_of_bool_bool =
  function
    false, true -> Contravariant
  | true, false -> Covariant
  | _ -> Invariant
;;

let ocaml_type_declaration tn params cl tk pf tm loc variance =
  match list_map_check (fun s_opt -> s_opt) params with
    Some params ->
      let _ =
        if List.length params <> List.length variance then
          failwith "internal error: ocaml_type_declaration"
      in
      let params =
        List.map2
          (fun os va ->
             ocaml_mktyp loc (Ptyp_var os), variance_of_bool_bool va)
          params variance
      in
      Right
        {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
         ptype_private = pf; ptype_manifest = tm; ptype_loc = loc;
         ptype_name = mkloc loc tn; ptype_attributes = []}
  | None -> Left "no '_' type param in this ocaml version"
;;

let ocaml_class_type =
  Some (fun d loc -> {pcty_desc = d; pcty_loc = loc; pcty_attributes = []})
;;

let ocaml_class_expr =
  Some (fun d loc -> {pcl_desc = d; pcl_loc = loc; pcl_attributes = []})
;;

let ocaml_class_structure p cil = {pcstr_self = p; pcstr_fields = cil};;

let ocaml_pmty_ident loc li = Pmty_ident (mkloc loc li);;

let ocaml_pmty_functor sloc s mt1 mt2 =
  Pmty_functor (mkloc sloc s, Some mt1, mt2)
;;

let ocaml_pmty_typeof = Some (fun me -> Pmty_typeof me);;

let ocaml_pmty_with mt lcl =
  let lcl = List.map snd lcl in Pmty_with (mt, lcl)
;;

let ocaml_ptype_abstract = Ptype_abstract;;

let ocaml_ptype_record ltl priv =
  Ptype_record
    (List.map
       (fun (s, mf, ct, loc) ->
          {pld_name = mkloc loc s; pld_mutable = mf; pld_type = ct;
           pld_loc = loc; pld_attributes = []})
       ltl)
;;

let ocaml_ptype_variant ctl priv =
  try
    let ctl =
      List.map
        (fun (c, tl, rto, loc) ->
           if rto <> None then raise Exit
           else
             let tl = Pcstr_tuple tl in
             {pcd_name = mkloc loc c; pcd_args = tl; pcd_res = None;
              pcd_loc = loc; pcd_attributes = []})
        ctl
    in
    Some (Ptype_variant ctl)
  with Exit -> None
;;

let ocaml_ptyp_arrow lab t1 t2 = Ptyp_arrow (labelled lab, t1, t2);;

let ocaml_ptyp_class li tl ll = Ptyp_class (mknoloc li, tl);;

let ocaml_ptyp_constr loc li tl = Ptyp_constr (mkloc loc li, tl);;

let ocaml_ptyp_object loc ml is_open =
  let ml = List.map (fun (s, t) -> s, [], t) ml in
  Ptyp_object (ml, (if is_open then Open else Closed))
;;

let ocaml_ptyp_package = Some (fun pt -> Ptyp_package pt);;

let ocaml_ptyp_poly =
  Some
    (fun loc cl t ->
       match cl with
         [] -> t.ptyp_desc
       | _ -> Ptyp_poly (cl, t))
;;

let ocaml_ptyp_variant loc catl clos sl_opt =
  let catl =
    List.map
      (function
         Left (c, a, tl) -> Rtag (c, [], a, tl)
       | Right t -> Rinherit t)
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

let ocaml_const_string s = Const_string (s, None);;
let ocaml_pconst_string s so = Pconst_string (s, so);;

let pconst_of_const =
  function
    Const_int i -> ocaml_pconst_int i
  | Const_char c -> ocaml_pconst_char c
  | Const_string (s, so) -> ocaml_pconst_string s so
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
   pexp_attributes = [mkloc loc "ocaml.explicit_arity", PStr []]}
;;

let ocaml_pexp_field loc e li = Pexp_field (e, mkloc loc li);;

let ocaml_pexp_for i e1 e2 df e =
  Pexp_for (ocaml_mkpat loc_none (Ppat_var (mknoloc i)), e1, e2, df, e)
;;

let ocaml_case (p, wo, loc, e) = {pc_lhs = p; pc_guard = wo; pc_rhs = e};;

let ocaml_pexp_function lab eo pel =
  match pel with
    [{pc_lhs = p; pc_guard = None; pc_rhs = e}] ->
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

let ocaml_pexp_newtype = Some (fun loc s e -> Pexp_newtype (s, e));;

let ocaml_pexp_object = Some (fun cs -> Pexp_object cs);;

let ocaml_pexp_open = Some (fun li e -> Pexp_open (Fresh, mknoloc li, e));;

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

let ocaml_pexp_send loc e s = Pexp_send (e, s);;

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

let ocaml_value_binding loc p e =
  {pvb_pat = p; pvb_expr = e; pvb_loc = loc; pvb_attributes = []}
;;

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

let mkpat_ocaml_ppat_construct_arity loc li_loc li al =
  let a = ocaml_mkpat loc (Ppat_tuple al) in
  {ppat_desc = ocaml_ppat_construct li_loc li (Some a) true; ppat_loc = loc;
   ppat_attributes = [mkloc loc "ocaml.explicit_arity", PStr []]}
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

let ocaml_psig_exception loc s ed =
  Psig_exception
    {pext_name = mkloc loc s; pext_kind = Pext_decl (Pcstr_tuple ed, None);
     pext_loc = loc; pext_attributes = []}
;;

let ocaml_psig_include loc mt =
  Psig_include {pincl_mod = mt; pincl_loc = loc; pincl_attributes = []}
;;

let ocaml_psig_module loc s mt =
  Psig_module
    {pmd_name = mkloc loc s; pmd_type = mt; pmd_attributes = [];
     pmd_loc = loc}
;;

let ocaml_psig_modtype loc s mto =
  let pmtd =
    {pmtd_name = mkloc loc s; pmtd_type = mto; pmtd_attributes = [];
     pmtd_loc = loc}
  in
  Psig_modtype pmtd
;;

let ocaml_psig_open loc li =
  Psig_open
    {popen_lid = mknoloc li; popen_override = Fresh; popen_loc = loc;
     popen_attributes = []}
;;

let ocaml_psig_recmodule =
  let f ntl =
    let ntl =
      List.map
        (fun (s, mt) ->
           {pmd_name = mknoloc s; pmd_type = mt; pmd_attributes = [];
            pmd_loc = loc_none})
        ntl
    in
    Psig_recmodule ntl
  in
  Some f
;;

let ocaml_psig_type stl =
  let stl = List.map (fun (s, t) -> t) stl in Psig_type (Recursive, stl)
;;

let ocaml_psig_value s vd = Psig_value vd;;

let ocaml_pstr_class_type = Some (fun ctl -> Pstr_class_type ctl);;

let ocaml_pstr_eval e = Pstr_eval (e, []);;

let ocaml_pstr_exception loc s ed =
  Pstr_exception
    {pext_name = mkloc loc s; pext_kind = Pext_decl (Pcstr_tuple ed, None);
     pext_loc = loc; pext_attributes = []}
;;

let ocaml_pstr_exn_rebind =
  Some
    (fun loc s li ->
       Pstr_exception
         {pext_name = mkloc loc s; pext_kind = Pext_rebind (mkloc loc li);
          pext_loc = loc; pext_attributes = []})
;;

let ocaml_pstr_include =
  Some
    (fun loc me ->
       Pstr_include {pincl_mod = me; pincl_loc = loc; pincl_attributes = []})
;;

let ocaml_pstr_modtype loc s mt =
  let pmtd =
    {pmtd_name = mkloc loc s; pmtd_type = Some mt; pmtd_attributes = [];
     pmtd_loc = loc}
  in
  Pstr_modtype pmtd
;;

let ocaml_pstr_module loc s me =
  let mb =
    {pmb_name = mkloc loc s; pmb_expr = me; pmb_attributes = [];
     pmb_loc = loc}
  in
  Pstr_module mb
;;

let ocaml_pstr_open loc li =
  Pstr_open
    {popen_lid = mknoloc li; popen_override = Fresh; popen_loc = loc;
     popen_attributes = []}
;;

let ocaml_pstr_primitive s vd = Pstr_primitive vd;;

let ocaml_pstr_recmodule =
  let f nel =
    Pstr_recmodule
      (List.map
         (fun (s, mt, me) ->
            {pmb_name = mknoloc s; pmb_expr = me; pmb_attributes = [];
             pmb_loc = loc_none})
         nel)
  in
  Some f
;;

let ocaml_pstr_type is_nonrec stl =
  let stl = List.map (fun (s, t) -> t) stl in
  Pstr_type ((if is_nonrec then Nonrecursive else Recursive), stl)
;;

let ocaml_class_infos =
  Some
    (fun virt (sl, sloc) name expr loc variance ->
       let _ =
         if List.length sl <> List.length variance then
           failwith "internal error: ocaml_class_infos"
       in
       let params =
         List.map2
           (fun os va ->
              ocaml_mktyp loc (Ptyp_var os), variance_of_bool_bool va)
           sl variance
       in
       {pci_virt = virt; pci_params = params; pci_name = mkloc loc name;
        pci_expr = expr; pci_loc = loc; pci_attributes = []})
;;

let ocaml_pmod_constraint loc me mt =
  ocaml_mkmod loc (Pmod_constraint (me, mt))
;;

let ocaml_pmod_ident li = Pmod_ident (mknoloc li);;

let ocaml_pmod_functor s mt me = Pmod_functor (mknoloc s, Some mt, me);;

let ocaml_pmod_unpack : ('a -> 'b -> 'c, 'd) choice option =
  Some (Right ((fun e -> Pmod_unpack e), (fun pt -> Ptyp_package pt)))
;;

let ocaml_pcf_cstr = Some (fun (t1, t2, loc) -> Pcf_constraint (t1, t2));;

let ocaml_pcf_inher loc ce pb = Pcf_inherit (Fresh, ce, pb);;

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

let ocaml_pcl_structure = Some (fun cs -> Pcl_structure cs);;

let ocaml_pctf_cstr = Some (fun (t1, t2, loc) -> Pctf_constraint (t1, t2));;

let ocaml_pctf_inher ct = Pctf_inherit ct;;

let ocaml_pctf_meth (s, pf, t, loc) = Pctf_method (s, pf, Concrete, t);;

let ocaml_pctf_val (s, mf, t, loc) = Pctf_val (s, mf, Concrete, t);;

let ocaml_pctf_virt (s, pf, t, loc) = Pctf_method (s, pf, Virtual, t);;

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
let ocaml_pdir_some x = x;;
let ocaml_pdir_none = Pdir_none;;
let ocaml_ptop_dir loc s da = Ptop_dir (s, da);;

let ocaml_pwith_modsubst =
  Some (fun loc me -> Pwith_modsubst (mkloc loc "", mkloc loc me))
;;

let ocaml_pwith_type loc (i, td) = Pwith_type (mkloc loc i, td);;

let ocaml_pwith_module loc mname me =
  Pwith_module (mkloc loc mname, mkloc loc me)
;;

let ocaml_pwith_typesubst = Some (fun loc td -> Pwith_typesubst td);;

let module_prefix_can_be_in_first_record_label_only = true;;

let split_or_patterns_with_bindings = false;;

let has_records_with_with = true;;

(* *)

let jocaml_pstr_def : (_ -> _) option = None;;

let jocaml_pexp_def : (_ -> _ -> _) option = None;;

let jocaml_pexp_par : (_ -> _ -> _) option = None;;

let jocaml_pexp_reply : (_ -> _ -> _ -> _) option = None;;

let jocaml_pexp_spawn : (_ -> _) option = None;;

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
