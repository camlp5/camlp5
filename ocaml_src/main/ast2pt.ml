(* camlp5r *)
(* ast2pt.ml,v *)

(* #load "q_MLast.cmo" *)

open Parsetree;;
open Longident;;
open Asttypes;;
open Versdep;;

open MLast;;

let fast = ref false;;

let get_tag x =
  if Obj.is_block (Obj.repr x) then Obj.tag (Obj.repr x) else Obj.magic x
;;

let error loc str = Ploc.raise loc (Failure str);;

let char_of_char_token loc s =
  try Plexing.eval_char s with Failure _ as exn -> Ploc.raise loc exn
;;

let string_of_string_token loc s =
  try Plexing.eval_string loc s with Failure _ as exn -> Ploc.raise loc exn
;;

let glob_fname = ref "";;

let mkloc loc =
  let bp = Ploc.first_pos loc in
  let ep = Ploc.last_pos loc in
  let lnum = Ploc.line_nb loc in
  let bolp = Ploc.bol_pos loc in
  let lnuml = Ploc.line_nb_last loc in
  let bolpl = Ploc.bol_pos_last loc in
  ocaml_location (!glob_fname, lnum, bolp, lnuml, bolpl, bp, ep)
;;

let mktyp loc d = ocaml_mktyp (mkloc loc) d;;
let mkpat loc d = ocaml_mkpat (mkloc loc) d;;
let mkexp loc d = ocaml_mkexp (mkloc loc) d;;
let mkmty loc d = ocaml_mkmty (mkloc loc) d;;
let mksig loc d = {psig_desc = d; psig_loc = mkloc loc};;
let mkmod loc d = ocaml_mkmod (mkloc loc) d;;
let mkstr loc d = {pstr_desc = d; pstr_loc = mkloc loc};;
let mkfield loc d fl = ocaml_mkfield (mkloc loc) d fl;;
let mkfield_var loc = ocaml_mkfield_var (mkloc loc);;

let mkcty loc d =
  match ocaml_class_type with
    Some class_type -> class_type d (mkloc loc)
  | None -> error loc "no class type in this ocaml version"
;;
let mkpcl loc d =
  match ocaml_class_expr with
    Some class_expr -> class_expr d (mkloc loc)
  | None -> error loc "no class expr in this ocaml version"
;;
let mklazy loc e =
  match ocaml_pexp_lazy with
    Some pexp_lazy -> mkexp loc (pexp_lazy e)
  | None ->
      let ghpat = mkpat loc in
      let ghexp = mkexp loc in
      let void_pat =
        ghpat (ocaml_ppat_construct (mkloc loc) (Lident "()") None false)
      in
      let pwe = ocaml_case (void_pat, None, mkloc loc, e) in
      let f = ghexp (ocaml_pexp_function "" None [pwe]) in
      let delayed = Ldot (Lident "Lazy", "Delayed") in
      let cloc = mkloc loc in
      let df = ghexp (ocaml_pexp_construct cloc delayed (Some f) false) in
      let r =
        ghexp (ocaml_pexp_ident cloc (Ldot (Lident "Pervasives", "ref")))
      in
      ghexp (ocaml_pexp_apply r ["", df])
;;

let strip_char c s =
  match try Some (string_index s c) with Not_found -> None with
    Some _ ->
      let s = string_copy s in
      let rec loop i j =
        if i = string_length s then string_sub s 0 j
        else if string_get s i = '_' then loop (i + 1) j
        else begin string_set s j (string_get s i); loop (i + 1) (j + 1) end
      in
      loop 0 0
  | None -> s
;;

let mkintconst loc s c =
  let s = bytes_to_string (strip_char '_' (bytes_of_string s)) in
  match c with
    "" ->
      begin match (try Some (int_of_string s) with Failure _ -> None) with
        Some i -> Const_int i
      | None -> error loc "too big integer value"
      end
  | "l" ->
      begin match ocaml_const_int32 with
        Some const_int32 ->
          begin match (try Some (const_int32 s) with Failure _ -> None) with
            Some i32 -> i32
          | None -> error loc "too big 32 bits integer value"
          end
      | None -> error loc "no int32 in this ocaml version"
      end
  | "L" ->
      begin match ocaml_const_int64 with
        Some const_int64 ->
          begin match (try Some (const_int64 s) with Failure _ -> None) with
            Some i64 -> i64
          | None -> error loc "too big 64 bits integer value"
          end
      | None -> error loc "no int64 in this ocaml version"
      end
  | "n" ->
      begin match ocaml_const_nativeint with
        Some const_nativeint ->
          begin match
            (try Some (const_nativeint s) with Failure _ -> None)
          with
            Some ni -> ni
          | None -> error loc "too big native int integer value"
          end
      | None -> error loc "no native int in this ocaml version"
      end
  | _ -> error loc "special int not implemented"
;;

let conv_con =
  let t = Hashtbl.create 73 in
  List.iter (fun (s, s') -> Hashtbl.add t s s')
    ["True", "true"; "False", "false"; "True_", "True"; "False_", "False"];
  fun s -> try Hashtbl.find t s with Not_found -> s
;;

let conv_lab =
  let t = Hashtbl.create 73 in
  List.iter (fun (s, s') -> Hashtbl.add t s s') ["val", "contents"];
  fun s -> try Hashtbl.find t s with Not_found -> s
;;

let array_function str name =
  Ldot (Lident str, (if !fast then "unsafe_" ^ name else name))
;;

let uv c =
  match c, "" with
    c, "" -> c
  | _ -> invalid_arg "Ast2pt.uv"
;;

let mkrf =
  function
    true -> Recursive
  | false -> Nonrecursive
;;

let mkli s =
  let rec loop f =
    function
      i :: il -> loop (fun s -> Ldot (f i, s)) il
    | [] -> f s
  in
  loop (fun s -> Lident s)
;;

let long_id_of_string_list loc sl =
  match List.rev sl with
    [] -> error loc "bad ast"
  | s :: sl -> mkli s (List.rev sl)
;;

let long_id_class_type loc ct =
  let rec longident =
    function
      CtIde (loc, s) -> Lident (uv s)
    | CtApp (loc, ct1, ct2) ->
        let li1 = longident ct1 in
        let li2 = longident ct2 in Lapply (li1, li2)
    | CtAcc (loc, ct1, ct2) ->
        let li1 = longident ct1 in
        let li2 = longident ct2 in
        let rec loop li1 =
          function
            Lident s -> Ldot (li1, s)
          | Lapply (li21, li22) -> error loc "long_id_of_class_type bad ast"
          | Ldot (li2, s) -> Ldot (loop li1 li2, s)
        in
        loop li1 li2
    | _ -> error loc "long_id_of_class_type case not impl"
  in
  longident ct
;;

let rec ctyp_fa al =
  function
    TyApp (_, f, a) -> ctyp_fa (a :: al) f
  | f -> f, al
;;

let rec ctyp_long_id =
  function
    MLast.TyAcc (_, m, MLast.TyLid (_, s)) ->
      let (is_cls, li) = ctyp_long_id m in is_cls, Ldot (li, s)
  | MLast.TyAcc (_, m, MLast.TyUid (_, s)) ->
      let (is_cls, li) = ctyp_long_id m in is_cls, Ldot (li, s)
  | MLast.TyApp (_, m1, m2) ->
      let (is_cls, li1) = ctyp_long_id m1 in
      let (_, li2) = ctyp_long_id m2 in is_cls, Lapply (li1, li2)
  | MLast.TyUid (_, s) -> false, Lident s
  | MLast.TyLid (_, s) -> false, Lident s
  | TyCls (loc, sl) -> true, long_id_of_string_list loc (uv sl)
  | t -> error (loc_of_ctyp t) "incorrect type"
;;

let rec module_type_long_id =
  function
    MLast.MtAcc (_, m, MLast.MtUid (_, s)) -> Ldot (module_type_long_id m, s)
  | MLast.MtAcc (_, m, MLast.MtLid (_, s)) -> Ldot (module_type_long_id m, s)
  | MtApp (_, m1, m2) ->
      Lapply (module_type_long_id m1, module_type_long_id m2)
  | MLast.MtLid (_, s) -> Lident s
  | MLast.MtUid (_, s) -> Lident s
  | t -> error (loc_of_module_type t) "bad module type long ident"
;;

let rec ctyp =
  function
    TyAcc (loc, _, _) as f ->
      let (is_cls, li) = ctyp_long_id f in
      if is_cls then mktyp loc (ocaml_ptyp_class li [] [])
      else mktyp loc (ocaml_ptyp_constr (mkloc loc) li [])
  | TyAli (loc, t1, t2) ->
      let (t, i) =
        match t1, t2 with
          t, MLast.TyQuo (_, s) -> t, s
        | MLast.TyQuo (_, s), t -> t, s
        | _ -> error loc "incorrect alias type"
      in
      mktyp loc (Ptyp_alias (ctyp t, i))
  | TyAny loc -> mktyp loc Ptyp_any
  | TyApp (loc, _, _) as f ->
      let (f, al) = ctyp_fa [] f in
      let (is_cls, li) = ctyp_long_id f in
      if is_cls then mktyp loc (ocaml_ptyp_class li (List.map ctyp al) [])
      else mktyp loc (ocaml_ptyp_constr (mkloc loc) li (List.map ctyp al))
  | TyArr (loc, TyLab (loc1, lab, t1), t2) ->
      mktyp loc (ocaml_ptyp_arrow (uv lab) (ctyp t1) (ctyp t2))
  | TyArr (loc, TyOlb (loc1, lab, t1), t2) ->
      mktyp loc (ocaml_ptyp_arrow ("?" ^ uv lab) (ctyp t1) (ctyp t2))
  | TyArr (loc, t1, t2) -> mktyp loc (ocaml_ptyp_arrow "" (ctyp t1) (ctyp t2))
  | TyObj (loc, fl, v) ->
      mktyp loc
        (ocaml_ptyp_object (mkloc loc) (meth_list loc (uv fl) v) (uv v))
  | TyCls (loc, id) ->
      mktyp loc (ocaml_ptyp_class (long_id_of_string_list loc (uv id)) [] [])
  | TyLab (loc, _, _) -> error loc "labeled type not allowed here"
  | TyLid (loc, s) ->
      mktyp loc (ocaml_ptyp_constr (mkloc loc) (Lident (uv s)) [])
  | TyMan (loc, _, _, _) -> error loc "type manifest not allowed here"
  | TyOlb (loc, lab, _) -> error loc "labeled type not allowed here"
  | TyPck (loc, mt) ->
      begin match ocaml_ptyp_package with
        Some ptyp_package ->
          let pt = package_of_module_type loc mt in
          mktyp loc (ptyp_package pt)
      | None -> error loc "no package type in this ocaml version"
      end
  | TyPol (loc, pl, t) ->
      begin match ocaml_ptyp_poly with
        Some ptyp_poly -> mktyp loc (ptyp_poly (mkloc loc) (uv pl) (ctyp t))
      | None -> error loc "no poly types in that ocaml version"
      end
  | TyPot (loc, pl, t) -> error loc "'type id . t' not allowed here"
  | TyQuo (loc, s) -> mktyp loc (Ptyp_var (uv s))
  | TyRec (loc, _) -> error loc "record type not allowed here"
  | TySum (loc, _) -> error loc "sum type not allowed here"
  | TyTup (loc, tl) -> mktyp loc (Ptyp_tuple (List.map ctyp (uv tl)))
  | TyUid (loc, s) ->
      mktyp loc (ocaml_ptyp_constr (mkloc loc) (Lident (uv s)) [])
  | TyVrn (loc, catl, ool) ->
      let catl =
        List.map
          (function
             PvTag (loc, c, a, t) -> Left (uv c, uv a, List.map ctyp (uv t))
           | PvInh (loc, t) -> Right (ctyp t))
          (uv catl)
      in
      let (clos, sl) =
        match ool with
          None -> true, None
        | Some ol ->
            match ol with
              None -> false, None
            | Some sl -> true, Some (uv sl)
      in
      begin match ocaml_ptyp_variant (mkloc loc) catl clos sl with
        Some t -> mktyp loc t
      | None -> error loc "no variant type or inherit in this ocaml version"
      end
  | TyXtr (loc, _, _) -> error loc "bad ast TyXtr"
and meth_list loc fl v =
  match fl with
    [] -> if uv v then mkfield_var loc else []
  | (lab, t) :: fl -> mkfield loc (lab, add_polytype t) (meth_list loc fl v)
and add_polytype t =
  match ocaml_ptyp_poly with
    Some ptyp_poly ->
      begin match t with
        MLast.TyPol (loc, pl, t) ->
          mktyp loc (ptyp_poly (mkloc loc) (uv pl) (ctyp t))
      | _ ->
          let loc = MLast.loc_of_ctyp t in
          mktyp loc (ptyp_poly (mkloc loc) [] (ctyp t))
      end
  | None -> ctyp t
and package_of_module_type loc mt =
  let (mt, with_con) =
    match mt with
      MLast.MtWit (_, mt, with_con) ->
        let with_con =
          List.map
            (function
               WcTyp (loc, id, tpl, pf, ct) ->
                 let id_or_li =
                   match uv id with
                     [] -> error loc "bad ast"
                   | sl ->
                       match ocaml_id_or_li_of_string_list loc sl with
                         Some li -> li
                       | None -> error loc "simple identifier expected"
                 in
                 if uv tpl <> [] then
                   error loc "no type parameters allowed here";
                 if uv pf then error loc "no 'private' allowed here";
                 id_or_li, ctyp ct
             | WcTys (loc, id, tpl, t) ->
                 error loc "package type with 'type :=' no allowed"
             | WcMod (loc, _, _) ->
                 error loc "package type with 'module' no allowed"
             | WcMos (loc, _, _) ->
                 error loc "package type with 'module' no allowed")
            with_con
        in
        mt, with_con
    | _ -> mt, []
  in
  let li = module_type_long_id mt in ocaml_package_type li with_con
;;

let variance_of_var =
  function
    Some false -> false, true
  | Some true -> true, false
  | None -> false, false
;;

let mktype loc tn tl cl tk pf tm =
  let (params, var_list) = List.split tl in
  let variance = List.map variance_of_var var_list in
  let params = List.map uv params in
  match ocaml_type_declaration tn params cl tk pf tm (mkloc loc) variance with
    Right td -> td
  | Left msg -> error loc msg
;;

let mkmutable m = if m then Mutable else Immutable;;
let mkprivate m = if m then Private else Public;;

let mktrecord ltl priv =
  let ltl =
    List.map
      (fun (loc, n, m, t) ->
         let loc = mkloc loc in
         let m = mkmutable m in let t = add_polytype t in n, m, t, loc)
      ltl
  in
  ocaml_ptype_record ltl priv
;;

let option_map f =
  function
    Some x -> Some (f x)
  | None -> None
;;

let mktvariant loc ctl priv =
  let ctl =
    List.map
      (fun (loc, c, tl, rto) ->
         conv_con (uv c), List.map ctyp (uv tl), option_map ctyp rto,
         mkloc loc)
      ctl
  in
  match ocaml_ptype_variant ctl priv with
    Some x -> x
  | None -> error loc "no generalized data types in this ocaml version"
;;

let type_decl tn tl priv cl =
  function
    TyMan (loc, t, pf, MLast.TyRec (_, ltl)) ->
      let priv = if uv pf then Private else Public in
      mktype loc tn tl cl (mktrecord ltl (uv pf)) priv (Some (ctyp t))
  | TyMan (loc, t, pf, MLast.TySum (_, ctl)) ->
      let priv = if uv pf then Private else Public in
      mktype loc tn tl cl (mktvariant loc ctl (uv pf)) priv (Some (ctyp t))
  | TyRec (loc, ltl) ->
      mktype loc tn tl cl (mktrecord (uv ltl) false) priv None
  | TySum (loc, ctl) ->
      mktype loc tn tl cl (mktvariant loc (uv ctl) false) priv None
  | t ->
      let m =
        match t with
          MLast.TyQuo (_, s) ->
            if List.exists (fun (t, _) -> Some s = uv t) tl then Some (ctyp t)
            else None
        | _ -> Some (ctyp t)
      in
      mktype (loc_of_ctyp t) tn tl cl Ptype_abstract priv m
;;

let mkvalue_desc vn t p = ocaml_value_description vn (ctyp t) p;;

let option f =
  function
    Some x -> Some (f x)
  | None -> None
;;

let rec same_type_expr ct ce =
  match ct, ce with
    MLast.TyLid (_, s1), MLast.ExLid (_, s2) -> s1 = s2
  | MLast.TyUid (_, s1), MLast.ExUid (_, s2) -> s1 = s2
  | MLast.TyAcc (_, t1, t2), MLast.ExAcc (_, e1, e2) ->
      same_type_expr t1 e1 && same_type_expr t2 e2
  | _ -> false
;;

let rec module_expr_long_id =
  function
    MLast.MeApp (_, me1, me2) ->
      Lapply (module_expr_long_id me1, module_expr_long_id me2)
  | MLast.MeAcc (_, m, MLast.MeUid (_, s)) -> Ldot (module_expr_long_id m, s)
  | MLast.MeUid (_, s) -> Lident s
  | t -> error (loc_of_module_expr t) "bad module expr long ident"
;;

let type_decl_of_with_type loc tn tpl pf ct =
  let (params, var_list) = List.split (uv tpl) in
  let variance = List.map variance_of_var var_list in
  let params = List.map uv params in
  let ct = Some (ctyp ct) in
  let tk = if pf then ocaml_ptype_abstract else Ptype_abstract in
  let pf = if pf then Private else Public in
  ocaml_type_declaration tn params [] tk pf ct (mkloc loc) variance
;;

let mkwithc =
  function
    WcMod (loc, id, m) ->
      let mname = long_id_of_string_list loc (uv id) in
      mname, ocaml_pwith_module (mkloc loc) mname (module_expr_long_id m)
  | WcMos (loc, id, m) ->
      begin match ocaml_pwith_modsubst with
        Some pwith_modsubst ->
          long_id_of_string_list loc (uv id),
          pwith_modsubst (mkloc loc) (module_expr_long_id m)
      | None -> error loc "no with module := in this ocaml version"
      end
  | WcTyp (loc, id, tpl, pf, ct) ->
      begin match uv id with
        [] -> error loc "Empty list as type name is not allowed there"
      | xs ->
          (* Last element of this list is actual declaration. List begins from
             optional module path. We pass actual name to make type declaration
             and a whole list to make With_type constraint.
             See Parsetree.with_constaint type in compiler sources for more
             details *)
          let li = long_id_of_string_list loc xs in
          let tname = List.hd (List.rev xs) in
          match type_decl_of_with_type loc tname tpl (uv pf) ct with
            Right td -> li, ocaml_pwith_type (mkloc loc) (li, td)
          | Left msg -> error loc msg
      end
  | WcTys (loc, id, tpl, t) ->
      match ocaml_pwith_typesubst with
        Some pwith_typesubst ->
          begin match type_decl_of_with_type loc "" tpl false t with
            Right td ->
              let li = long_id_of_string_list loc (uv id) in
              li, pwith_typesubst (mkloc loc) td
          | Left msg -> error loc msg
          end
      | None -> error loc "no with type := in this ocaml version"
;;

let rec patt_fa al =
  function
    PaApp (_, f, a) -> patt_fa (a :: al) f
  | f -> f, al
;;

let rec mkrangepat loc c1 c2 =
  if c1 > c2 then mkrangepat loc c2 c1
  else if c1 = c2 then mkpat loc (Ppat_constant (ocaml_pconst_char c1))
  else
    mkpat loc
      (Ppat_or
         (mkpat loc (Ppat_constant (ocaml_pconst_char c1)),
          mkrangepat loc (Char.chr (Char.code c1 + 1)) c2))
;;

let rec patt_long_id il =
  function
    MLast.PaAcc (_, p, MLast.PaUid (_, i)) -> patt_long_id (i :: il) p
  | p -> p, il
;;

let rec patt_label_long_id =
  function
    MLast.PaAcc (_, m, MLast.PaLid (_, s)) ->
      Ldot (patt_label_long_id m, conv_lab s)
  | MLast.PaAcc (_, m, MLast.PaUid (_, s)) -> Ldot (patt_label_long_id m, s)
  | MLast.PaUid (_, s) -> Lident s
  | MLast.PaLid (_, s) -> Lident (conv_lab s)
  | p -> error (loc_of_patt p) "bad label"
;;

let int_of_string_l loc s = try int_of_string s with e -> Ploc.raise loc e;;

let rec patt =
  function
    PaAcc (loc, p1, p2) ->
      let p =
        match patt_long_id [] p1 with
          MLast.PaUid (loc, i), il ->
            begin match p2 with
              MLast.PaUid (_, s) ->
                ocaml_ppat_construct (mkloc loc) (mkli (conv_con s) (i :: il))
                  None (not !(Prtools.no_constructors_arity))
            | _ -> error (loc_of_patt p2) "bad access pattern"
            end
        | _ -> error (loc_of_patt p2) "bad pattern"
      in
      mkpat loc p
  | PaAli (loc, p1, p2) ->
      let (p, i, iloc) =
        match p1, p2 with
          p, MLast.PaLid (_, s) -> p, s, loc
        | MLast.PaLid (_, s), p -> p, s, loc
        | _ -> error loc "incorrect alias pattern"
      in
      mkpat loc (ocaml_ppat_alias (patt p) i (mkloc iloc))
  | PaAnt (_, p) -> patt p
  | PaAny loc -> mkpat loc Ppat_any
  | PaApp (loc, _, _) as f ->
      let (f, al) = patt_fa [] f in
      let al = List.map patt al in
      let p = (patt f).ppat_desc in
      begin match ocaml_ppat_construct_args p with
        Some (li, li_loc, None, _) ->
          if !(Prtools.no_constructors_arity) then
            let a =
              match al with
                [a] -> a
              | _ -> mkpat loc (Ppat_tuple al)
            in
            mkpat loc (ocaml_ppat_construct li_loc li (Some a) false)
          else mkpat_ocaml_ppat_construct_arity (mkloc loc) li_loc li al
      | Some _ | None ->
          match ocaml_ppat_variant with
            Some (ppat_variant_pat, ppat_variant) ->
              begin match ppat_variant_pat p with
                Some (s, None) ->
                  let a =
                    match al with
                      [a] -> a
                    | _ -> mkpat loc (Ppat_tuple al)
                  in
                  mkpat loc (ppat_variant (s, Some a))
              | Some _ | None ->
                  error (loc_of_patt f)
                    ("this is not a constructor, " ^
                     "it cannot be applied in a pattern")
              end
          | None ->
              error (loc_of_patt f)
                ("this is not a constructor, " ^
                 "it cannot be applied in a pattern")
      end
  | PaArr (loc, pl) ->
      begin match ocaml_ppat_array with
        Some ppat_array -> mkpat loc (ppat_array (List.map patt (uv pl)))
      | None -> error loc "no array patterns in this ocaml version"
      end
  | PaChr (loc, s) ->
      mkpat loc
        (Ppat_constant (ocaml_pconst_char (char_of_char_token loc (uv s))))
  | PaInt (loc, s, c) ->
      mkpat loc (Ppat_constant (pconst_of_const (mkintconst loc (uv s) c)))
  | PaFlo (loc, s) -> mkpat loc (Ppat_constant (ocaml_pconst_float (uv s)))
  | PaLab (loc, _) -> error loc "labeled pattern not allowed here"
  | PaLaz (loc, p) ->
      begin match ocaml_ppat_lazy with
        Some ppat_lazy -> mkpat loc (ppat_lazy (patt p))
      | None -> error loc "lazy patterns not in this version"
      end
  | PaLid (loc, s) -> mkpat loc (ocaml_ppat_var (mkloc loc) (uv s))
  | PaNty (loc, s) -> error loc "new type not allowed here"
  | PaOlb (loc, _, _) -> error loc "labeled pattern not allowed here"
  | PaOrp (loc, p1, p2) -> mkpat loc (Ppat_or (patt p1, patt p2))
  | PaRng (loc, p1, p2) ->
      begin match p1, p2 with
        PaChr (loc1, c1), PaChr (loc2, c2) ->
          let c1 = char_of_char_token loc1 (uv c1) in
          let c2 = char_of_char_token loc2 (uv c2) in mkrangepat loc c1 c2
      | _ -> error loc "range pattern allowed only for characters"
      end
  | PaRec (loc, lpl) ->
      let (lpl, is_closed) =
        List.fold_right
          (fun lp (lpl, is_closed) ->
             match lp with
               PaAny _, PaAny _ -> lpl, false
             | lp -> lp :: lpl, is_closed)
          (uv lpl) ([], true)
      in
      mkpat loc (ocaml_ppat_record (List.map mklabpat lpl) is_closed)
  | PaStr (loc, s) ->
      mkpat loc
        (Ppat_constant
           (ocaml_pconst_string (string_of_string_token loc (uv s)) None))
  | PaTup (loc, pl) -> mkpat loc (Ppat_tuple (List.map patt (uv pl)))
  | PaTyc (loc, p, t) -> mkpat loc (Ppat_constraint (patt p, ctyp t))
  | PaTyp (loc, sl) ->
      begin match ocaml_ppat_type with
        Some ppat_type ->
          mkpat loc
            (ppat_type (mkloc loc) (long_id_of_string_list loc (uv sl)))
      | None -> error loc "no #type in this ocaml version"
      end
  | PaUid (loc, s) ->
      let ca = not !(Prtools.no_constructors_arity) in
      mkpat loc
        (ocaml_ppat_construct (mkloc loc) (Lident (conv_con (uv s))) None ca)
  | PaUnp (loc, s, mto) ->
      begin match ocaml_ppat_unpack with
        Some (ppat_unpack, ptyp_package) ->
          let p = mkpat loc (ppat_unpack (mkloc loc) (uv s)) in
          begin match mto with
            Some mt ->
              let pt = package_of_module_type loc mt in
              mkpat loc (Ppat_constraint (p, mktyp loc (ptyp_package pt)))
          | None -> p
          end
      | None -> error loc "no unpack pattern in this ocaml version"
      end
  | PaVrn (loc, s) ->
      begin match ocaml_ppat_variant with
        Some (_, ppat_variant) -> mkpat loc (ppat_variant (uv s, None))
      | None -> error loc "no variant in this ocaml version"
      end
  | PaXtr (loc, _, _) -> error loc "bad ast PaXtr"
and mklabpat (lab, p) =
  patt_label_long_id lab, mkloc (loc_of_patt lab), patt p
;;

let rec expr_fa al =
  function
    ExApp (_, f, a) -> expr_fa (a :: al) f
  | f -> f, al
;;

let rec class_expr_fa al =
  function
    CeApp (_, ce, a) -> class_expr_fa (a :: al) ce
  | ce -> ce, al
;;

let rec sep_expr_acc l =
  function
    MLast.ExAcc (_, e1, e2) -> sep_expr_acc (sep_expr_acc l e2) e1
  | MLast.ExUid (_, s) as e ->
      let loc = MLast.loc_of_expr e in
      begin match l with
        [] -> [loc, [], e]
      | (loc2, sl, e) :: l -> (Ploc.encl loc loc2, s :: sl, e) :: l
      end
  | e -> (loc_of_expr e, [], e) :: l
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

let class_info class_expr ci =
  let (params, var_list) = List.split (uv (snd ci.ciPrm)) in
  let variance = List.map variance_of_var var_list in
  match ocaml_class_infos with
    Some class_infos ->
      begin match list_map_check uv params with
        Some params ->
          class_infos (if uv ci.ciVir then Virtual else Concrete)
            (params, mkloc (fst ci.ciPrm)) (uv ci.ciNam) (class_expr ci.ciExp)
            (mkloc ci.ciLoc) variance
      | None -> error ci.ciLoc "no '_' type parameter allowed"
      end
  | None -> error ci.ciLoc "no class_info in this ocaml version"
;;

let bigarray_get loc e el =
  match el with
    [c1] ->
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExAcc
              (loc,
               MLast.ExAcc
                 (loc, MLast.ExUid (loc, "Bigarray"),
                  MLast.ExUid (loc, "Array1")),
               MLast.ExLid (loc, "get")),
            e),
         c1)
  | [c1; c2] ->
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExApp
              (loc,
               MLast.ExAcc
                 (loc,
                  MLast.ExAcc
                    (loc, MLast.ExUid (loc, "Bigarray"),
                     MLast.ExUid (loc, "Array2")),
                  MLast.ExLid (loc, "get")),
               e),
            c1),
         c2)
  | [c1; c2; c3] ->
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExApp
              (loc,
               MLast.ExApp
                 (loc,
                  MLast.ExAcc
                    (loc,
                     MLast.ExAcc
                       (loc, MLast.ExUid (loc, "Bigarray"),
                        MLast.ExUid (loc, "Array3")),
                     MLast.ExLid (loc, "get")),
                  e),
               c1),
            c2),
         c3)
  | _ ->
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExAcc
              (loc,
               MLast.ExAcc
                 (loc, MLast.ExUid (loc, "Bigarray"),
                  MLast.ExUid (loc, "Genarray")),
               MLast.ExLid (loc, "get")),
            e),
         MLast.ExArr (loc, el))
;;

let bigarray_set loc e el v =
  match el with
    [c1] ->
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExApp
              (loc,
               MLast.ExAcc
                 (loc,
                  MLast.ExAcc
                    (loc, MLast.ExUid (loc, "Bigarray"),
                     MLast.ExUid (loc, "Array1")),
                  MLast.ExLid (loc, "set")),
               e),
            c1),
         v)
  | [c1; c2] ->
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExApp
              (loc,
               MLast.ExApp
                 (loc,
                  MLast.ExAcc
                    (loc,
                     MLast.ExAcc
                       (loc, MLast.ExUid (loc, "Bigarray"),
                        MLast.ExUid (loc, "Array2")),
                     MLast.ExLid (loc, "set")),
                  e),
               c1),
            c2),
         v)
  | [c1; c2; c3] ->
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExApp
              (loc,
               MLast.ExApp
                 (loc,
                  MLast.ExApp
                    (loc,
                     MLast.ExAcc
                       (loc,
                        MLast.ExAcc
                          (loc, MLast.ExUid (loc, "Bigarray"),
                           MLast.ExUid (loc, "Array3")),
                        MLast.ExLid (loc, "set")),
                     e),
                  c1),
               c2),
            c3),
         v)
  | _ ->
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExApp
              (loc,
               MLast.ExAcc
                 (loc,
                  MLast.ExAcc
                    (loc, MLast.ExUid (loc, "Bigarray"),
                     MLast.ExUid (loc, "Genarray")),
                  MLast.ExLid (loc, "set")),
               e),
            MLast.ExArr (loc, el)),
         v)
;;

let neg_string n =
  let len = String.length n in
  if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1) else "-" ^ n
;;

let varify_constructors var_names =
  let rec loop =
    function
      MLast.TyArr (loc, t1, t2) -> MLast.TyArr (loc, loop t1, loop t2)
    | MLast.TyApp (loc, t1, t2) -> MLast.TyApp (loc, loop t1, loop t2)
    | MLast.TyTup (loc, tl) -> MLast.TyTup (loc, List.map loop tl)
    | MLast.TyLid (loc, s) as t ->
        if List.mem s var_names then MLast.TyQuo (loc, "&" ^ s) else t
    | t -> t
  in
  loop
;;

let label_of_patt =
  function
    PaLid (_, s) -> uv s
  | PaTyc (_, PaLid (_, s), _) -> uv s
  | p -> error (MLast.loc_of_patt p) "label_of_patt; case not impl"
;;

let rec expr =
  function
    ExAcc (loc, x, MLast.ExLid (_, "val")) ->
      mkexp loc
        (ocaml_pexp_apply
           (mkexp loc (ocaml_pexp_ident (mkloc loc) (Lident "!")))
           ["", expr x])
  | ExAcc (loc, _, _) as e ->
      let (e, l) =
        match sep_expr_acc [] e with
          (loc, ml, MLast.ExUid (_, s)) :: l ->
            let ca = not !(Prtools.no_constructors_arity) in
            let cloc = mkloc loc in
            mkexp loc (ocaml_pexp_construct cloc (mkli s ml) None ca), l
        | (loc, ml, MLast.ExLid (_, s)) :: l ->
            mkexp loc (ocaml_pexp_ident (mkloc loc) (mkli s ml)), l
        | (_, [], e) :: l -> expr e, l
        | _ -> error loc "bad ast"
      in
      let (_, e) =
        List.fold_left
          (fun (loc1, e1) (loc2, ml, e2) ->
             match e2 with
               MLast.ExLid (_, s) ->
                 let loc = Ploc.encl loc1 loc2 in
                 let li = mkli (conv_lab s) ml in
                 let e = ocaml_pexp_field (mkloc loc) e1 li in
                 loc, mkexp loc e
             | _ -> error (loc_of_expr e2) "lowercase identifier expected")
          (loc, e) l
      in
      e
  | ExAnt (_, e) -> expr e
  | ExApp (loc, ExLid (_, "-"), ExInt (_, s, c)) ->
      let s = neg_string (uv s) in
      mkexp loc (Pexp_constant (pconst_of_const (mkintconst loc s c)))
  | ExApp (loc, ExLid (_, ("-" | "-.")), ExFlo (_, s)) ->
      let s = neg_string (uv s) in
      mkexp loc (Pexp_constant (ocaml_pconst_float s))
  | ExApp (loc, _, _) as f ->
      let (f, al) = expr_fa [] f in
      let f =
        match f, al with
          ExLid (loc, s), [_] ->
            let s = uv s in
            begin match s with
              "-" | "-." -> ExLid (loc, "~" ^ s)
            | _ -> f
            end
        | _ -> f
      in
      let al = List.rev (List.fold_left label_expr [] al) in
      begin match ocaml_pexp_construct_args (expr f).pexp_desc with
        Some (li, li_loc, None, _) ->
          let al = List.map snd al in
          if !(Prtools.no_constructors_arity) then
            let a =
              match al with
                [a] -> a
              | _ -> mkexp loc (Pexp_tuple al)
            in
            mkexp loc (ocaml_pexp_construct li_loc li (Some a) false)
          else mkexp_ocaml_pexp_construct_arity (mkloc loc) li_loc li al
      | Some _ | None ->
          let e = (expr f).pexp_desc in
          match ocaml_pexp_variant with
            Some (pexp_variant_pat, pexp_variant) ->
              begin match pexp_variant_pat e with
                Some (s, None) ->
                  let al = List.map snd al in
                  let a =
                    match al with
                      [a] -> a
                    | _ -> mkexp loc (Pexp_tuple al)
                  in
                  mkexp loc (pexp_variant (s, Some a))
              | Some _ | None -> mkexp loc (ocaml_pexp_apply (expr f) al)
              end
          | None -> mkexp loc (ocaml_pexp_apply (expr f) al)
      end
  | ExAre (loc, e1, e2) ->
      begin match e1 with
        MLast.ExUid (_, m) ->
          begin match ocaml_pexp_open with
            Some pexp_open ->
              let li = Lident m in mkexp loc (pexp_open li (expr e2))
          | None -> error loc "no expression open in this ocaml version"
          end
      | _ ->
          let cloc = mkloc loc in
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc
                  (ocaml_pexp_ident cloc (array_function "Array" "get")))
               ["", expr e1; "", expr e2])
      end
  | ExArr (loc, el) -> mkexp loc (Pexp_array (List.map expr (uv el)))
  | ExAss (loc, e, v) ->
      begin match e with
        ExAcc (loc, x, MLast.ExLid (_, "val")) ->
          let cloc = mkloc loc in
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc (ocaml_pexp_ident cloc (Lident ":=")))
               ["", expr x; "", expr v])
      | ExAcc (loc, _, _) ->
          begin match (expr e).pexp_desc with
            Pexp_field (e, lab) -> mkexp loc (Pexp_setfield (e, lab, expr v))
          | _ -> error loc "bad record access"
          end
      | ExAre (_, e1, e2) ->
          let cloc = mkloc loc in
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc
                  (ocaml_pexp_ident cloc (array_function "Array" "set")))
               ["", expr e1; "", expr e2; "", expr v])
      | ExBae (loc, e, el) -> expr (bigarray_set loc e (uv el) v)
      | ExLid (_, lab) -> mkexp loc (ocaml_pexp_setinstvar (uv lab) (expr v))
      | ExSte (_, e1, e2) ->
          let cloc = mkloc loc in
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc
                  (ocaml_pexp_ident cloc
                     (array_function bytes_modname "set")))
               ["", expr e1; "", expr e2; "", expr v])
      | _ -> error loc "bad left part of assignment"
      end
  | ExAsr (loc, MLast.ExUid (_, "False")) ->
      mkexp loc (ocaml_pexp_assertfalse !glob_fname (mkloc loc))
  | ExAsr (loc, e) ->
      mkexp loc (ocaml_pexp_assert !glob_fname (mkloc loc) (expr e))
  | ExBae (loc, e, el) -> expr (bigarray_get loc e (uv el))
  | ExChr (loc, s) ->
      mkexp loc
        (Pexp_constant (ocaml_pconst_char (char_of_char_token loc (uv s))))
  | ExCoe (loc, e, t1, t2) ->
      mkexp loc
        (ocaml_pexp_constraint (expr e) (option ctyp t1) (Some (ctyp t2)))
  | ExFlo (loc, s) -> mkexp loc (Pexp_constant (ocaml_pconst_float (uv s)))
  | ExFor (loc, i, e1, e2, df, el) ->
      let e3 = MLast.ExSeq (loc, uv el) in
      let df = if uv df then Upto else Downto in
      mkexp loc (ocaml_pexp_for (uv i) (expr e1) (expr e2) df (expr e3))
  | ExFun (loc, pel) ->
      begin match uv pel with
        [PaLab (ploc, lppo), w, e] ->
          begin match uv lppo with
            [p, po] ->
              let lab = label_of_patt p in
              let p =
                match uv po with
                  Some p -> p
                | None -> p
              in
              mkexp loc (ocaml_pexp_function lab None [mkpwe (p, w, e)])
          | _ -> error loc "bad AST"
          end
      | [PaNty (loc, s), w, e] ->
          begin match ocaml_pexp_newtype with
            Some newtype ->
              begin match uv w with
                Some _ -> error loc "(type ..) not allowed with 'when'"
              | None -> mkexp loc (newtype (mkloc loc) (uv s) (expr e))
              end
          | None -> error loc "(type ..) not in this ocaml version"
          end
      | [PaOlb (loc, p, eo), w, e] ->
          let lab = label_of_patt p in
          let (p, eo) =
            match uv eo with
              Some (ExOlb (_, p, eo)) -> p, eo
            | Some _ | None -> p, eo
          in
          mkexp loc
            (ocaml_pexp_function ("?" ^ lab) (option expr (uv eo))
               [mkpwe (p, w, e)])
      | pel ->
          let pel =
            if split_or_patterns_with_bindings then
              Prtools.do_split_or_patterns_with_bindings pel
            else pel
          in
          mkexp loc (ocaml_pexp_function "" None (List.map mkpwe pel))
      end
  | ExIfe (loc, e1, e2, e3) ->
      let e3o =
        match e3 with
          MLast.ExUid (_, "()") -> None
        | _ -> Some (expr e3)
      in
      mkexp loc (Pexp_ifthenelse (expr e1, expr e2, e3o))
  | ExInt (loc, s, c) ->
      mkexp loc (Pexp_constant (pconst_of_const (mkintconst loc (uv s) c)))
  | ExJdf (loc, jl, e) ->
      begin match jocaml_pexp_def with
        Some pexp_def ->
          mkexp loc (pexp_def (list_rev_map mkjoinclause (uv jl)) (expr e))
      | None -> error loc "no 'def in' in this ocaml version"
      end
  | ExLab (loc, _) -> error loc "labeled expression not allowed here 1"
  | ExLaz (loc, e) -> mklazy loc (expr e)
  | ExLet (loc, rf, pel, e) ->
      mkexp loc (Pexp_let (mkrf (uv rf), List.map mkpe (uv pel), expr e))
  | ExLid (loc, s) -> mkexp loc (ocaml_pexp_ident (mkloc loc) (Lident (uv s)))
  | ExLmd (loc, i, me, e) ->
      begin match ocaml_pexp_letmodule with
        Some pexp_letmodule ->
          mkexp loc (pexp_letmodule (uv i) (module_expr me) (expr e))
      | None -> error loc "no 'let module' in this ocaml version"
      end
  | ExLop (loc, me, e) ->
      begin match ocaml_pexp_open with
        Some pexp_open ->
          let li = module_expr_long_id me in mkexp loc (pexp_open li (expr e))
      | None -> error loc "no expression open in this ocaml version"
      end
  | ExMat (loc, e, pel) ->
      let pel = uv pel in
      let pel =
        if split_or_patterns_with_bindings then
          Prtools.do_split_or_patterns_with_bindings pel
        else pel
      in
      mkexp loc (Pexp_match (expr e, List.map mkpwe pel))
  | ExNew (loc, id) ->
      mkexp loc
        (ocaml_pexp_new (mkloc loc) (long_id_of_string_list loc (uv id)))
  | ExObj (loc, po, cfl) ->
      begin match ocaml_pexp_object with
        Some pexp_object ->
          let p =
            match uv po with
              Some p -> p
            | None -> PaAny loc
          in
          let cil = List.fold_right class_str_item (uv cfl) [] in
          mkexp loc (pexp_object (ocaml_class_structure (patt p) cil))
      | None -> error loc "no object in this ocaml version"
      end
  | ExOlb (loc, _, _) -> error loc "labeled expression not allowed here 2"
  | ExOvr (loc, iel) ->
      mkexp loc (ocaml_pexp_override (List.map mkideexp (uv iel)))
  | ExPar (loc, e1, e2) ->
      begin match jocaml_pexp_par with
        Some pexp_par -> mkexp loc (pexp_par (expr e1) (expr e2))
      | None -> error loc "no '&' in this ocaml version"
      end
  | ExPck (loc, me, mto) ->
      begin match ocaml_pexp_pack with
        Some (Left pexp_pack) ->
          begin match mto with
            Some mt ->
              let pt = package_of_module_type loc mt in
              mkexp loc (pexp_pack (module_expr me) pt)
          | None -> error loc "no such module pack in this ocaml version"
          end
      | Some (Right (pexp_pack, ptyp_package)) ->
          let e = pexp_pack (module_expr me) in
          let e =
            match mto with
              Some mt ->
                let pt = package_of_module_type loc mt in
                ocaml_pexp_constraint (mkexp loc e)
                  (Some (mktyp loc (ptyp_package pt))) None
            | None -> e
          in
          mkexp loc e
      | None -> error loc "no module pack in this ocaml version"
      end
  | ExRec (loc, lel, eo) ->
      let lel = uv lel in
      if lel = [] then error loc "empty record"
      else if eo <> None && not has_records_with_with then
        match eo with
          Some e ->
            begin match Prtools.record_without_with loc e lel with
              Some e -> expr e
            | None -> error loc "cannot convert record"
            end
        | None -> assert false
      else
        let lel =
          if module_prefix_can_be_in_first_record_label_only then lel
          else
            match lel with
              ((PaAcc (_, PaUid (_, m), _) as p), e) :: rest ->
                Prtools.expand_module_prefix (uv m) [p, e] rest
            | _ -> lel
        in
        let eo =
          match eo with
            Some e -> Some (expr e)
          | None -> None
        in
        mkexp loc (ocaml_pexp_record (List.map mklabexp lel) eo)
  | ExRpl (loc, eo, locs) ->
      let (sloc, s) = uv locs in
      begin match jocaml_pexp_reply with
        Some pexp_reply ->
          let e =
            match uv eo with
              Some e -> expr e
            | None ->
                let cloc = mkloc sloc in
                let e = ocaml_pexp_construct cloc (Lident "()") None false in
                mkexp loc e
          in
          mkexp loc (pexp_reply (mkloc loc) e (mkloc sloc, uv s))
      | None -> error loc "no 'reply' in this ocaml version"
      end
  | ExSeq (loc, el) ->
      let rec loop =
        function
          [] -> expr (MLast.ExUid (loc, "()"))
        | [e] -> expr e
        | e :: el ->
            let loc = Ploc.encl (loc_of_expr e) loc in
            mkexp loc (Pexp_sequence (expr e, loop el))
      in
      loop (uv el)
  | ExSnd (loc, e, s) ->
      mkexp loc (ocaml_pexp_send (mkloc loc) (expr e) (uv s))
  | ExSpw (loc, e) ->
      begin match jocaml_pexp_spawn with
        Some pexp_spawn -> mkexp loc (pexp_spawn (expr e))
      | None -> error loc "no 'spawn' in this ocaml version"
      end
  | ExSte (loc, e1, e2) ->
      let cloc = mkloc loc in
      mkexp loc
        (ocaml_pexp_apply
           (mkexp loc (ocaml_pexp_ident cloc (array_function "String" "get")))
           ["", expr e1; "", expr e2])
  | ExStr (loc, s) ->
      mkexp loc
        (Pexp_constant
           (ocaml_pconst_string (string_of_string_token loc (uv s)) None))
  | ExTry (loc, e, pel) ->
      mkexp loc (Pexp_try (expr e, List.map mkpwe (uv pel)))
  | ExTup (loc, el) -> mkexp loc (Pexp_tuple (List.map expr (uv el)))
  | ExTyc (loc, e, t) ->
      mkexp loc (ocaml_pexp_constraint (expr e) (Some (ctyp t)) None)
  | ExUid (loc, s) ->
      let ca = not !(Prtools.no_constructors_arity) in
      let cloc = mkloc loc in
      mkexp loc (ocaml_pexp_construct cloc (Lident (conv_con (uv s))) None ca)
  | ExVrn (loc, s) ->
      begin match ocaml_pexp_variant with
        Some (_, pexp_variant) -> mkexp loc (pexp_variant (uv s, None))
      | None -> error loc "no variants in this ocaml version"
      end
  | ExWhi (loc, e1, el) ->
      let e2 = MLast.ExSeq (loc, uv el) in
      mkexp loc (Pexp_while (expr e1, expr e2))
  | ExXtr (loc, _, _) -> error loc "bad ast ExXtr"
and label_expr rev_al =
  function
    ExLab (loc, lpeo) ->
      List.fold_left
        (fun rev_al (p, eo) ->
           match p with
             PaLid (loc, lab) ->
               let e =
                 match uv eo with
                   Some e -> e
                 | None -> ExLid (loc, lab)
               in
               (uv lab, expr e) :: rev_al
           | _ -> error loc "ExLab case not impl")
        rev_al (uv lpeo)
  | ExOlb (loc, p, eo) ->
      begin match p with
        PaLid (loc, lab) ->
          let e =
            match uv eo with
              Some e -> e
            | None -> ExLid (loc, lab)
          in
          ("?" ^ uv lab, expr e) :: rev_al
      | _ -> error loc "ExOlb case not impl"
      end
  | e -> ("", expr e) :: rev_al
and mkjoinclause jc =
  let jcval =
    list_rev_map
      (fun (loc, jpl, e) ->
         let jpl =
           list_rev_map
             (fun (locp, locs, jp) ->
                let (loc, s) = locs in
                let p =
                  match uv jp with
                    Some p -> patt p
                  | None ->
                      mkpat loc
                        (ocaml_ppat_construct (mkloc loc) (Lident "()") None
                           false)
                in
                mkloc locp, (mkloc loc, uv s), p)
             (uv jpl)
         in
         mkloc loc, (jpl, expr e))
      (uv jc.jcVal)
  in
  mkloc jc.jcLoc, jcval
and mkpe (p, e) =
  let loc = Ploc.encl (loc_of_patt p) (loc_of_expr e) in
  let (p, e) =
    match e with
      ExTyc (loc, e, (TyPol (_, _, _) as t)) -> PaTyc (loc, p, t), e
    | ExTyc (loc, e, (TyPot (_, _, _) as t)) -> PaTyc (loc, p, t), e
    | _ -> p, e
  in
  let (p, e) =
    match p with
      PaTyc (loc, p, TyPot (loc1, nt, ct)) ->
        expand_gadt_type loc p loc1 nt ct e
    | p -> p, e
  in
  ocaml_value_binding (mkloc loc) (patt p) (expr e)
and expand_gadt_type loc p loc1 nt ct e =
  let nt = uv nt in
  let e = MLast.ExTyc (loc, e, ct) in
  let e =
    List.fold_right
      (fun s e -> MLast.ExFun (loc, [MLast.PaNty (loc, s), None, e])) nt e
  in
  let ct = varify_constructors nt ct in
  let tp = List.map (fun s -> "&" ^ s) nt in
  let ct = MLast.TyPol (loc, tp, ct) in MLast.PaTyc (loc, p, ct), e
and mkpwe (p, w, e) =
  ocaml_case (patt p, option expr (uv w), mkloc (loc_of_expr e), expr e)
and mklabexp (lab, e) =
  patt_label_long_id lab, mkloc (loc_of_patt lab), expr e
and mkideexp (ide, e) = ide, expr e
and mktype_decl td =
  let priv = if uv td.tdPrv then Private else Public in
  let cl =
    List.map
      (fun (t1, t2) ->
         let loc = Ploc.encl (loc_of_ctyp t1) (loc_of_ctyp t2) in
         ctyp t1, ctyp t2, mkloc loc)
      (uv td.tdCon)
  in
  let tn = uv (snd (uv td.tdNam)) in
  tn, type_decl tn (uv td.tdPrm) priv cl td.tdDef
and module_type =
  function
    MtAcc (loc, _, _) as f ->
      mkmty loc (ocaml_pmty_ident (mkloc loc) (module_type_long_id f))
  | MtApp (loc, _, _) as f ->
      mkmty loc (ocaml_pmty_ident (mkloc loc) (module_type_long_id f))
  | MtFun (loc, n, nt, mt) ->
      mkmty loc
        (ocaml_pmty_functor (mkloc loc) (uv n) (module_type nt)
           (module_type mt))
  | MtLid (loc, s) -> mkmty loc (ocaml_pmty_ident (mkloc loc) (Lident (uv s)))
  | MtQuo (loc, _) -> error loc "abstract module type not allowed here"
  | MtSig (loc, sl) ->
      mkmty loc (Pmty_signature (List.fold_right sig_item (uv sl) []))
  | MtTyo (loc, me) ->
      begin match ocaml_pmty_typeof with
        Some pmty_typeof -> mkmty loc (pmty_typeof (module_expr me))
      | None -> error loc "no 'module type of ..' in this ocaml version"
      end
  | MtUid (loc, s) -> mkmty loc (ocaml_pmty_ident (mkloc loc) (Lident (uv s)))
  | MtWit (loc, mt, wcl) ->
      mkmty loc (ocaml_pmty_with (module_type mt) (List.map mkwithc (uv wcl)))
  | MtXtr (loc, _, _) -> error loc "bad ast MtXtr"
and sig_item s l =
  match s with
    SgCls (loc, cd) ->
      mksig loc (Psig_class (List.map (class_info class_type) (uv cd))) :: l
  | SgClt (loc, ctd) ->
      begin match ocaml_psig_class_type with
        Some psig_class_type ->
          mksig loc
            (psig_class_type (List.map (class_info class_type) (uv ctd))) ::
          l
      | None -> error loc "no class type in this ocaml version"
      end
  | SgDcl (loc, sl) -> List.fold_right sig_item (uv sl) l
  | SgDir (loc, _, _) -> l
  | SgExc (loc, n, tl) ->
      mksig loc
        (ocaml_psig_exception (mkloc loc) (uv n) (List.map ctyp (uv tl))) ::
      l
  | SgExt (loc, n, t, p) ->
      let vn = uv n in
      mksig loc (ocaml_psig_value vn (mkvalue_desc vn t (uv p))) :: l
  | SgInc (loc, mt) ->
      mksig loc (ocaml_psig_include (mkloc loc) (module_type mt)) :: l
  | SgMod (loc, rf, ntl) ->
      if not (uv rf) then
        List.fold_right
          (fun (n, mt) l ->
             mksig loc
               (ocaml_psig_module (mkloc loc) (uv n) (module_type mt)) ::
             l)
          (uv ntl) l
      else
        begin match ocaml_psig_recmodule with
          Some psig_recmodule ->
            let ntl =
              List.map (fun (n, mt) -> uv n, module_type mt) (uv ntl)
            in
            mksig loc (psig_recmodule ntl) :: l
        | None -> error loc "no recursive module in this ocaml version"
        end
  | SgMty (loc, n, mt) ->
      let mto =
        match mt with
          MtQuo (_, _) -> None
        | _ -> Some (module_type mt)
      in
      mksig loc (ocaml_psig_modtype (mkloc loc) (uv n) mto) :: l
  | SgOpn (loc, id) ->
      mksig loc
        (ocaml_psig_open (mkloc loc) (long_id_of_string_list loc (uv id))) ::
      l
  | SgTyp (loc, tdl) ->
      mksig loc (ocaml_psig_type (List.map mktype_decl (uv tdl))) :: l
  | SgUse (loc, fn, sl) ->
      Ploc.call_with glob_fname (uv fn)
        (fun () -> List.fold_right (fun (si, _) -> sig_item si) (uv sl) l) ()
  | SgVal (loc, n, t) ->
      let vn = uv n in
      mksig loc (ocaml_psig_value vn (mkvalue_desc vn t [])) :: l
  | SgXtr (loc, _, _) -> error loc "bad ast SgXtr"
and module_expr =
  function
    MeAcc (loc, _, _) as f ->
      mkmod loc (ocaml_pmod_ident (module_expr_long_id f))
  | MeApp (loc, me1, me2) ->
      mkmod loc (Pmod_apply (module_expr me1, module_expr me2))
  | MeFun (loc, n, mt, me) ->
      mkmod loc (ocaml_pmod_functor (uv n) (module_type mt) (module_expr me))
  | MeStr (loc, sl) ->
      mkmod loc (Pmod_structure (List.fold_right str_item (uv sl) []))
  | MeTyc (loc, me, mt) ->
      mkmod loc (Pmod_constraint (module_expr me, module_type mt))
  | MeUid (loc, s) -> mkmod loc (ocaml_pmod_ident (Lident (uv s)))
  | MeUnp (loc, e, mto) ->
      begin match ocaml_pmod_unpack with
        Some (Left pmod_unpack) ->
          begin match mto with
            Some mt ->
              let pt = package_of_module_type loc mt in
              mkmod loc (pmod_unpack (expr e) pt)
          | None -> error loc "no such module unpack in this ocaml version"
          end
      | Some (Right (pmod_unpack, ptyp_package)) ->
          let e =
            match mto with
              Some mt ->
                let pt = package_of_module_type loc mt in
                let t = mktyp loc (ptyp_package pt) in
                mkexp loc (ocaml_pexp_constraint (expr e) (Some t) None)
            | None -> expr e
          in
          mkmod loc (pmod_unpack e)
      | None -> error loc "no module unpack in this ocaml version"
      end
  | MeXtr (loc, _, _) -> error loc "bad ast MeXtr"
and str_item s l =
  match s with
    StCls (loc, cd) ->
      mkstr loc (Pstr_class (List.map (class_info class_expr) (uv cd))) :: l
  | StClt (loc, ctd) ->
      begin match ocaml_pstr_class_type with
        Some pstr_class_type ->
          mkstr loc
            (pstr_class_type (List.map (class_info class_type) (uv ctd))) ::
          l
      | None -> error loc "no class type in this ocaml version"
      end
  | StDcl (loc, sl) -> List.fold_right str_item (uv sl) l
  | StDef (loc, jcl) ->
      begin match jocaml_pstr_def with
        Some pstr_def ->
          let jcl = List.map mkjoinclause (uv jcl) in
          mkstr loc (pstr_def jcl) :: l
      | None -> error loc "no 'def' in this ocaml version"
      end
  | StDir (loc, _, _) -> l
  | StExc (loc, n, tl, sl) ->
      let si =
        match uv tl, uv sl with
          tl, [] -> ocaml_pstr_exception (mkloc loc) (uv n) (List.map ctyp tl)
        | [], sl ->
            begin match ocaml_pstr_exn_rebind with
              Some pstr_exn_rebind ->
                pstr_exn_rebind (mkloc loc) (uv n)
                  (long_id_of_string_list loc sl)
            | None -> error loc "no exception renaming in this ocaml version"
            end
        | _ -> error loc "renamed exception should not have parameters"
      in
      mkstr loc si :: l
  | StExp (loc, e) -> mkstr loc (ocaml_pstr_eval (expr e)) :: l
  | StExt (loc, n, t, p) ->
      let vn = uv n in
      mkstr loc (ocaml_pstr_primitive vn (mkvalue_desc vn t (uv p))) :: l
  | StInc (loc, me) ->
      begin match ocaml_pstr_include with
        Some pstr_include ->
          mkstr loc (pstr_include (mkloc loc) (module_expr me)) :: l
      | None -> error loc "no include in this ocaml version"
      end
  | StMod (loc, rf, nel) ->
      if not (uv rf) then
        List.fold_right
          (fun (n, me) l ->
             let m = ocaml_pstr_module (mkloc loc) (uv n) (module_expr me) in
             mkstr loc m :: l)
          (uv nel) l
      else
        begin match ocaml_pstr_recmodule with
          Some pstr_recmodule ->
            let nel =
              List.map
                (fun (n, me) ->
                   let (me, mt) =
                     match me with
                       MeTyc (_, me, mt) -> module_expr me, module_type mt
                     | _ ->
                         error (MLast.loc_of_module_expr me)
                           "module rec needs module types constraints"
                   in
                   uv n, mt, ocaml_pmod_constraint (mkloc loc) me mt)
                (uv nel)
            in
            mkstr loc (pstr_recmodule nel) :: l
        | None -> error loc "no recursive module in this ocaml version"
        end
  | StMty (loc, n, mt) ->
      let m = ocaml_pstr_modtype (mkloc loc) (uv n) (module_type mt) in
      mkstr loc m :: l
  | StOpn (loc, id) ->
      mkstr loc
        (ocaml_pstr_open (mkloc loc) (long_id_of_string_list loc (uv id))) ::
      l
  | StTyp (loc, flg, tdl) ->
      mkstr loc (ocaml_pstr_type (uv flg) (List.map mktype_decl (uv tdl))) ::
      l
  | StUse (loc, fn, sl) ->
      Ploc.call_with glob_fname (uv fn)
        (fun () -> List.fold_right (fun (si, _) -> str_item si) (uv sl) l) ()
  | StVal (loc, rf, pel) ->
      mkstr loc (Pstr_value (mkrf (uv rf), List.map mkpe (uv pel))) :: l
  | StXtr (loc, _, _) -> error loc "bad ast StXtr"
and class_type =
  function
    CtAcc (loc, _, _) as ct ->
      let li = long_id_class_type loc ct in
      begin match ocaml_pcty_constr with
        Some pcty_constr -> mkcty loc (pcty_constr li [])
      | None -> error loc "no class type desc in this ocaml version"
      end
  | CtApp (loc, _, _) as ct ->
      let li = long_id_class_type loc ct in
      begin match ocaml_pcty_constr with
        Some pcty_constr -> mkcty loc (pcty_constr li [])
      | None -> error loc "no class type desc in this ocaml version"
      end
  | CtIde (loc, _) as ct ->
      let li = long_id_class_type loc ct in
      begin match ocaml_pcty_constr with
        Some pcty_constr -> mkcty loc (pcty_constr li [])
      | None -> error loc "no class type desc in this ocaml version"
      end
  | CtCon (loc, ct, tl) ->
      let li = long_id_class_type loc ct in
      begin match ocaml_pcty_constr with
        Some pcty_constr -> mkcty loc (pcty_constr li (List.map ctyp (uv tl)))
      | None -> error loc "no class type desc in this ocaml version"
      end
  | CtFun (loc, TyLab (_, lab, t), ct) ->
      begin match ocaml_pcty_fun with
        Some pcty_fun ->
          let ty = ctyp t in
          mkcty loc (pcty_fun (uv lab) ty ty (class_type ct))
      | None -> error loc "no class type desc in this ocaml version"
      end
  | CtFun (loc, TyOlb (loc1, lab, t), ct) ->
      begin match ocaml_pcty_fun with
        Some pcty_fun ->
          let ty = ctyp t in
          let ot =
            let loc = loc1 in
            ctyp (MLast.TyApp (loc, MLast.TyLid (loc, "option"), t))
          in
          let pcty = pcty_fun ("?" ^ uv lab) ty ot (class_type ct) in
          mkcty loc pcty
      | None -> error loc "no class type desc in this ocaml version"
      end
  | CtFun (loc, t, ct) ->
      begin match ocaml_pcty_fun with
        Some pcty_fun ->
          let ty = ctyp t in mkcty loc (pcty_fun "" ty ty (class_type ct))
      | None -> error loc "no class type desc in this ocaml version"
      end
  | CtSig (loc, t_o, ctfl) ->
      begin match ocaml_pcty_signature with
        Some pcty_signature ->
          let t =
            match uv t_o with
              Some t -> t
            | None -> TyAny loc
          in
          let cil = List.fold_right class_sig_item (uv ctfl) [] in
          mkcty loc (pcty_signature (ctyp t, cil))
      | None -> error loc "no class type desc in this ocaml version"
      end
  | CtXtr (loc, _, _) -> error loc "bad ast CtXtr"
and class_sig_item c l =
  match c with
    CgCtr (loc, t1, t2) ->
      begin match ocaml_pctf_cstr with
        Some pctf_cstr ->
          let loc = mkloc loc in
          ocaml_class_type_field loc (pctf_cstr (ctyp t1, ctyp t2, loc)) :: l
      | None -> error loc "no class constraint in this ocaml version"
      end
  | CgDcl (loc, cl) -> List.fold_right class_sig_item (uv cl) l
  | CgInh (loc, ct) ->
      ocaml_class_type_field (mkloc loc) (ocaml_pctf_inher (class_type ct)) ::
      l
  | CgMth (loc, pf, s, t) ->
      ocaml_class_type_field (mkloc loc)
        (ocaml_pctf_meth
           (uv s, mkprivate (uv pf), add_polytype t, mkloc loc)) ::
      l
  | CgVal (loc, b, s, t) ->
      ocaml_class_type_field (mkloc loc)
        (ocaml_pctf_val (uv s, mkmutable (uv b), ctyp t, mkloc loc)) ::
      l
  | CgVir (loc, b, s, t) ->
      ocaml_class_type_field (mkloc loc)
        (ocaml_pctf_virt
           (uv s, mkprivate (uv b), add_polytype t, mkloc loc)) ::
      l
and class_expr =
  function
    CeApp (loc, _, _) as c ->
      begin match ocaml_pcl_apply with
        Some pcl_apply ->
          let (ce, el) = class_expr_fa [] c in
          let el = List.rev (List.fold_left label_expr [] el) in
          mkpcl loc (pcl_apply (class_expr ce) el)
      | None -> error loc "no class expr desc in this ocaml version"
      end
  | CeCon (loc, id, tl) ->
      begin match ocaml_pcl_constr with
        Some pcl_constr ->
          mkpcl loc
            (pcl_constr (long_id_of_string_list loc (uv id))
               (List.map ctyp (uv tl)))
      | None -> error loc "no class expr desc in this ocaml version"
      end
  | CeFun (loc, PaLab (ploc, lppo), ce) ->
      begin match ocaml_pcl_fun with
        Some pcl_fun ->
          begin match uv lppo with
            [p, po] ->
              let lab = label_of_patt p in
              let p =
                match uv po with
                  Some p -> p
                | None -> p
              in
              mkpcl loc (pcl_fun lab None (patt p) (class_expr ce))
          | [] | _ :: _ -> error ploc "case class multi lab not yet impl"
          end
      | None -> error loc "no class expr desc in this ocaml version"
      end
  | CeFun (loc, PaOlb (_, p, eo), ce) ->
      begin match ocaml_pcl_fun with
        Some pcl_fun ->
          let lab = label_of_patt p in
          let (p, eo) =
            match uv eo with
              Some (ExOlb (_, p, eo)) -> p, eo
            | Some _ | None -> p, eo
          in
          mkpcl loc
            (pcl_fun ("?" ^ lab) (option expr (uv eo)) (patt p)
               (class_expr ce))
      | None -> error loc "no class expr desc in this ocaml version"
      end
  | CeFun (loc, p, ce) ->
      begin match ocaml_pcl_fun with
        Some pcl_fun -> mkpcl loc (pcl_fun "" None (patt p) (class_expr ce))
      | None -> error loc "no class expr desc in this ocaml version"
      end
  | CeLet (loc, rf, pel, ce) ->
      begin match ocaml_pcl_let with
        Some pcl_let ->
          mkpcl loc
            (pcl_let (mkrf (uv rf)) (List.map mkpe (uv pel)) (class_expr ce))
      | None -> error loc "no class expr desc in this ocaml version"
      end
  | CeStr (loc, po, cfl) ->
      begin match ocaml_pcl_structure with
        Some pcl_structure ->
          let p =
            match uv po with
              Some p -> p
            | None -> PaAny loc
          in
          let cil = List.fold_right class_str_item (uv cfl) [] in
          mkpcl loc (pcl_structure (ocaml_class_structure (patt p) cil))
      | None -> error loc "no class expr desc in this ocaml version"
      end
  | CeTyc (loc, ce, ct) ->
      begin match ocaml_pcl_constraint with
        Some pcl_constraint ->
          mkpcl loc (pcl_constraint (class_expr ce) (class_type ct))
      | None -> error loc "no class expr desc in this ocaml version"
      end
  | CeXtr (loc, _, _) -> error loc "bad ast CeXtr"
and class_str_item c l =
  match c with
    CrCtr (loc, t1, t2) ->
      begin match ocaml_pcf_cstr with
        Some pcf_cstr ->
          let loc = mkloc loc in
          ocaml_class_field loc (pcf_cstr (ctyp t1, ctyp t2, loc)) :: l
      | None -> error loc "no constraint in this ocaml version"
      end
  | CrDcl (loc, cl) -> List.fold_right class_str_item (uv cl) l
  | CrInh (loc, ce, pb) ->
      ocaml_class_field (mkloc loc)
        (ocaml_pcf_inher (mkloc loc) (class_expr ce) (uv pb)) ::
      l
  | CrIni (loc, e) ->
      begin match ocaml_pcf_init with
        Some pcf_init ->
          ocaml_class_field (mkloc loc) (pcf_init (expr e)) :: l
      | None -> error loc "no initializer in this ocaml version"
      end
  | CrMth (loc, ovf, pf, s, ot, e) ->
      let e =
        match ocaml_pexp_poly with
          Some pexp_poly ->
            let t = option (fun t -> add_polytype t) (uv ot) in
            mkexp loc (pexp_poly (expr e) t)
        | None ->
            if uv ot = None then expr e
            else error loc "no method with label in this ocaml version"
      in
      ocaml_class_field (mkloc loc)
        (ocaml_pcf_meth (uv s, uv pf, uv ovf, e, mkloc loc)) ::
      l
  | CrVal (loc, ovf, mf, s, e) ->
      ocaml_class_field (mkloc loc)
        (ocaml_pcf_val (uv s, uv mf, uv ovf, expr e, mkloc loc)) ::
      l
  | CrVav (loc, mf, s, t) ->
      begin match ocaml_pcf_valvirt with
        Some pcf_valvirt ->
          ocaml_class_field (mkloc loc)
            (pcf_valvirt (uv s, uv mf, ctyp t, mkloc loc)) ::
          l
      | None -> error loc "no virtual value in this ocaml version"
      end
  | CrVir (loc, b, s, t) ->
      ocaml_class_field (mkloc loc)
        (ocaml_pcf_virt
           (uv s, mkprivate (uv b), add_polytype t, mkloc loc)) ::
      l
;;

let interf fname ast = glob_fname := fname; List.fold_right sig_item ast [];;

let implem fname ast = glob_fname := fname; List.fold_right str_item ast [];;

let directive loc =
  function
    MLast.ExStr (_, s) -> Pdir_string s
  | MLast.ExInt (_, i, "") -> ocaml_pdir_int i (int_of_string_l loc i)
  | MLast.ExUid (_, "True") ->
      begin match ocaml_pdir_bool with
        Some pdir_bool -> pdir_bool true
      | None -> error loc "no such kind of directive in this ocaml version"
      end
  | MLast.ExUid (_, "False") ->
      begin match ocaml_pdir_bool with
        Some pdir_bool -> pdir_bool false
      | None -> error loc "no such kind of directive in this ocaml version"
      end
  | e ->
      let sl =
        let rec loop =
          function
            MLast.ExLid (_, i) -> [i]
          | MLast.ExUid (_, i) -> [i]
          | MLast.ExAcc (_, e, MLast.ExLid (_, i)) -> loop e @ [i]
          | MLast.ExAcc (_, e, MLast.ExUid (_, i)) -> loop e @ [i]
          | e -> Ploc.raise (loc_of_expr e) (Failure "bad ast")
        in
        loop e
      in
      Pdir_ident (long_id_of_string_list loc sl)
;;

let directive_args loc d =
  match d with
    Some d -> ocaml_pdir_some (directive loc d)
  | None -> ocaml_pdir_none
;;

let phrase =
  function
    StDir (loc, d, dp) ->
      ocaml_ptop_dir (mkloc loc) (uv d) (directive_args loc (uv dp))
  | si -> glob_fname := !(Plexing.input_file); Ptop_def (str_item si [])
;;
