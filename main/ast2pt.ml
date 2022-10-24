(* camlp5r *)
(* ast2pt.ml,v *)

#load "q_MLast.cmo";

open Parsetree;
open Longident;
open Asttypes;
open Asttools;
open Versdep;

open MLast;

value fast = ref False;

value get_tag x =
  if Obj.is_block (Obj.repr x) then Obj.tag (Obj.repr x) else Obj.magic x
;

value error loc str = Ploc.raise loc (Failure str);

value char_of_char_token loc s =
  try Plexing.eval_char s with [ Failure _ as exn → Ploc.raise loc exn ]
;

value string_of_string_token loc s =
  try Plexing.eval_string loc s with [ Failure _ as exn → Ploc.raise loc exn ]
;

value glob_fname = ref "";

value mkloc loc =
  let bp = Ploc.first_pos loc in
  let ep = Ploc.last_pos loc in
  let lnum = Ploc.line_nb loc in
  let bolp = Ploc.bol_pos loc in
  let lnuml = Ploc.line_nb_last loc in
  let bolpl = Ploc.bol_pos_last loc in
  ocaml_location (glob_fname.val, lnum, bolp, lnuml, bolpl, bp, ep)
;

value mktyp ?{alg_attributes=[]} loc d = ocaml_mktyp ~{alg_attributes=alg_attributes} (mkloc loc) d;
value mkpat loc d = ocaml_mkpat (mkloc loc) d;
value mkexp loc d = ocaml_mkexp (mkloc loc) d;
value mkmty loc d = ocaml_mkmty (mkloc loc) d;
value mksig loc d = {psig_desc = d; psig_loc = mkloc loc};
value mkmod loc d = ocaml_mkmod (mkloc loc) d;
value mkstr loc d = {pstr_desc = d; pstr_loc = mkloc loc};
value mkfield_tag ~{alg_attributes=alg_attributes} loc d fl = ocaml_mkfield_tag ~{alg_attributes=alg_attributes} (mkloc loc) d fl;
value mkfield_inh ~{alg_attributes=alg_attributes} loc d fl = ocaml_mkfield_inh ~{alg_attributes=alg_attributes} (mkloc loc) d fl;
value mkfield_var loc = ocaml_mkfield_var (mkloc loc);

value mkcty loc d =
  match ocaml_class_type with
  [ Some class_type → class_type d (mkloc loc)
  | None → error loc "no class type in this ocaml version" ]
;
value mkpcl loc d =
  match ocaml_class_expr with
  [ Some class_expr → class_expr d (mkloc loc)
  | None → error loc "no class expr in this ocaml version" ]
;
value mklazy loc e =
  match ocaml_pexp_lazy with
  [ Some pexp_lazy → mkexp loc (pexp_lazy e)
  | None →
      let ghpat = mkpat loc in
      let ghexp = mkexp loc in
      let void_pat =
        ghpat (ocaml_ppat_construct (mkloc loc) (Lident "()") None False)
      in
      let pwe = ocaml_case (void_pat, None, mkloc loc, e) in
      let f = ghexp (ocaml_pexp_function "" None [pwe]) in
      let delayed = Ldot (Lident "Lazy") "Delayed" in
      let cloc = mkloc loc in
      let df = ghexp (ocaml_pexp_construct cloc delayed (Some f) False) in
      let r =
        ghexp (ocaml_pexp_ident cloc (Ldot (Lident "Pervasives") "ref"))
      in
      ghexp (ocaml_pexp_apply r [("", df)]) ]
;

value strip_char c s =
  match try Some (string_index s c) with [ Not_found → None ] with
  [ Some _ →
      let s = string_copy s in
      loop 0 0 where rec loop i j =
        if i = string_length s then string_sub s 0 j
        else if string_get s i = '_' then loop (i + 1) j
        else do { string_set s j (string_get s i); loop (i + 1) (j + 1) }
  | None → s ]
;

value mkintconst loc s c =
  let s = bytes_to_string (strip_char '_' (bytes_of_string s)) in
  match c with
  [ "" →
      match try Some (int_of_string s) with [ Failure _ → None ] with
      [ Some i → Const_int i
      | None → error loc "too big integer value" ]
  | "l" →
      match ocaml_const_int32 with
      [ Some const_int32 →
          match try Some (const_int32 s) with [ Failure _ → None ] with
          [ Some i32 → i32
          | None → error loc "too big 32 bits integer value" ]
      | None → error loc "no int32 in this ocaml version" ]
  | "L" →
      match ocaml_const_int64 with
      [ Some const_int64 →
          match try Some (const_int64 s) with [ Failure _ → None ] with
          [ Some i64 → i64
          | None → error loc "too big 64 bits integer value" ]
      | None → error loc "no int64 in this ocaml version" ]
  | "n" →
      match ocaml_const_nativeint with
      [ Some const_nativeint →
          match try Some (const_nativeint s) with [ Failure _ → None ] with
          [ Some ni → ni
          | None → error loc "too big native int integer value" ]
      | None → error loc "no native int in this ocaml version" ]
  | _ → error loc "special int not implemented" ]
;

value conv_con = do {
  let t = Hashtbl.create 73 in
  List.iter (fun (s, s') → Hashtbl.add t s s')
    [("True", "true"); ("False", "false"); ("True_", "True");
     ("False_", "False")];
  fun s → try Hashtbl.find t s with [ Not_found → s ]
};

value conv_lab = do {
  let t = Hashtbl.create 73 in
  List.iter (fun (s, s') → Hashtbl.add t s s') [("val", "contents")];
  fun s → try Hashtbl.find t s with [ Not_found → s ]
};

value array_function str name =
  Ldot (Lident str) (if fast.val then "unsafe_" ^ name else name)
;

value uv c =
  match (c, "") with
  [ (<:vala< c >>, "") → c
  | _ → invalid_arg "Ast2pt.uv" ]
;

value mkrf =
  fun
  [ True → Recursive
  | False → Nonrecursive ]
;

value uident_True__True = fun [
  "True_" -> "True"
| "False_" -> "False"
| x -> x
]
;

value mkli s =
  loop (fun s → Lident s) where rec loop f =
    fun
    [ [i :: il] → loop (fun s → Ldot (f i) s) il
    | [] → f s ]
;

value long_id_of_string_list loc sl =
  match List.rev sl with
  [ [] → error loc "bad ast"
  | [s :: sl] → mkli s (List.rev sl) ]
;

value concat_long_ids l1 l2 =
let rec crec lhs = fun [
  Lident s -> Ldot lhs s
| Ldot li s -> Ldot (crec lhs li) s
| Lapply lif liarg -> Lapply (crec lhs lif) liarg
] in
crec l1 l2
;

value longid_long_id_gen ~{extended} =
  let rec lrec = fun
  [ <:extended_longident< $longid:me1$ ( $longid:me2$ ) >> when extended ->
      Lapply (lrec me1) (lrec me2)
  | <:extended_longident:< $longid:_$ ( $longid:_$ ) >>  ->
      Ploc.raise loc (Failure "longid_long_id: extended longid forbidden here (application not allowed)")
  | <:extended_longident< $longid:me1$ . $_uid:uid$ >> → Ldot (lrec me1) (uident_True__True (uv uid))
  | <:extended_longident< $_uid:s$ >> → Lident (uident_True__True(uv s))
  | LiXtr loc _ _ -> Ploc.raise loc (Failure "longid_long_id: LiXtr forbidden here")
  ]
  in lrec
;
value longid_long_id = longid_long_id_gen ~{extended=False} ;
value extended_longid_long_id = longid_long_id_gen ~{extended=True} ;

value rec ctyp_fa al =
  fun
  [ TyApp _ f a → ctyp_fa [a :: al] f
  | f → (f, al) ]
;

value rec module_expr_long_id =
  fun
  [ <:module_expr< $me1$ ( $me2$ ) >> →
      Lapply (module_expr_long_id me1) (module_expr_long_id me2)
  | <:module_expr< $m$ . $uid:s$ >> → Ldot (module_expr_long_id m) s
  | <:module_expr< $uid:s$ >> → Lident s
  | t → error (loc_of_module_expr t) "bad module expr long ident" ]
;

value rec expr_long_id = fun
  [ <:expr< $longid:li$ >> -> longid_long_id li
  | _ -> failwith "expr_long_id: unexpected expr"
  ]
;

value longid_lident_long_id_gen ~{extended} (lio,s) = match (lio, s) with [
    (Some li, s) → Ldot (longid_long_id_gen ~{extended=extended} (uv li)) (uv s)
  | (None, s) → Lident (uv s)
]
;
value longid_lident_long_id = longid_lident_long_id_gen ~{extended=False} ;
value extended_longid_lident_long_id = longid_lident_long_id_gen ~{extended=True} ;

value rec ctyp_long_id =
  fun
  [
    <:ctyp< $m1$ $m2$ >> →
      let (is_cls, li1) = ctyp_long_id m1 in
      let (_, li2) = ctyp_long_id m2 in
      (is_cls, Lapply li1 li2)
  | <:ctyp:< $longid:m$ . $lid:id$ >> →
      let li1 = extended_longid_long_id m in
      let (is_cls, li2) = ctyp_long_id <:ctyp< $lid:id$ >> in
      (is_cls, concat_long_ids li1 li2)
  | <:ctyp< $lid:s$ >> → (False, Lident s)
  | TyCls loc cli → (True, extended_longid_lident_long_id (uv cli))
  | t → error (loc_of_ctyp t) "incorrect type" ]
;

value module_type_long_id = fun [
  <:module_type< $longid:li$ . $_lid:lid$ >> -> Ldot (extended_longid_long_id li) (uv lid)
| <:module_type< $longid:li$ >> -> extended_longid_long_id li
| _ -> failwith "module_type_long_id"
]
;

value class_type_long_id = fun [
  <:class_type< $longid:li$ . $_lid:lid$ >> ->
    Ldot (extended_longid_long_id li) (uv lid)
| <:class_type< $_lid:lid$ >> ->
    Lident (uv lid)
| _ -> failwith "class_type_long_id"
]
;

value mktype ~{item_attributes} loc tn tl cl tk pf tm =
  let (params, variance) = List.split tl in
  let params = List.map uv params in
  match ocaml_type_declaration tn params cl tk pf tm (mkloc loc) variance item_attributes with
  [ Right td → td
  | Left msg → error loc msg ]
;

value mkoverride m = if m then Override else Fresh;
value mkmutable m = if m then Mutable else Immutable;
value mkvirtual m = if m then Virtual else Concrete;
value mkprivate m = if m then Private else Public;

value option_map f =
  fun
  [ Some x → Some (f x)
  | None → None ]
;

value rec patt_fa al =
  fun
  [ PaApp _ f a → patt_fa [a :: al] f
  | f → (f, al) ]
;

value exception_to_constructor_pattern =
  let rec erec =
  fun
  [ PaApp loc f a → PaApp loc (erec f) a
  | PaExc loc ename -> ename
  | _ -> assert False ]
in erec
;

value rec mkrangepat loc c1 c2 =
  if c1 > c2 then mkrangepat loc c2 c1
  else if c1 = c2 then mkpat loc (Ppat_constant (ocaml_pconst_char c1))
  else
    mkpat loc
      (Ppat_or (mkpat loc (Ppat_constant (ocaml_pconst_char c1)))
         (mkrangepat loc (Char.chr (Char.code c1 + 1)) c2))
;

value rec patt_label_long_id =
  fun
  [ <:patt< $longid:li$ . $lid:s$ >> → Ldot (longid_long_id li) (conv_lab s)
  | <:patt< $longid:li$ . $uid:s$ >> → longid_long_id li
  | <:patt< $lid:s$ >> → Lident (conv_lab s)
  | p → error (loc_of_patt p) "bad label" ]
;

value int_of_string_l loc s = try int_of_string s with e → Ploc.raise loc e;

value rec expr_fa al =
  fun
  [ ExApp _ f a → expr_fa [a :: al] f
  | f → (f, al) ]
;

value rec class_expr_fa al =
  fun
  [ CeApp _ ce a → class_expr_fa [a :: al] ce
  | ce → (ce, al) ]
;

value list_map_check f l =
  loop [] l where rec loop rev_l =
    fun
    [ [x :: l] →
        match f x with
        [ Some s → loop [s :: rev_l] l
        | None → None ]
    | [] → Some (List.rev rev_l) ]
;

value class_info item_attributes_fun class_expr ci =
  let (params, variance) = List.split (uv (snd ci.ciPrm)) in
  match ocaml_class_infos with
  [ Some class_infos →
      match list_map_check uv params with
      [ Some params →
          class_infos
            ~{item_attributes=item_attributes_fun ci.ciAttributes}
            (if uv ci.ciVir then Virtual else Concrete)
            (params, mkloc (fst ci.ciPrm)) (uv ci.ciNam) (class_expr ci.ciExp)
            (mkloc ci.ciLoc) variance
      | None → error ci.ciLoc "no '_' type parameter allowed" ]
  | None → error ci.ciLoc "no class_info in this ocaml version" ]
;

value bigarray_get loc e el =
  match el with
  [ [c1] → <:expr< Bigarray.Array1.get $e$ $c1$ >>
  | [c1; c2] → <:expr< Bigarray.Array2.get $e$ $c1$ $c2$ >>
  | [c1; c2; c3] → <:expr< Bigarray.Array3.get $e$ $c1$ $c2$ $c3$ >>
  | _ → <:expr< Bigarray.Genarray.get $e$ [| $list:el$ |] >> ]
;

value bigarray_set loc e el v =
  match el with
  [ [c1] → <:expr< Bigarray.Array1.set $e$ $c1$ $v$ >>
  | [c1; c2] → <:expr< Bigarray.Array2.set $e$ $c1$ $c2$ $v$ >>
  | [c1; c2; c3] → <:expr< Bigarray.Array3.set $e$ $c1$ $c2$ $c3$ $v$ >>
  | _ → <:expr< Bigarray.Genarray.set $e$ [| $list:el$ |] $v$ >> ]
;

value neg_string n =
  let len = String.length n in
  if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1) else "-" ^ n
;

value varify_constructors var_names =
  loop where rec loop =
    fun
    [ <:ctyp:< $t1$ → $t2$ >> → <:ctyp< $loop t1$ → $loop t2$ >>
    | <:ctyp:< $t1$ $t2$ >> → <:ctyp:< $loop t1$ $loop t2$ >>
    | <:ctyp:< ($list:tl$) >> → <:ctyp:< ($list:List.map loop tl$) >>
    | <:ctyp:< $lid:s$ >> as t →
        if List.mem s var_names then <:ctyp< '$"&"^s$ >> else t
    | t → t ]
;

value label_of_patt =
  fun
  [ PaLid _ s → uv s
  | PaTyc _ (PaLid _ s) _ → uv s
  | p → error (MLast.loc_of_patt p) "label_of_patt; case not impl" ]
;

value ctyp_mentions s cty =
  let rec crec = fun [
    <:ctyp< '$s2$ >> ->  s = s2
  | <:ctyp< $t1$ $t2$ >> ->  crec t1 || crec t2
  | <:ctyp< $t1$ -> $t2$ >> ->  crec t1 || crec t2
  | <:ctyp< ($list:tl$) >> -> List.exists crec tl
  | _ -> False
  ] in
  crec cty
;

value rec type_decl_of_with_type loc tn tpl pf ct =
  let (params, variance) = List.split (uv tpl) in
  let params = List.map uv params in
  let ct = Some (ctyp ct) in
  let tk = if pf then ocaml_ptype_abstract else Ptype_abstract in
  let pf = if pf then Private else Public in
  ocaml_type_declaration tn params [] tk pf ct (mkloc loc) variance []

and mkwithc =
  fun
  [ WcMod loc id m →
      let mname = longid_long_id (uv id) in
      (mname, ocaml_pwith_module (mkloc loc) mname (module_expr_long_id m))
  | WcMos loc id m →
      match ocaml_pwith_modsubst with
      [ Some pwith_modsubst →
          let li = longid_long_id (uv id) in
          (li,
           pwith_modsubst (mkloc loc) li (module_expr_long_id m))
      | None → error loc "no with module := in this ocaml version" ]
  | WcMty loc id mty ->
      match ocaml_pwith_modtype with [
        Some pwith_modtype ->
      let mname = longid_long_id (uv id) in
      (mname, pwith_modtype (mkloc loc) mname (module_type mty))
      | None -> error loc "no with module := in this ocaml version"
        ]
  | WcMts loc id mty ->
      match ocaml_pwith_modtypesubst with [
        Some pwith_modtypesubst ->
          let li = longid_long_id (uv id) in
          (li, pwith_modtypesubst (mkloc loc) li (module_type mty))
      | None -> error loc "no with module type := in this ocaml version"
        ]
  | WcTyp loc id tpl pf ct →
          let li = longid_lident_long_id (uv id) in
          let (_, tname) = (uv id) in
          match type_decl_of_with_type loc (uv tname) tpl (uv pf) ct with
          | Right td -> (li, ocaml_pwith_type (mkloc loc) (li, td))
          | Left msg → error loc msg
          end
  | WcTys loc ids tpl t →
      match ocaml_pwith_typesubst with
      [ Some pwith_typesubst →
          let ids = uv ids in
          let (_,last) = ids in
          match type_decl_of_with_type loc (uv last) tpl False t with
          [ Right td →
              let li = longid_lident_long_id ids in
              (li, pwith_typesubst (mkloc loc) li td)
          | Left msg →
              error loc msg ]
      | None → error loc "no with type := in this ocaml version" ] ]

and mkvalue_desc ~{item_attributes} vn (tyvars, t) p =
  let t = match tyvars with [ [] -> t | l ->
    let loc = loc_of_ctyp t in
    TyPol loc <:vala< l >> t ] in
 ocaml_value_description ~{item_attributes=item_attributes} vn (ctyp t) p

and sumbranch_ctyp ?{priv=False} loc tyvars l rto =
    let rto = option_map ctyp rto in
    match l with [
      [TyRec loc ltl] -> do {
        assert ([] = tyvars) ;
        (Right (mktrecord (uv ltl) priv), rto)
      }
    | [TyRec _ _ :: _] -> error loc "only ONE record type allowed here"
    | l -> (Left (tyvars, List.map ctyp l), rto)
    ]

and conv_constructor priv (loc, c, tyvars, tl, rto, alg_attrs) =
    (conv_con (uv c), sumbranch_ctyp ~{priv=priv} loc (uv tyvars) (uv tl) (uv rto),
     mkloc loc, uv_alg_attributes alg_attrs)

and mktvariant loc ctl priv =
  let ctl =
    List.map (conv_constructor priv) ctl
  in
  match ocaml_ptype_variant ctl priv with
  [ Some x → x
  | None → error loc "no generalized data types in this ocaml version" ]
and mktrecord ltl priv =
  let ltl =
    List.map
      (fun (loc, n, m, t, attrs) →
         let loc = mkloc loc in
         let m = mkmutable m in
         let t = add_polytype t in
         let attrs = uv_alg_attributes attrs in
         (n, m, t, loc, attrs))
      ltl
  in
  ocaml_ptype_record ltl priv

and ctyp =
  fun
  [ TyAtt loc ct a ->
    ocaml_coretype_addattr (attr (uv a)) (ctyp ct)
  | TyAcc loc _ _ as f →
      let (is_cls, li) = ctyp_long_id f in
      if is_cls then mktyp loc (ocaml_ptyp_class li [] [])
      else mktyp loc (ocaml_ptyp_constr (mkloc loc) li [])

  | TyAli loc t1 t2 →
      let (t, i) =
        match (t1, t2) with
        [ (t, <:ctyp< '$s$ >>) → (t, s)
        | (<:ctyp< '$s$ >>, t) → (t, s)
        | _ → error loc "incorrect alias type" ]
      in
      mktyp loc (Ptyp_alias (ctyp t) i)
  | TyAny loc → mktyp loc Ptyp_any
  | TyApp loc _ _ as f →
      let (f, al) = ctyp_fa [] f in
      let (is_cls, li) = ctyp_long_id f in
      if is_cls then mktyp loc (ocaml_ptyp_class li (List.map ctyp al) [])
      else mktyp loc (ocaml_ptyp_constr (mkloc loc) li (List.map ctyp al))
  | TyArr loc (TyLab loc1 lab t1) t2 →
      mktyp loc (ocaml_ptyp_arrow (uv lab) (ctyp t1) (ctyp t2))
  | TyArr loc (TyOlb loc1 lab t1) t2 →
      mktyp loc (ocaml_ptyp_arrow ("?" ^ uv lab) (ctyp t1) (ctyp t2))
  | TyArr loc t1 t2 → mktyp loc (ocaml_ptyp_arrow "" (ctyp t1) (ctyp t2))
  | TyObj loc fl v →
      mktyp loc
        (ocaml_ptyp_object (mkloc loc) (meth_list loc (uv fl) v) (uv v))
  | TyCls loc cli →
      mktyp loc (ocaml_ptyp_class (extended_longid_lident_long_id (uv cli)) [] [])
  | TyLab loc _ _ → error loc "labeled type not allowed here"
  | TyLid loc s → mktyp loc (ocaml_ptyp_constr (mkloc loc) (Lident (uv s)) [])
  | TyMan loc _ _ _ → error loc "type manifest not allowed here"
  | TyOlb loc lab _ → error loc "labeled type not allowed here"
  | TyOpn loc ->  error loc "open (parsed as '..') type not allowed here"
  | TyPck loc mt →
      match ocaml_ptyp_package with
      [ Some ptyp_package →
          let (mt, attrs) = module_type_unwrap_attrs mt in
          let pt = package_of_module_type loc mt in
          mktyp ~{alg_attributes=conv_attributes attrs} loc (ptyp_package pt)
      | None → error loc "no package type in this ocaml version" ]
  | TyPol loc pl t →
      match ocaml_ptyp_poly with
      [ Some ptyp_poly →
        let (ct, attrs) = ptyp_poly (mkloc loc) (uv pl) (ctyp t)
        in mktyp ~{alg_attributes=attrs} loc ct
      | None → error loc "no poly types in that ocaml version" ]
  | TyPot loc pl t → error loc "'type id . t' not allowed here"
  | TyQuo loc s → mktyp loc (Ptyp_var (uv s))
  | TyRec loc _ → error loc "record type not allowed here"
  | TySum loc _ → error loc "sum type not allowed here"
  | TyTup loc tl → mktyp loc (Ptyp_tuple (List.map ctyp (uv tl)))
  | TyVrn loc catl ool →
      let catl =
        List.map
          (fun
           [ PvTag loc c a t alg_attrs → Left (uv c, uv a, List.map ctyp (uv t), uv_alg_attributes alg_attrs)
           | PvInh loc t → Right (ctyp t) ])
          (uv catl)
      in
      let (clos, sl) =
        match ool with
        [ None → (True, None)
        | Some ol →
            match ol with
            [ None → (False, None)
            | Some sl → (True, Some (uv sl)) ] ]
      in
      match ocaml_ptyp_variant (mkloc loc) catl clos sl with
      [ Some t → mktyp loc t
      | None → error loc "no variant type or inherit in this ocaml version" ]
  | TyXtr loc _ _ → error loc "bad ast TyXtr"
  | TyExten loc ebody -> mktyp loc (ocaml_ptyp_extension (extension (uv ebody)))
  ]
and meth_list loc fl v =
  match fl with
  [ [] → if uv v then mkfield_var loc else []
  | [(Some lab, t, attrs) :: fl] →
          mkfield_tag ~{alg_attributes=uv_alg_attributes attrs} loc (lab, add_polytype t) (meth_list loc fl v)
  | [(None, t, attrs) :: fl] →
          mkfield_inh ~{alg_attributes=uv_alg_attributes attrs} loc (add_polytype t) (meth_list loc fl v)
  ]
    
and add_polytype t =
  match ocaml_ptyp_poly with
  [ Some ptyp_poly →
      match t with
      [ MLast.TyPol loc pl t →
          let (ct, attrs) = ptyp_poly (mkloc loc) (uv pl) (ctyp t) in
          mktyp ~{alg_attributes=attrs} loc ct
      | _ →
          let loc = MLast.loc_of_ctyp t in
          let (ct, attrs) = ptyp_poly (mkloc loc) [] (ctyp t) in
          mktyp ~{alg_attributes=attrs} loc ct ]
  | None → ctyp t ]
and package_of_module_type loc mt =
  let (mt, with_con) =
    match mt with
    [ <:module_type< $mt$ with $list:with_con$ >> →
        let with_con =
          List.map
            (fun
             [ WcTyp loc id tpl pf ct → do {
                 let id_or_li = longid_lident_long_id (uv id)
                 in
                 if uv tpl <> [] then
                   error loc "no type parameters allowed here"
                 else ();
                 if uv pf then error loc "no 'private' allowed here" else ();
                 (id_or_li, ctyp ct)
               }
             | WcTys loc id tpl t →
                 error loc "package type with 'type :=' no allowed"
             | WcMod loc _ _ | WcMos loc _ _ →
                 error loc "package type with 'module' no allowed" 
             | WcMty loc _ _ | WcMts loc _ _ →
                 error loc "package type with 'module type' no allowed" ])
            with_con
        in
        (mt, with_con)
    | _ → (mt, []) ]
  in
  let li = module_type_long_id mt in
  ocaml_package_type li with_con

and type_decl ?{item_attributes=[]} tn tl priv (cl,tdCon) =
  fun
  [ TyMan loc t pf <:ctyp< { $list:ltl$ } >> →
      let priv = if uv pf then Private else Public in
      mktype ~{item_attributes=item_attributes} loc tn tl cl (mktrecord ltl (uv pf)) priv (Some (ctyp t))
  | TyMan loc t pf <:ctyp< [ $list:ctl$ ] >> →
      let priv = if uv pf then Private else Public in
      mktype ~{item_attributes=item_attributes} loc tn tl cl (mktvariant loc ctl (uv pf)) priv (Some (ctyp t))

  | TyMan loc t pf <:ctyp< .. >> →
      let priv = if uv pf then Private else Public in
      mktype ~{item_attributes=item_attributes} loc tn tl cl (ocaml_ptype_open ()) priv (Some (ctyp t))

  | TyRec loc ltl →
      mktype ~{item_attributes=item_attributes} loc tn tl cl (mktrecord (uv ltl) False) priv None
  | TySum loc ctl →
      mktype ~{item_attributes=item_attributes} loc tn tl cl (mktvariant loc (uv ctl) False) priv None
  | TyOpn loc ->
      mktype ~{item_attributes=item_attributes} loc tn tl cl (ocaml_ptype_open ()) priv None
  | t →
      let m =
        match t with
        [ <:ctyp< '$s$ >> when not (List.exists (fun [ (t1, t2) -> ctyp_mentions s t1 || ctyp_mentions s t2 ]) tdCon) →
            if List.exists (fun (t, _) → Some s = uv t) tl then Some (ctyp t)
            else None
        | _ → Some (ctyp t) ]
      in
      mktype ~{item_attributes=item_attributes} (loc_of_ctyp t) tn tl cl Ptype_abstract priv m ]
and extension_constructor ec = match ec with [
      EcTuple loc gc ->
      let (n, tl, _, alg_attrs) = conv_constructor False gc in
      match tl with [
        (Left (tyvars, x),y) -> 
          ocaml_ec_tuple ~{alg_attributes=alg_attrs} (mkloc loc) n tyvars (x,y)
      | (Right x, y) -> do {
          ocaml_ec_record ~{alg_attributes=alg_attrs} (mkloc loc) n (x,y)
        }
      ]
    | EcRebind loc n li alg_attrs ->
      ocaml_ec_rebind (mkloc loc) (uv n) (longid_long_id (uv li))
    ]
and type_extension loc te =
  let pf = uv te.tePrv in
  let ecstrs = List.map extension_constructor (uv te.teECs) in
  ocaml_type_extension ~{item_attributes=uv_item_attributes te.teAttributes} (mkloc loc)
    (longid_lident_long_id (uv te.teNam))
    (List.map (fun (p,v) -> (uv p, v)) (uv te.tePrm))
    (if pf then Private else Public)
    ecstrs
and patt =
  fun
  [ PaAtt loc p1 a ->
    ocaml_patt_addattr (attr (uv a)) (patt p1)
  | PaPfx loc li p2 ->
    mkpat loc (ocaml_ppat_open (mkloc loc) (longid_long_id li) (patt p2))
  | PaLong loc li _ ->
    let li = match li with [
      <:longident:< $uid:s$ >> -> <:longident< $uid:conv_con s$ >>
    | <:longident:< $longid:li$ . $uid:s$ >> -> <:longident< $longid:li$ . $uid:conv_con s$ >>
    | _ -> failwith "Lapply not allowed here"
    ] in
    let li = longid_long_id li in
    mkpat loc (ocaml_ppat_construct (mkloc loc) li
                 None (not Prtools.no_constructors_arity.val))

  | PaAli loc p1 p2 →
      let (p, i, iloc) =
        match (p1, p2) with
        [ (p, <:patt< $lid:s$ >>) → (p, s, loc)
        | (<:patt< $lid:s$ >>, p) → (p, s, loc)
        | _ → error loc "incorrect alias pattern" ]
      in
      mkpat loc (ocaml_ppat_alias (patt p) i (mkloc iloc))
  | PaAnt _ p → patt p
  | PaAny loc → mkpat loc Ppat_any
  | PaExc loc p ->
      let p = patt p in
      mkpat loc (ocaml_ppat_exception p)

  | PaApp loc _ _ as f0 →
      let (f, al) = patt_fa [] f0 in
      match f with [
        PaExc loc ename ->
          let p = patt (exception_to_constructor_pattern f0) in
          mkpat loc (ocaml_ppat_exception p)
      | _ -> 
      let al = List.map patt al in
      let p = (patt f).ppat_desc in
      match ocaml_ppat_construct_args p with
      [ Some (li, li_loc, None, _) →
          if Prtools.no_constructors_arity.val then
            let a =
              match al with
              [ [a] -> a
              | _ -> mkpat loc (Ppat_tuple al) ]
            in
            mkpat loc (ocaml_ppat_construct li_loc li (Some ([],a)) False)
          else mkpat_ocaml_ppat_construct_arity (mkloc loc) li_loc li [] al
      | Some _ | None →
          match ocaml_ppat_variant with
          [ Some (ppat_variant_pat, ppat_variant) →
              match ppat_variant_pat p with
              [ Some (s, None) →
                  let a =
                    match al with
                    [ [a] → a
                    | _ → mkpat loc (Ppat_tuple al) ]
                  in
                  mkpat loc (ppat_variant (s, Some a))
              | Some _ | None →
                  error (loc_of_patt f)
                    ("this is not a constructor, " ^
                     "it cannot be applied in a pattern") ]
          | None →
              error (loc_of_patt f)
                ("this is not a constructor, " ^
                 "it cannot be applied in a pattern") ] ]
      ]
  | PaArr loc pl →
      match ocaml_ppat_array with
      [ Some ppat_array → mkpat loc (ppat_array (List.map patt (uv pl)))
      | None → error loc "no array patterns in this ocaml version" ]
  | PaChr loc s →
      mkpat loc
        (Ppat_constant (ocaml_pconst_char (char_of_char_token loc (uv s))))
  | PaInt loc s c →
      mkpat loc (Ppat_constant (pconst_of_const (mkintconst loc (uv s) c)))
  | PaFlo loc s → mkpat loc (Ppat_constant (ocaml_pconst_float (uv s)))
  | PaLab loc _ → error loc "labeled pattern not allowed here"
  | PaLaz loc p →
      match ocaml_ppat_lazy with
      [ Some ppat_lazy → mkpat loc (ppat_lazy (patt p))
      | None → error loc "lazy patterns not in this version" ]
  | PaLid loc s → mkpat loc (ocaml_ppat_var (mkloc loc) (uv s))
  | PaNty loc s → error loc "new type not allowed here"
  | PaOlb loc _ _ → error loc "labeled pattern not allowed here"
  | PaOrp loc p1 p2 → mkpat loc (Ppat_or (patt p1) (patt p2))
  | PaRng loc p1 p2 →
      match (p1, p2) with
      [ (PaChr loc1 c1, PaChr loc2 c2) →
          let c1 = char_of_char_token loc1 (uv c1) in
          let c2 = char_of_char_token loc2 (uv c2) in
          mkrangepat loc c1 c2
      | _ → error loc "range pattern allowed only for characters" ]
  | PaRec loc lpl →
      let (lpl, is_closed) =
        List.fold_right
          (fun lp (lpl, is_closed) →
             match lp with
             [ (PaAny _, PaAny _) → (lpl, False)
             | lp → ([lp :: lpl], is_closed) ])
          (uv lpl) ([], True)
      in
      mkpat loc (ocaml_ppat_record (List.map mklabpat lpl) is_closed)
  | PaStr loc s →
      mkpat loc
        (Ppat_constant
           (ocaml_pconst_string (string_of_string_token loc (uv s)) (mkloc loc) None))
  | PaTup loc pl → mkpat loc (Ppat_tuple (List.map patt (uv pl)))
  | PaTyc loc p t → mkpat loc (Ppat_constraint (patt p) (ctyp t))
  | PaTyp loc lili →
      match ocaml_ppat_type with
      [ Some ppat_type →
          mkpat loc
            (ppat_type (mkloc loc) (extended_longid_lident_long_id (uv lili)))
      | None → error loc "no #type in this ocaml version" ]
  | PaUnp loc s mto →
      match ocaml_ppat_unpack with
      [ Some (ppat_unpack, ptyp_package) →
          let p = mkpat loc (ppat_unpack (mkloc loc) (option_map uv (uv s))) in
          match mto with
          [ Some mt →
              let (mt, alg_attrs) = module_type_unwrap_attrs mt in
              let pt = package_of_module_type loc mt in
              mkpat loc (Ppat_constraint p (mktyp ~{alg_attributes=conv_attributes alg_attrs} loc (ptyp_package pt)))
          | None → p ]
      | None → error loc "no unpack pattern in this ocaml version" ]
  | PaVrn loc s →
      match ocaml_ppat_variant with
      [ Some (_, ppat_variant) → mkpat loc (ppat_variant (uv s, None))
      | None → error loc "no variant in this ocaml version" ]
  | PaXtr loc _ _ → error loc "bad ast PaXtr"
  | PaExten loc ebody -> mkpat loc (ocaml_ppat_extension (extension (uv ebody)))
  ]
and mklabpat (lab, p) =
  (patt_label_long_id lab, mkloc (loc_of_patt lab), patt p)

and expr =
  fun
  [ 
    ExAtt loc e a ->
    ocaml_expr_addattr (attr (uv a)) (expr e)
  | ExLong loc li ->
    let ca = not Prtools.no_constructors_arity.val in
    let li = match li with [
      <:longident:< $uid:s$ >> -> <:longident< $uid:conv_con s$ >>
    | <:longident:< $longid:li$ . $uid:s$ >> -> <:longident< $longid:li$ . $uid:conv_con s$ >>
    | _ -> failwith "Lapply not allowed here"
    ] in
    let li = longid_long_id li in
    let cloc = mkloc loc in
    mkexp loc (ocaml_pexp_construct cloc li None ca)

  | ExOpen loc li <:expr< $lid:id$ >> ->
    let vid = <:vala< id >> in
    expr (ExFle loc (ExLong loc li) <:vala< (None, vid) >>)

  | ExOpen loc li e ->
    let li = longid_long_id li in
    let me = mkmod loc (ocaml_pmod_ident li) in
    match ocaml_pexp_open with [
        Some pexp_open ->
        mkexp loc (pexp_open (mkoverride False) me (expr e))
      | None -> error loc "no expression open in this ocaml version"
    ]

  | ExFle loc e <:vala< (None, s) >> when uv s = "val" ->
      mkexp loc
        (ocaml_pexp_apply
           (mkexp loc (ocaml_pexp_ident (mkloc loc) (Lident "!")))
           [("", expr e)])

  | ExFle loc (ExLong _ li) <:vala< (None, s) >> ->
    let li = longid_lident_long_id (Some <:vala< li >>, s) in
    mkexp loc (ocaml_pexp_ident (mkloc loc) li)

  | ExFle loc (ExLong _ li) <:vala< (Some _, _) >> ->
    error loc "<longid>.<longid> not valid syntax (nor parseable)"

  | ExFle loc e <:vala< (Some _, s) >> when uv s = "val" ->
    error loc "().<lident>.val not valid syntax"

  | ExFle loc e lili ->
    let li = longid_lident_long_id (uv lili) in
    mkexp loc (ocaml_pexp_field (mkloc loc) (expr e) li)

  | ExAnt _ e → expr e
  | ExApp loc (ExLid _ <:vala< "-" >>) (ExInt _ s c) →
      let s = neg_string (uv s) in
      mkexp loc (Pexp_constant (pconst_of_const (mkintconst loc s c)))
  | ExApp loc (ExLid _ <:vala< "-" | "-." >>) (ExFlo _ s) →
      let s = neg_string (uv s) in
      mkexp loc (Pexp_constant (ocaml_pconst_float s))
  | ExApp loc _ _ as f →
      let (f, al) = expr_fa [] f in
      let f =
        match (f, al) with
        [ (ExLid loc s, [_]) →
            let s = uv s in
            match s with
            [ "-" | "-." → ExLid loc <:vala< "~" ^ s >>
            | _ → f ]
        | _ → f ]
      in
      let al = List.rev (List.fold_left label_expr [] al) in
      match ocaml_pexp_construct_args (expr f).pexp_desc with
      [ Some (li, li_loc, None, _) →
          let al = List.map snd al in
          if Prtools.no_constructors_arity.val then
            let a =
              match al with
              [ [a] -> a
              | _ -> mkexp loc (Pexp_tuple al) ]
            in
            mkexp loc (ocaml_pexp_construct li_loc li (Some a) False)
          else
            mkexp_ocaml_pexp_construct_arity (mkloc loc) li_loc li al
      | Some _ | None →
          let e = (expr f).pexp_desc in
          match ocaml_pexp_variant with
          [ Some (pexp_variant_pat, pexp_variant) →
              match pexp_variant_pat e with
              [ Some (s, None) →
                  let al = List.map snd al in
                  let a =
                    match al with
                    [ [a] → a
                    | _ → mkexp loc (Pexp_tuple al) ]
                  in
                  mkexp loc (pexp_variant (s, Some a))
              | Some _ | None →
                  mkexp loc (ocaml_pexp_apply (expr f) al) ]
          | None → mkexp loc (ocaml_pexp_apply (expr f) al) ] ]
  | ExAre loc dotop e1 e2l →
      match (uv dotop, uv e2l) with [
        (".", [e2]) ->
          let cloc = mkloc loc in
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc
                  (ocaml_pexp_ident cloc (array_function "Array" "get")))
               [("", expr e1); ("", expr e2)])
      | (".", e2l) -> assert False
      | (dotop, [e2]) -> 
        let dotop = dotop ^ "()" in
        expr <:expr< $lid:dotop$ $e1$ $e2$ >>
      | (dotop, e2l) ->
         let dotop = dotop ^ "(;..)" in
         let aexp = <:expr< [| $list:e2l$ |] >> in
         expr <:expr< $lid:dotop$ $e1$ $aexp$ >>
      ]
  | ExArr loc el → mkexp loc (Pexp_array (List.map expr (uv el)))
  | ExAss loc e v →
      match e with
      [ ExFle loc x <:vala< (None, vval) >> when uv vval = "val" ->
          let cloc = mkloc loc in
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc (ocaml_pexp_ident cloc (Lident ":=")))
               [("", expr x); ("", expr v)])

      | ExFle loc _ _ ->
          match (expr e).pexp_desc with
          [ Pexp_field e lab → mkexp loc (Pexp_setfield e lab (expr v))
          | _ → error loc "bad record access" ]

      | ExAre _ dotop e1 e2l →
          match (uv dotop, uv e2l) with [
            (".", [e2]) ->
              let cloc = mkloc loc in
              mkexp loc
                (ocaml_pexp_apply
                   (mkexp loc
                      (ocaml_pexp_ident cloc (array_function "Array" "set")))
                   [("", expr e1); ("", expr e2); ("", expr v)])
          | (".", e2l) -> assert False
          | (dotop, [e2]) ->
            let dotop = dotop ^ "()<-" in
            expr <:expr< $lid:dotop$ $e1$ $e2$ $v$ >>
          | (dotop, e2l) ->
            let dotop = dotop ^ "(;..)<-" in
            let aexp = <:expr< [| $list:e2l$ |] >> in
            expr <:expr< $lid:dotop$ $e1$ $aexp$ $v$ >>
          ]
      | ExBae loc dotop e1 el →
          match (uv dotop, uv el) with [
            (".", el) -> expr (bigarray_set loc e1 el v)
          | (dotop, [e2]) ->
            let dotop = dotop ^ "{}<-" in
            expr <:expr< $lid:dotop$ $e1$ $e2$ $v$ >>
          | (dotop, e2l) ->
            let dotop = dotop ^ "{;..}<-" in
            let aexp = <:expr< [| $list:e2l$ |] >> in
            expr <:expr< $lid:dotop$ $e1$ $aexp$ $v$ >>
          ]
      | ExLid _ lab → mkexp loc (ocaml_pexp_setinstvar (uv lab) (expr v))
      | ExSte _ dotop e1 e2l →
          match (uv dotop, uv e2l) with [
            (".", [e2]) ->
              let cloc = mkloc loc in
              mkexp loc
                (ocaml_pexp_apply
                   (mkexp loc
                      (ocaml_pexp_ident cloc
                         (array_function bytes_modname "set")))
                   [("", expr e1); ("", expr e2); ("", expr v)])
          | (".", e2l) -> assert False
          | (dotop, [e2]) ->
            let dotop = dotop ^ "[]<-" in
            expr <:expr< $lid:dotop$ $e1$ $e2$ $v$ >>
          | (dotop, e2l) ->
            let dotop = dotop ^ "[;..]<-" in
            let aexp = <:expr< [| $list:e2l$ |] >> in
            expr <:expr< $lid:dotop$ $e1$ $aexp$ $v$ >>
          ]

      | _ → error loc "bad left part of assignment"
      ]
  | ExAsr loc <:expr< False >> →
      mkexp loc (ocaml_pexp_assertfalse glob_fname.val (mkloc loc))
  | ExAsr loc e →
      mkexp loc (ocaml_pexp_assert glob_fname.val (mkloc loc) (expr e))
  | ExBae loc dotop e1 el →
      match (uv dotop, uv el) with [
        (".", el) -> expr (bigarray_get loc e1 el)
      | (dotop, [e2]) ->
        let dotop = dotop ^ "{}" in
        expr <:expr< $lid:dotop$ $e1$ $e2$ >>
      | (dotop, e2l) ->
        let dotop = dotop ^ "{;..}" in
        let aexp = <:expr< [| $list:e2l$ |] >> in
        expr <:expr< $lid:dotop$ $e1$ $aexp$ >>
      ]
  | ExChr loc s →
      mkexp loc
        (Pexp_constant (ocaml_pconst_char (char_of_char_token loc (uv s))))
  | ExCoe loc e t1 t2 →
      mkexp loc
        (ocaml_pexp_constraint (expr e) (option_map ctyp t1) (Some (ctyp t2)))
  | ExFlo loc s → mkexp loc (Pexp_constant (ocaml_pconst_float (uv s)))
  | ExFor loc i e1 e2 df el →
      let e3 = <:expr< do { $list:uv el$ } >> in
      let df = if uv df then Upto else Downto in
      mkexp loc (ocaml_pexp_for (patt i) (expr e1) (expr e2) df (expr e3))
  | ExFun loc pel →
      match uv pel with
      [ [(PaLab ploc lppo, w, e)] →
          match uv lppo with
          [ [(p, po)] →
              let lab = label_of_patt p in
              let p =
                match uv po with
                [ Some p → p
                | None → p ]
              in
              mkexp loc (ocaml_pexp_function lab None [mkpwe (p, w, e)])
          | _ → error loc "bad AST" ]
      | [(PaNty loc s, w, e)] →
          match ocaml_pexp_newtype with
          [ Some newtype →
              match uv w with
              [ Some _ → error loc "(type ..) not allowed with 'when'"
              | None → mkexp loc (newtype (mkloc loc) (uv s) (expr e)) ]
          | None → error loc "(type ..) not in this ocaml version" ]
      | [(PaOlb loc p eo, w, e)] →
          let lab = label_of_patt p in
          let (p, eo) =
            match uv eo with
            [ Some (ExOlb _ p eo) → (p, eo)
            | Some _ | None → (p, eo) ]
          in
          mkexp loc
            (ocaml_pexp_function ("?" ^ lab) (option_map expr (uv eo))
               [mkpwe (p, w, e)])
      | pel →
          let pel =
            if split_or_patterns_with_bindings then
              Prtools.do_split_or_patterns_with_bindings pel
            else pel
          in
          mkexp loc (ocaml_pexp_function "" None (List.map mkpwe pel)) ]
  | ExIfe loc e1 e2 e3 →
      let e3o =
        match e3 with
        [ ExLong _ <:longident< $uid:"()"$ >> → None
        | _ → Some (expr e3) ]
      in
      mkexp loc (Pexp_ifthenelse (expr e1) (expr e2) e3o)
  | ExInt loc s c →
      mkexp loc (Pexp_constant (pconst_of_const (mkintconst loc (uv s) c)))
  | ExLab loc _ → error loc "labeled expression not allowed here 1"
  | ExLaz loc e → mklazy loc (expr e)
  | ExLet loc rf pel e →
      mkexp loc (Pexp_let (mkrf (uv rf)) (List.map mkpe (uv pel)) (expr e))
  | ExLEx loc exnname exntyl body alg_attrs ->
      let exdef = ocaml_extension_exception (mkloc loc) (uv exnname) (List.map ctyp (uv exntyl)) (uv_alg_attributes alg_attrs) in
      mkexp loc (ocaml_pexp_letexception exdef (expr body))
  | ExLid loc s → mkexp loc (ocaml_pexp_ident (mkloc loc) (Lident (uv s)))
  | ExLmd loc i me e →
      match ocaml_pexp_letmodule with
      [ Some pexp_letmodule →
          mkexp loc (pexp_letmodule (option_map uv (uv i)) (module_expr me) (expr e))
      | None → error loc "no 'let module' in this ocaml version" ]
  | ExLop loc ovf me e →
      match ocaml_pexp_open with
      | Some pexp_open →
          let me = module_expr me in
          mkexp loc (pexp_open (mkoverride (uv ovf)) me (expr e))
      | None → error loc "no expression open in this ocaml version"
      end
  | ExMat loc e pel →
      let pel = uv pel in
      let pel =
        if split_or_patterns_with_bindings then
          Prtools.do_split_or_patterns_with_bindings pel
        else pel
      in
      mkexp loc (Pexp_match (expr e) (List.map mkpwe pel))
  | ExNew loc cli →
      mkexp loc
        (ocaml_pexp_new (mkloc loc) (longid_lident_long_id (uv cli)))
  | ExObj loc po cfl →
      match ocaml_pexp_object with
      [ Some pexp_object →
          let p =
            match uv po with
            [ Some p → p
            | None → PaAny loc ]
          in
          let cil = List.fold_right class_str_item (uv cfl) [] in
          mkexp loc (pexp_object (ocaml_class_structure (patt p) cil))
      | None → error loc "no object in this ocaml version" ]
  | ExOlb loc _ _ → error loc "labeled expression not allowed here 2"
  | ExOvr loc iel →
      mkexp loc (ocaml_pexp_override (List.map mkideexp (uv iel)))
  | ExPck loc me mto →
      match ocaml_pexp_pack with
      [ Some (Left pexp_pack) →
          match mto with
          [ Some mt →
              let pt = package_of_module_type loc mt in
              mkexp loc (pexp_pack (module_expr me) pt)
          | None → error loc "no such module pack in this ocaml version" ]
      | Some (Right (pexp_pack, ptyp_package)) →
          let e = pexp_pack (module_expr me) in
          let e =
            match mto with
            [ Some mt →
                let pt = package_of_module_type loc mt in
                ocaml_pexp_constraint (mkexp loc e)
                  (Some (mktyp loc (ptyp_package pt))) None
            | None → e ]
          in
          mkexp loc e
      | None → error loc "no module pack in this ocaml version" ]
  | ExRec loc lel eo →
      let lel = uv lel in
      if lel = [] then error loc "empty record"
      else
        let eo =
          match eo with
          [ Some e → Some (expr e)
          | None → None ]
        in
        mkexp loc (ocaml_pexp_record (List.map mklabexp lel) eo)
  | ExSeq loc el →
      loop (uv el) where rec loop =
        fun
        [ [] → expr <:expr< () >>
        | [e] → expr e
        | [e :: el] →
            let loc = Ploc.encl (loc_of_expr e) loc in
            mkexp loc (Pexp_sequence (expr e) (loop el)) ]
  | ExSnd loc e s → mkexp loc (ocaml_pexp_send (mkloc loc) (expr e) (uv s))
  | ExSte loc dotop e1 e2l →
      match (uv dotop, uv e2l) with [
        (".", [e2]) ->
          let cloc = mkloc loc in
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc (ocaml_pexp_ident cloc (array_function "String" "get")))
               [("", expr e1); ("", expr e2)])
      | (".", e2l) -> assert False
      | (dotop, [e2]) ->
        let dotop = dotop ^ "[]" in
        expr <:expr< $lid:dotop$ $e1$ $e2$ >>
      | (dotop, e2l) ->
        let dotop = dotop ^ "[;..]" in
        let aexp = <:expr< [| $list:e2l$ |] >> in
        expr <:expr< $lid:dotop$ $e1$ $aexp$ >>
      ]
  | ExStr loc s →
      mkexp loc
        (Pexp_constant
           (ocaml_pconst_string (string_of_string_token loc (uv s)) (mkloc loc) None))
  | ExTry loc e pel → mkexp loc (Pexp_try (expr e) (List.map mkpwe (uv pel)))
  | ExTup loc el → mkexp loc (Pexp_tuple (List.map expr (uv el)))
  | ExTyc loc e t →
      mkexp loc (ocaml_pexp_constraint (expr e) (Some (ctyp t)) None)
  | ExVrn loc s →
      match ocaml_pexp_variant with
      [ Some (_, pexp_variant) → mkexp loc (pexp_variant (uv s, None))
      | None → error loc "no variants in this ocaml version" ]
  | ExWhi loc e1 el →
      let e2 = <:expr< do { $list:uv el$ } >> in
      mkexp loc (Pexp_while (expr e1) (expr e2))
  | ExXtr loc _ _ → error loc "bad ast ExXtr"
  | ExExten loc ebody -> mkexp loc (ocaml_pexp_extension (extension (uv ebody)))
  | ExUnr loc -> error loc "bad ast ExUnr (parses as '.'; cannot have an ExUnr except at the rhs of match-case)"
  ]
and label_expr rev_al =
  fun
  [ ExLab loc lpeo →
      List.fold_left
        (fun rev_al (p, eo) →
           match p with
           [ PaLid loc lab →
               let e =
                 match uv eo with
                 [ Some e → e
                 | None → ExLid loc lab ]
               in
               [(uv lab, expr e) :: rev_al]
           | _ → error loc "ExLab case not impl" ])
        rev_al (uv lpeo)
  | ExOlb loc p eo →
      match p with
      [ PaLid loc lab →
          let e =
            match uv eo with
            [ Some e → e
            | None → ExLid loc lab ]
          in
          [("?" ^ uv lab, expr e) :: rev_al]
      | _ → error loc "ExOlb case not impl" ]
  | e → [("", expr e) :: rev_al] ]
and mkpe (p, e, attrs) =
  let loc = Ploc.encl (loc_of_patt p) (loc_of_expr e) in
  let (p, e) =
    match p with
    [ PaTyc loc p (TyPot loc1 nt ct) → expand_gadt_type loc p loc1 nt ct e
    | p → (p, e) ]
  in
  ocaml_value_binding ~{item_attributes=uv_item_attributes attrs} (mkloc loc) (patt p) (expr e)
and expand_gadt_type loc p loc1 nt ct e =
  let nt = uv nt in
  let e = <:expr< ($e$ : $ct$) >> in
  let e =
    List.fold_right (fun s e → <:expr< fun (type $s$) →  $e$ >>)
      nt e
  in
  let ct = varify_constructors nt ct in
  let tp = List.map (fun s → "&" ^ s) nt in
  let ct = <:ctyp< ! $list:tp$ . $ct$ >> in
  (<:patt< ($p$ : $ct$) >>, e)
and mkpwe (p, w, e) =
  let conve = match e with [
    ExUnr loc -> mkexp loc (ocaml_pexp_unreachable())
  | e -> expr e ] in
  ocaml_case (patt p, option_map expr (uv w), mkloc (loc_of_expr e), conve)
and mklabexp (lab, e) =
  (patt_label_long_id lab, mkloc (loc_of_patt lab), expr e)
and mkideexp (ide, e) = (ide, expr e)
and mktype_decl td =
  let priv = if uv td.tdPrv then Private else Public in
  let cl =
    List.map
      (fun (t1, t2) →
         let loc = Ploc.encl (loc_of_ctyp t1) (loc_of_ctyp t2) in
         (ctyp t1, ctyp t2, mkloc loc))
      (uv td.tdCon)
  in
  let tn = uv (snd (uv td.tdNam)) in
  (tn, type_decl ~{item_attributes=uv_item_attributes td.tdAttributes} tn (uv td.tdPrm) priv (cl,uv td.tdCon) td.tdDef)
and module_type =
  fun
  [ MtAtt loc e a ->
      ocaml_pmty_addattr (attr (uv a)) (module_type e)
  | MtLongLid loc _ _ as f →
      mkmty loc (ocaml_pmty_ident (mkloc loc) (module_type_long_id f))
  | MtLong loc _ as f →
      mkmty loc (ocaml_pmty_ident (mkloc loc) (module_type_long_id f))
  | MtLid loc s → mkmty loc (ocaml_pmty_ident (mkloc loc) (Lident (uv s)))
  | MtFun loc arg mt →
    let arg = option_map (fun (idopt, mt) -> (option_map uv (uv idopt), module_type mt)) (uv arg) in
      mkmty loc
        (ocaml_pmty_functor (mkloc loc) arg
           (module_type mt))
  | MtQuo loc _ → error loc "abstract module type not allowed here"
  | MtSig loc sl →
      mkmty loc (Pmty_signature (List.fold_right sig_item (uv sl) []))
  | MtTyo loc me →
      match ocaml_pmty_typeof with
      [ Some pmty_typeof → mkmty loc (pmty_typeof (module_expr me))
      | None → error loc "no 'module type of ..' in this ocaml version" ]
  | MtWit loc mt wcl →
      mkmty loc (ocaml_pmty_with (module_type mt) (List.map mkwithc (uv wcl)))
  | MtXtr loc _ _ → error loc "bad ast MtXtr"
  | MtExten loc ebody -> mkmty loc (ocaml_pmty_extension (extension (uv ebody)))
  ]
and sig_item s l =
  match s with
  [ 
    SgCls loc cd →
      [mksig loc (Psig_class (List.map (class_info uv_item_attributes class_type) (uv cd))) :: l]
  | SgClt loc ctd →
      match ocaml_psig_class_type with
      [ Some psig_class_type →
          [mksig loc
             (psig_class_type (List.map (class_info uv_item_attributes class_type) (uv ctd))) ::
           l]
      | None → error loc "no class type in this ocaml version" ]
  | SgDcl loc sl → List.fold_right sig_item (uv sl) l
  | SgDir loc _ _ → l
  | SgExc loc gc item_attrs ->
      let (n, tl, _, alg_attrs) = conv_constructor False gc in
      [mksig loc
         (ocaml_psig_exception ~{alg_attributes=alg_attrs} ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc) n tl) ::
       l]
  | SgExt loc n ls t p attrs →
      let vn = uv n in
      [mksig loc (ocaml_psig_value vn (mkvalue_desc ~{item_attributes=uv_item_attributes attrs} vn (uv ls, t) (uv p))) :: l]
  | SgInc loc mt attrs →
      [mksig loc (ocaml_psig_include ~{item_attributes=uv_item_attributes attrs} (mkloc loc) (module_type mt)) :: l]
  | SgMod loc rf ntl →
      if not (uv rf) then
        List.fold_right
          (fun (nopt, mt, item_attrs) l →
             [mksig loc
                (ocaml_psig_module ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc) (option_map uv (uv nopt)) (module_type mt)) :: l])
          (uv ntl) l
      else
        match ocaml_psig_recmodule with
        [ Some psig_recmodule →
            let ntl =
              List.map (fun (nopt, mt, item_attrs) → (option_map uv (uv nopt), module_type mt, uv_item_attributes item_attrs)) (uv ntl)
            in
            [mksig loc (psig_recmodule ntl) :: l]
        | None → error loc "no recursive module in this ocaml version" ]
  | SgMty loc n mt item_attrs →
      let mto =
        match mt with
        | MtQuo _ _ -> None
        | _ -> Some (module_type mt)
        end
      in
      [mksig loc (ocaml_psig_modtype ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc) (uv n) mto) :: l]
  | SgMtySubst loc n mt item_attrs →
      let mto =
        match mt with
        | MtQuo _ _ -> None
        | _ -> Some (module_type mt)
        end
      in
      [mksig loc (ocaml_psig_modtypesubst ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc) (uv n) mto) :: l]

  | SgMtyAlias loc n li item_attrs ->
      let li = longid_long_id (uv li) in
      let mty = mkmty loc (ocaml_pmty_alias (mkloc loc) li) in
      let m = ocaml_psig_module ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc) (Some (uv n)) mty in
      [mksig loc m :: l]

  | SgModSubst loc s li item_attrs ->
      let li = longid_long_id li in
      let attrs = uv_item_attributes item_attrs in
      let m = ocaml_psig_modsubst ~{item_attributes=attrs} (mkloc loc) (uv s) li in
      [mksig loc m :: l]

  | SgOpn loc lid attrs →
      let lid = extended_longid_long_id lid in
      [mksig loc
         (ocaml_psig_open ~{item_attributes=uv_item_attributes attrs} (mkloc loc) lid) ::
       l]
  | SgTyp loc flg tdl →
      let si_desc =
        if List.for_all (fun td -> uv td.tdIsDecl) (uv tdl) then
          ocaml_psig_type (uv flg) (List.map mktype_decl (uv tdl))
        else if List.for_all (fun td -> not (uv td.tdIsDecl)) (uv tdl) then
          if not (uv flg) then
            ocaml_psig_typesubst (List.map mktype_decl (uv tdl))
          else error loc "type-subst with nonrec flag specified"
        else error loc "type-decl/subst with mixed decl/subst"
      in
      [mksig loc si_desc :: l]

  | SgTypExten loc te →
      [mksig loc (ocaml_psig_typext (type_extension loc te)) :: l]
  | SgUse loc fn sl →
      Ploc.call_with glob_fname (uv fn)
        (fun () → List.fold_right (fun (si, _) → sig_item si) (uv sl) l) ()
  | SgVal loc n t attrs →
      let vn = uv n in
      [mksig loc (ocaml_psig_value vn (mkvalue_desc ~{item_attributes=uv_item_attributes attrs} vn ([], t) [])) :: l]
  | SgXtr loc _ _ → error loc "bad ast SgXtr"
  | SgFlAtt loc float_attr →
      [mksig loc
         (ocaml_psig_attribute (attr (uv float_attr))) ::
       l]
  | SgExten loc ebody attrs -> [mksig loc (ocaml_psig_extension ~{item_attributes=uv_item_attributes attrs} (extension (uv ebody))) :: l]
  ]
and module_expr =
  fun
  [ MeAtt loc e a ->
      ocaml_pmod_addattr (attr (uv a)) (module_expr e)
  | MeAcc loc _ _ as f → mkmod loc (ocaml_pmod_ident (module_expr_long_id f))
  | MeApp loc me1 me2 →
      mkmod loc (Pmod_apply (module_expr me1) (module_expr me2))
  | MeFun loc arg me →
    let arg = option_map (fun (idopt, mt) -> (option_map uv (uv idopt), module_type mt)) (uv arg) in
      mkmod loc (ocaml_pmod_functor arg (module_expr me))
  | MeStr loc sl →
      mkmod loc (Pmod_structure (List.fold_right str_item (uv sl) []))
  | MeTyc loc me mt →
      mkmod loc (Pmod_constraint (module_expr me) (module_type mt))
  | MeUid loc s → mkmod loc (ocaml_pmod_ident (Lident (uv s)))
  | MeUnp loc e mto1 mto2 →
      match ocaml_pmod_unpack with
      [ Some (Left pmod_unpack) →
          match (mto1, mto2) with
          [ (Some mt, None) →
              let pt = package_of_module_type loc mt in
              mkmod loc (pmod_unpack (expr e) pt)
          | _ → error loc "no such module unpack in this ocaml version" ]
      | Some (Right (pmod_unpack, ptyp_package)) →
          let e =
            match (mto1, mto2) with
            [ (Some mt1, None) →
                let pt = package_of_module_type loc mt1 in
                let t = mktyp loc (ptyp_package pt) in
                mkexp loc (ocaml_pexp_constraint (expr e) (Some t) None)
            | (Some mt1, Some mt2) →
                let t1 = mktyp loc (ptyp_package (package_of_module_type loc mt1)) in
                let t2 = mktyp loc (ptyp_package (package_of_module_type loc mt2)) in
                mkexp loc (ocaml_pexp_constraint (expr e) (Some t1) (Some t2))
            | (None, Some _) -> error loc "malformed module unpack"
            | (None, None) →
                expr e ]
          in
          mkmod loc (pmod_unpack e)
      | None → error loc "no module unpack in this ocaml version" ]
  | MeXtr loc _ _ → error loc "bad ast MeXtr"
  | MeExten loc ebody -> mkmod loc (ocaml_pmod_extension (extension (uv ebody)))
 ]
and str_item s l =
  match s with
  [ StCls loc cd →
      [mkstr loc (Pstr_class (List.map (class_info uv_item_attributes class_expr) (uv cd))) :: l]
  | StClt loc ctd →
      match ocaml_pstr_class_type with
      [ Some pstr_class_type →
          [mkstr loc
             (pstr_class_type (List.map (class_info uv_item_attributes class_type) (uv ctd))) ::
           l]
      | None → error loc "no class type in this ocaml version" ]
  | StDcl loc sl → List.fold_right str_item (uv sl) l
  | StDir loc _ _ → l
  | StExc loc ec item_attrs ->
    match uv ec with [
      EcTuple loc gc ->
      let (n, tl, _, alg_attrs) = conv_constructor False gc in
      let si =
            ocaml_pstr_exception ~{alg_attributes=alg_attrs} ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc) n tl
      in
      [mkstr loc si :: l]


    | EcRebind loc n li alg_attrs ->
      let si =
            match ocaml_pstr_exn_rebind with
            [ Some pstr_exn_rebind →
                pstr_exn_rebind (mkloc loc) (uv n)
                  (longid_long_id (uv li))
            | None →
                error loc "no exception renaming in this ocaml version" ]
      in
      [mkstr loc si :: l]
    ]
  | StExp loc e attrs → [mkstr loc (ocaml_pstr_eval ~{item_attributes=uv_item_attributes attrs} (expr e)) :: l]
  | StExt loc n ls t p attrs →
      let vn = uv n in
      [mkstr loc (ocaml_pstr_primitive vn (mkvalue_desc ~{item_attributes=uv_item_attributes attrs} vn (uv ls, t) (uv p))) :: l]
  | StInc loc me attrs →
      match ocaml_pstr_include with
      [ Some pstr_include →
          [mkstr loc (pstr_include ~{item_attributes=uv_item_attributes attrs} (mkloc loc) (module_expr me)) :: l]
      | None → error loc "no include in this ocaml version" ]
  | StMod loc rf nel →
      if not (uv rf) then
        List.fold_right
          (fun (nopt, me, attrs) l →
             let m = ocaml_pstr_module ~{item_attributes=uv_item_attributes attrs} (mkloc loc) (option_map uv (uv nopt)) (module_expr me) in
             [mkstr loc m :: l])
          (uv nel) l
      else
        match ocaml_pstr_recmodule with
        [ Some pstr_recmodule →
            let nel =
              List.map
                (fun (nopt, me, attrs) →
                   let attrs = uv_item_attributes attrs in
                   let (me, mt) =
                     match me with
                     [ MeTyc _ me mt → (module_expr me, module_type mt)
                     | _ →
                         error (MLast.loc_of_module_expr me)
                           "module rec needs module types constraints" ]
                   in
                   (option_map uv (uv nopt), mt, ocaml_pmod_constraint (mkloc loc) me mt, attrs))
                (uv nel)
            in
            [mkstr loc (pstr_recmodule nel) :: l]
        | None → error loc "no recursive module in this ocaml version" ]
  | StMty loc n mt item_attrs →
      let mto =
        match mt with
        | MtQuo _ _ -> None
        | _ -> Some (module_type mt)
        end
      in
      let m = ocaml_pstr_modtype ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc) (uv n) mto in
      [mkstr loc m :: l]
  | StOpn loc ovf me attrs →
      [mkstr loc
         (ocaml_pstr_open ~{item_attributes=uv_item_attributes attrs} (mkoverride (uv ovf)) (mkloc loc) (module_expr me)) ::
       l]
  | StTyp loc flg tdl →
      [mkstr loc (ocaml_pstr_type (uv flg) (List.map mktype_decl (uv tdl))) :: l]
  | StTypExten loc te →
      [mkstr loc (ocaml_pstr_typext (type_extension loc te)) :: l]
  | StUse loc fn sl →
      Ploc.call_with glob_fname (uv fn)
        (fun () → List.fold_right (fun (si, _) → str_item si) (uv sl) l) ()
  | StVal loc rf pel →
      [mkstr loc (Pstr_value (mkrf (uv rf)) (List.map mkpe (uv pel))) :: l]
  | StXtr loc _ _ → error loc "bad ast StXtr"
  | StFlAtt loc float_attr →
      [mkstr loc
         (ocaml_pstr_attribute (attr (uv float_attr))) ::
       l]
  | StExten loc ebody attrs -> [mkstr loc (ocaml_pstr_extension ~{item_attributes=uv_item_attributes attrs} (extension (uv ebody))) :: l]
  ]
and class_type =
  fun
  [ CtAtt loc e a ->
    ocaml_pcty_addattr (attr (uv a)) (class_type e)
  | CtLongLid loc _ _ | CtLid loc _ as ct ->
    let li = class_type_long_id ct in
      match ocaml_pcty_constr with
      [ Some pcty_constr → mkcty loc (pcty_constr li [])
      | None → error loc "no class type desc in this ocaml version" ]

  | CtLop loc ovf me ct →
      let li = longid_long_id me in
      mkcty loc
        (ocaml_pcty_open (mkloc loc) li (mkoverride (uv ovf)) (class_type ct))
  | CtCon loc ct tl →
      let li = class_type_long_id ct in
      match ocaml_pcty_constr with
      [ Some pcty_constr → mkcty loc (pcty_constr li (List.map ctyp (uv tl)))
      | None → error loc "no class type desc in this ocaml version" ]
  | CtFun loc (TyLab _ lab t) ct →
      match ocaml_pcty_fun with
      [ Some pcty_fun →
          let ty = ctyp t in
          mkcty loc (pcty_fun (uv lab) ty ty (class_type ct))
      | None → error loc "no class type desc in this ocaml version" ]
  | CtFun loc (TyOlb loc1 lab t) ct →
      match ocaml_pcty_fun with
      [ Some pcty_fun →
          let ty = ctyp t in
          let ot = let loc = loc1 in ctyp <:ctyp< option_map $t$ >> in
          let pcty = pcty_fun ("?" ^ uv lab) ty ot (class_type ct) in
          mkcty loc pcty
      | None → error loc "no class type desc in this ocaml version" ]
  | CtFun loc t ct →
      match ocaml_pcty_fun with
      [ Some pcty_fun →
          let ty = ctyp t in
          mkcty loc (pcty_fun "" ty ty (class_type ct))
      | None → error loc "no class type desc in this ocaml version" ]
  | CtSig loc t_o ctfl →
      match ocaml_pcty_signature with
      [ Some pcty_signature →
          let t =
            match uv t_o with
            [ Some t → t
            | None → TyAny loc ]
          in
          let cil = List.fold_right class_sig_item (uv ctfl) [] in
          mkcty loc (pcty_signature (ctyp t, cil))
      | None → error loc "no class type desc in this ocaml version" ]
  | CtXtr loc _ _ → error loc "bad ast CtXtr"
  | CtExten loc ebody -> mkcty loc (ocaml_pcty_extension (extension (uv ebody)))
  ]
and class_sig_item c l =
  match c with
  [ CgCtr loc t1 t2 item_attrs →
      match ocaml_pctf_cstr with
      [ Some pctf_cstr →
          let loc = mkloc loc in
          [ocaml_class_type_field ~{item_attributes=uv_item_attributes item_attrs} loc (pctf_cstr (ctyp t1, ctyp t2, loc)) ::
           l]
      | None → error loc "no class constraint in this ocaml version" ]
  | CgDcl loc cl → List.fold_right class_sig_item (uv cl) l
  | CgInh loc ct item_attrs →
      [ocaml_class_type_field ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc)
         (ocaml_pctf_inher (class_type ct)) :: l]
  | CgMth loc pf s t item_attrs →
      [ocaml_class_type_field ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc)
         (ocaml_pctf_meth
            (uv s, mkprivate (uv pf), add_polytype t, mkloc loc)) ::
       l]
  | CgVal loc mf vf s t item_attrs →
      [ocaml_class_type_field ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc)
         (ocaml_pctf_val (uv s, mkmutable (uv mf), mkvirtual (uv vf), ctyp t, mkloc loc)) ::
       l]
  | CgVir loc b s t item_attrs →
      [ocaml_class_type_field ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc)
         (ocaml_pctf_virt
            (uv s, mkprivate (uv b), add_polytype t, mkloc loc)) ::
       l]
  | CgFlAtt loc float_attr →
      [ocaml_class_type_field (mkloc loc)
         (ocaml_pctf_attribute (attr (uv float_attr))) ::
       l]
  | CgExten loc ebody ->
      [ocaml_class_type_field (mkloc loc) (ocaml_pctf_extension (extension (uv ebody))) ::
       l]
  ]
and class_expr =
  fun
  [ CeAtt loc e a ->
    ocaml_pcl_addattrs [attr (uv a)] (class_expr e)
  | CeApp loc _ _ as c →
      match ocaml_pcl_apply with
      [ Some pcl_apply →
          let (ce, el) = class_expr_fa [] c in
          let el = List.rev (List.fold_left label_expr [] el) in
          mkpcl loc (pcl_apply (class_expr ce) el)
      | None → error loc "no class expr desc in this ocaml version" ]
  | CeCon loc cli tl →
      match ocaml_pcl_constr with
      [ Some pcl_constr →
          mkpcl loc
            (pcl_constr (longid_lident_long_id (uv cli))
               (List.map ctyp (uv tl)))
      | None → error loc "no class expr desc in this ocaml version" ]
  | CeFun loc (PaLab ploc lppo) ce →
      match ocaml_pcl_fun with
      [ Some pcl_fun →
          match uv lppo with
          [ [(p, po)] →
              let lab = label_of_patt p in
              let p =
                match uv po with
                [ Some p → p
                | None → p ]
              in
              mkpcl loc (pcl_fun lab None (patt p) (class_expr ce))
          | [] | [_ :: _] → error ploc "case class multi lab not yet impl" ]
      | None → error loc "no class expr desc in this ocaml version" ]
  | CeFun loc (PaOlb _ p eo) ce →
      match ocaml_pcl_fun with
      [ Some pcl_fun →
          let lab = label_of_patt p in
          let (p, eo) =
            match uv eo with
            [ Some (ExOlb _ p eo) → (p, eo)
            | Some _ | None → (p, eo) ]
          in
          mkpcl loc
            (pcl_fun ("?" ^ lab) (option_map expr (uv eo)) (patt p)
               (class_expr ce))
      | None → error loc "no class expr desc in this ocaml version" ]
  | CeFun loc p ce →
      match ocaml_pcl_fun with
      [ Some pcl_fun → mkpcl loc (pcl_fun "" None (patt p) (class_expr ce))
      | None → error loc "no class expr desc in this ocaml version" ]
  | CeLet loc rf pel ce →
      match ocaml_pcl_let with
      [ Some pcl_let →
          mkpcl loc
            (pcl_let (mkrf (uv rf)) (List.map mkpe (uv pel)) (class_expr ce))
      | None → error loc "no class expr desc in this ocaml version" ]
  | CeLop loc ovf me ce →
      let li = longid_long_id me in
      mkpcl loc
        (ocaml_pcl_open (mkloc loc) li (mkoverride (uv ovf)) (class_expr ce))
  | CeStr loc po cfl →
      match ocaml_pcl_structure with
      [ Some pcl_structure →
          let p =
            match uv po with
            [ Some p → p
            | None → PaAny loc ]
          in
          let cil = List.fold_right class_str_item (uv cfl) [] in
          mkpcl loc (pcl_structure (ocaml_class_structure (patt p) cil))
      | None → error loc "no class expr desc in this ocaml version" ]
  | CeTyc loc ce ct →
      match ocaml_pcl_constraint with
      [ Some pcl_constraint →
          mkpcl loc (pcl_constraint (class_expr ce) (class_type ct))
      | None → error loc "no class expr desc in this ocaml version" ]
  | CeXtr loc _ _ → error loc "bad ast CeXtr"
  | CeExten loc ebody -> mkpcl loc (ocaml_pcl_extension (extension (uv ebody)))
  ]
and class_str_item c l =
  match c with
  [ CrCtr loc t1 t2 attrs →
      match ocaml_pcf_cstr with
      [ Some pcf_cstr →
          let loc = mkloc loc in
          [ocaml_class_field ~{item_attributes=uv_item_attributes attrs} loc (pcf_cstr (ctyp t1, ctyp t2, loc)) :: l]
      | None → error loc "no constraint in this ocaml version" ]
  | CrDcl loc cl → List.fold_right class_str_item (uv cl) l
  | CrInh loc ovflag ce pb attrs →
      let ovflag = mkoverride (uv ovflag) in
      [ocaml_class_field ~{item_attributes=uv_item_attributes attrs} (mkloc loc)
         (ocaml_pcf_inher (mkloc loc) ovflag (class_expr ce) (uv pb)) ::
       l]
  | CrIni loc e attrs →
      match ocaml_pcf_init with
      [ Some pcf_init →
          [ocaml_class_field ~{item_attributes=uv_item_attributes attrs} (mkloc loc) (pcf_init (expr e)) :: l]
      | None → error loc "no initializer in this ocaml version" ]
  | CrMth loc ovf pf s ot e item_attrs →
      let e =
        match ocaml_pexp_poly with
        [ Some pexp_poly →
            let t = option_map (fun t → add_polytype t) (uv ot) in
            mkexp loc (pexp_poly (expr e) t)
        | None →
            if uv ot = None then expr e
            else error loc "no method with label in this ocaml version" ]
      in
      [ocaml_class_field ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc)
         (ocaml_pcf_meth (uv s, uv pf, uv ovf, e, mkloc loc)) ::
       l]
  | CrVal loc ovf mf s e attrs →
      [ocaml_class_field ~{item_attributes=uv_item_attributes attrs} (mkloc loc)
         (ocaml_pcf_val (uv s, uv mf, uv ovf, expr e, mkloc loc)) ::
       l]
  | CrVav loc mf s t attrs →
      match ocaml_pcf_valvirt with
      [ Some pcf_valvirt →
          [ocaml_class_field ~{item_attributes=uv_item_attributes attrs} (mkloc loc)
             (pcf_valvirt (uv s, uv mf, ctyp t, mkloc loc)) ::
           l]
      | None → error loc "no virtual value in this ocaml version" ]
  | CrVir loc b s t item_attrs →
      [ocaml_class_field ~{item_attributes=uv_item_attributes item_attrs} (mkloc loc)
         (ocaml_pcf_virt
            (uv s, mkprivate (uv b), add_polytype t, mkloc loc)) ::
       l]
  | CrFlAtt loc float_attr →
      [ocaml_class_field (mkloc loc)
         (ocaml_pcf_attribute (attr (uv float_attr))) ::
       l]
  | CrExten loc ebody -> 
      [ocaml_class_field (mkloc loc) (ocaml_pcf_extension (extension (uv ebody))) :: l]
  ]
and uv_item_attributes attrs =
    conv_attributes (uv attrs)
and uv_alg_attributes attrs =
    conv_attributes (uv attrs)
and conv_attributes x =
    let x = List.map uv x in
    let x = List.map attr x in
    x

and attr (id, payload) =
  let (idloc, id) = uv id in
  let locid = (mkloc idloc, id) in
  match payload with [
    StAttr loc st ->
      let st = List.fold_right str_item (uv st) [] in
      ocaml_attribute_implem (mkloc loc) locid st
  | SiAttr loc si ->
      let si = List.fold_right sig_item (uv si) [] in
      ocaml_attribute_interf (mkloc loc) locid si
  | TyAttr loc ty ->
      let ty = ctyp (uv ty) in
      ocaml_attribute_type (mkloc loc) locid ty
  | PaAttr loc p eopt ->
      let p = patt (uv p) in
      let eopt = option_map uv eopt in
      let eopt = option_map expr eopt in
      ocaml_attribute_patt (mkloc loc) locid p eopt
  ]
and extension (idloc, payload) =
  let (idloc, id) = uv idloc in
  match payload with [
    StAttr _ st ->
      let st = List.fold_right str_item (uv st) [] in
      ocaml_extension_implem (mkloc idloc, id) st
  | SiAttr _ si ->
      let si = List.fold_right sig_item (uv si) [] in
      ocaml_extension_interf (mkloc idloc, id) si
  | TyAttr _ ty ->
      let ty = ctyp (uv ty) in
      ocaml_extension_type (mkloc idloc, id) ty
  | PaAttr _ p eopt ->
      let p = patt (uv p) in
      let eopt = option_map uv eopt in
      let eopt = option_map expr eopt in
      ocaml_extension_patt (mkloc idloc, id) p eopt
  ]
;

value interf fname ast = do {
  glob_fname.val := fname;
  List.fold_right sig_item ast []
};

value implem fname ast = do {
  glob_fname.val := fname;
  List.fold_right str_item ast []
};

value directive loc =
  fun
  [ <:expr< $str:s$ >> → Pdir_string s
  | <:expr< $int:i$ >> → ocaml_pdir_int i (int_of_string_l loc i)
  | <:expr< True >> →
      match ocaml_pdir_bool with
      [ Some pdir_bool → pdir_bool True
      | None → error loc "no such kind of directive in this ocaml version" ]
  | <:expr< False >> →
      match ocaml_pdir_bool with
      [ Some pdir_bool → pdir_bool False
      | None → error loc "no such kind of directive in this ocaml version" ]
  | <:expr< $longid:li$ >> -> Pdir_ident (longid_long_id li)
  | <:expr< $longid:li$ >> -> Pdir_ident (longid_long_id li)
  | <:expr< $longid:li$ . $lid:id$ >> -> Pdir_ident (longid_lident_long_id (Some <:vala< li >>,<:vala< id >>))
  | <:expr<  $lid:id$ >> -> Pdir_ident (Lident id)
  | e →
      let sl =
        loop e where rec loop =
          fun
          [ <:expr< $lid:i$ >> → [i]
          | <:expr< $uid:i$ >> → [i]
          | e → Ploc.raise (loc_of_expr e) (Failure "bad ast") ]
      in
      Pdir_ident (long_id_of_string_list loc sl) ]
;

value directive_args loc d =
  match d with
  | Some d -> ocaml_pdir_some (directive loc d)
  | None -> ocaml_pdir_none
  end
;

value phrase =
  fun
  [ StDir loc d dp →
      ocaml_ptop_dir (mkloc loc) (uv d) (directive_args loc (uv dp))
  | si → do {
      glob_fname.val := Plexing.input_file.val;
      Ptop_def (str_item si [])
    } ]
;
