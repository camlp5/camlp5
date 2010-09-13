(* camlp5r *)
(* $Id: ast2pt.ml,v 1.116 2010/09/13 15:37:06 deraugla Exp $ *)

#load "q_MLast.cmo";
#load "pa_macro.cmo";

open Parsetree;
open Longident;
open Asttypes;
open Versdep;

open MLast;

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

value fast = ref False;

value get_tag x =
  if Obj.is_block (Obj.repr x) then Obj.tag (Obj.repr x) else Obj.magic x
;

value error loc str = Ploc.raise loc (Failure str);

value char_of_char_token loc s =
  try Plexing.eval_char s with
  [ Failure _ as exn -> Ploc.raise loc exn ]
;

value string_of_string_token loc s =
  try Plexing.eval_string loc s with
  [ Failure _ as exn -> Ploc.raise loc exn ]
;

value glob_fname = ref "";

value mkloc loc =
  let bp = Ploc.first_pos loc in
  let ep = Ploc.last_pos loc in
  let lnum = Ploc.line_nb loc in
  let bolp = Ploc.bol_pos loc in
  ocaml_location (glob_fname.val, lnum, bolp, bp, ep)
;

value mktyp loc d = {ptyp_desc = d; ptyp_loc = mkloc loc};
value mkpat loc d = {ppat_desc = d; ppat_loc = mkloc loc};
value mkexp loc d = {pexp_desc = d; pexp_loc = mkloc loc};
value mkmty loc d = {pmty_desc = d; pmty_loc = mkloc loc};
value mksig loc d = {psig_desc = d; psig_loc = mkloc loc};
value mkmod loc d = {pmod_desc = d; pmod_loc = mkloc loc};
value mkstr loc d = {pstr_desc = d; pstr_loc = mkloc loc};
value mkfield loc d = {pfield_desc = d; pfield_loc = mkloc loc};
value mkcty loc d =
  match ocaml_class_type with
  [ Some class_type -> class_type d (mkloc loc)
  | None -> error loc "no class type in this ocaml version" ]
;
value mkpcl loc d =
  match ocaml_class_expr with
  [ Some class_expr -> class_expr d (mkloc loc)
  | None -> error loc "no class expr in this ocaml version" ]
;
value mklazy loc e =
  match ocaml_pexp_lazy with
  [ Some pexp_lazy -> mkexp loc (pexp_lazy e)
  | None -> do {
      let ghpat = mkpat loc in
      let ghexp = mkexp loc in
      let void_pat = ghpat (Ppat_construct (Lident "()") None False) in
      let f = ghexp (ocaml_pexp_function "" None [(void_pat, e)]) in
      let delayed = Ldot (Lident "Lazy") "Delayed" in
      let df = ghexp (Pexp_construct delayed (Some f) False) in
      let r = ghexp (Pexp_ident (Ldot (Lident "Pervasives") "ref")) in
      ghexp (ocaml_pexp_apply r [("", df)])
    } ]
;

value conv_con = do {
  let t = Hashtbl.create 73 in
  List.iter (fun (s, s') -> Hashtbl.add t s s')
    [("True", "true"); ("False", "false"); (" True", "True");
     (" False", "False")];
  fun s -> try Hashtbl.find t s with [ Not_found -> s ]
};

value conv_lab = do {
  let t = Hashtbl.create 73 in
  List.iter (fun (s, s') -> Hashtbl.add t s s') [("val", "contents")];
  fun s -> try Hashtbl.find t s with [ Not_found -> s ]
};

value array_function str name =
  Ldot (Lident str) (if fast.val then "unsafe_" ^ name else name)
;

value uv c =
  match (c, "") with
  [ (<:vala< c >>, "") -> c
  | _ -> invalid_arg "Ast2pt.uv" ]
;

value mkrf =
  fun
  [ True -> Recursive
  | False -> Nonrecursive ]
;

value mkli s =
  loop (fun s -> Lident s) where rec loop f =
    fun
    [ [i :: il] -> loop (fun s -> Ldot (f i) s) il
    | [] -> f s ]
;

value long_id_of_string_list loc sl =
  match List.rev sl with
  [ [] -> error loc "bad ast"
  | [s :: sl] -> mkli s (List.rev sl) ]
;

value rec ctyp_fa al =
  fun
  [ TyApp _ f a -> ctyp_fa [a :: al] f
  | f -> (f, al) ]
;

value rec ctyp_long_id =
  fun
  [ <:ctyp< $m$.$lid:s$ >> ->
      let (is_cls, li) = ctyp_long_id m in
      (is_cls, Ldot li s)
  | <:ctyp< $m$.$uid:s$ >> ->
      let (is_cls, li) = ctyp_long_id m in
      (is_cls, Ldot li s)
  | <:ctyp< $m1$ $m2$ >> ->
      let (is_cls, li1) = ctyp_long_id m1 in
      let (_, li2) = ctyp_long_id m2 in
      (is_cls, Lapply li1 li2)
  | <:ctyp< $uid:s$ >> -> (False, Lident s)
  | <:ctyp< $lid:s$ >> -> (False, Lident s)
  | TyCls loc sl -> (True, long_id_of_string_list loc (uv sl))
  | t -> error (loc_of_ctyp t) "incorrect type" ]
;

value rec module_type_long_id =
  fun
  [ <:module_type< $m$ . $uid:s$ >> -> Ldot (module_type_long_id m) s
  | <:module_type< $m$ . $lid:s$ >> -> Ldot (module_type_long_id m) s
  | MtApp _ m1 m2 -> Lapply (module_type_long_id m1) (module_type_long_id m2)
  | <:module_type< $lid:s$ >> -> Lident s
  | <:module_type< $uid:s$ >> -> Lident s
  | t -> error (loc_of_module_type t) "bad module type long ident" ]
;

value rec ctyp =
  fun
  [ TyAcc loc _ _ as f ->
      let (is_cls, li) = ctyp_long_id f in
      if is_cls then mktyp loc (ocaml_ptyp_class li [] [])
      else mktyp loc (Ptyp_constr li [])
  | TyAli loc t1 t2 ->
      let (t, i) =
        match (t1, t2) with
        [ (t, <:ctyp< '$s$ >>) -> (t, s)
        | (<:ctyp< '$s$ >>, t) -> (t, s)
        | _ -> error loc "incorrect alias type" ]
      in
      mktyp loc (Ptyp_alias (ctyp t) i)
  | TyAny loc -> mktyp loc Ptyp_any
  | TyApp loc _ _ as f ->
      let (f, al) = ctyp_fa [] f in
      let (is_cls, li) = ctyp_long_id f in
      if is_cls then mktyp loc (ocaml_ptyp_class li (List.map ctyp al) [])
      else mktyp loc (Ptyp_constr li (List.map ctyp al))
  | TyArr loc (TyLab loc1 lab t1) t2 ->
      mktyp loc (ocaml_ptyp_arrow (uv lab) (ctyp t1) (ctyp t2))
  | TyArr loc (TyOlb loc1 lab t1) t2 ->
      let t1 =
        let loc = loc1 in
        <:ctyp< option $t1$ >>
      in
      mktyp loc (ocaml_ptyp_arrow ("?" ^ uv lab) (ctyp t1) (ctyp t2))
  | TyArr loc t1 t2 -> mktyp loc (ocaml_ptyp_arrow "" (ctyp t1) (ctyp t2))
  | TyObj loc fl v -> mktyp loc (Ptyp_object (meth_list loc (uv fl) v))
  | TyCls loc id ->
      mktyp loc (ocaml_ptyp_class (long_id_of_string_list loc (uv id)) [] [])
  | TyLab loc _ _ -> error loc "labeled type not allowed here"
  | TyLid loc s -> mktyp loc (Ptyp_constr (Lident (uv s)) [])
  | TyMan loc _ _ -> error loc "type manifest not allowed here"
  | TyOlb loc lab _ -> error loc "labeled type not allowed here"
  | TyPck loc mt ->
      match ocaml_ptyp_package with
      [ Some ptyp_package ->
          let pt = package_of_module_type loc mt in
          mktyp loc (ptyp_package pt)
      | None -> error loc "no package type in this ocaml version" ]
  | TyPol loc pl t ->
       match ocaml_ptyp_poly with
       [ Some ptyp_poly -> mktyp loc (ptyp_poly (uv pl) (ctyp t))
       | None -> error loc "no poly types in that ocaml version" ]
  | TyQuo loc s -> mktyp loc (Ptyp_var (uv s))
  | TyRec loc _ -> error loc "record type not allowed here"
  | TySum loc _ -> error loc "sum type not allowed here"
  | TyTup loc tl -> mktyp loc (Ptyp_tuple (List.map ctyp (uv tl)))
  | TyUid loc s -> mktyp loc (Ptyp_constr (Lident (uv s)) [])
  | TyVrn loc catl ool ->
      let catl =
        List.map
          (fun
           [ PvTag c a t -> Left (uv c, uv a, List.map ctyp (uv t))
           | PvInh t -> Right (ctyp t) ])
          (uv catl)
      in
      let (clos, sl) =
        match ool with
        [ None -> (True, None)
        | Some None -> (False, None)
        | Some (Some sl) -> (True, Some (uv sl)) ]
      in
      match ocaml_ptyp_variant catl clos sl with
      [ Some t -> mktyp loc t
      | None -> error loc "no variant type or inherit in this ocaml version" ]
  | IFDEF STRICT THEN
      TyXtr loc _ _ -> error loc "bad ast TyXtr"
    END ]
and meth_list loc fl v =
  match fl with
  [ [] -> if uv v then [mkfield loc Pfield_var] else []
  | [(lab, t) :: fl] ->
      [mkfield loc (Pfield lab (add_polytype t)) :: meth_list loc fl v] ]
and add_polytype t =
  match ocaml_ptyp_poly with
  [ Some ptyp_poly ->
      match t with
      [ MLast.TyPol loc pl t -> mktyp loc (ptyp_poly (uv pl) (ctyp t))
      | _ ->
          let loc = MLast.loc_of_ctyp t in
          mktyp loc (ptyp_poly [] (ctyp t)) ]
  | None -> ctyp t ]
and package_of_module_type loc mt =
  let (mt, with_con) =
    match mt with
    [ <:module_type< $mt$ with $list:with_con$ >> ->
        let with_con =
          List.map
            (fun
             [ WcTyp loc id tpl pf ct -> do {
                 let li =
                   match uv id with
                   [ [id] -> id
                   | _ -> error loc "simple identifier expected" ]
                 in
                 if uv tpl <> [] then
                   error loc "no type parameters allowed here"
                 else ();
                 if uv pf then error loc "no 'private' allowed here" else ();
                 (li, ctyp ct)
               }
             | WcMod loc _ _ ->
                 error loc "package type with 'module' no allowed" ])
            with_con
        in
        (mt, with_con)
    | _ -> (mt, []) ]
  in
  let li = module_type_long_id mt in
  (li, with_con)
;

value variance_of_var =
  fun
  [ Some False -> (False, True)
  | Some True -> (True, False)
  | None -> (False, False) ]
;

value mktype loc tl cl tk pf tm =
  let (params, var_list) = List.split tl in
  let variance = List.map variance_of_var var_list in
  let params = List.map uv params in
  match ocaml_type_declaration params cl tk pf tm (mkloc loc) variance with
  [ Some td -> td
  | None -> error loc "no such type declaration in this ocaml version" ]
;

value mkmutable m = if m then Mutable else Immutable;
value mkprivate m = if m then Private else Public;

value mktrecord ltl priv =
  let ltl =
    List.map
      (fun (loc, n, m, t) ->
         let loc = mkloc loc in
         let m = mkmutable m in
         let t = add_polytype t in
         (n, m, t, loc))
      ltl
  in
  ocaml_ptype_record ltl priv
;

value mktvariant ctl priv =
  let ctl =
    List.map
      (fun (loc, c, tl) ->
         (conv_con (uv c), List.map ctyp (uv tl), mkloc loc))
      ctl
  in
  ocaml_ptype_variant ctl priv
;

value type_decl tl priv cl =
  fun
  [ TyMan loc t <:ctyp< { $list:ltl$ } >> ->
      mktype loc tl cl (mktrecord ltl priv) priv (Some (ctyp t))
  | TyMan loc t <:ctyp< [ $list:ctl$ ] >> ->
      mktype loc tl cl (mktvariant ctl priv) priv (Some (ctyp t))
  | TyRec loc ltl ->
      mktype loc tl cl (mktrecord (uv ltl) priv) priv None
  | TySum loc ctl ->
      mktype loc tl cl (mktvariant (uv ctl) priv) priv None
  | t ->
      let m =
        match t with
        [ <:ctyp< '$s$ >> ->
            if List.exists (fun (t, _) -> s = uv t) tl then Some (ctyp t)
            else None
        | _ -> Some (ctyp t) ]
      in
      mktype (loc_of_ctyp t) tl cl Ptype_abstract priv m ]
;

value mkvalue_desc t p = {pval_type = ctyp t; pval_prim = p};

value option f =
  fun
  [ Some x -> Some (f x)
  | None -> None ]
;

value expr_of_lab loc lab =
  fun
  [ Some e -> e
  | None -> <:expr< $lid:lab$ >> ]
;

value patt_of_lab loc lab =
  fun
  [ Some p -> p
  | None -> <:patt< $lid:lab$ >> ]
;

value paolab loc lab peoo =
  let lab =
    match (lab, peoo) with
    [ ("", Some (<:patt< $lid:i$ >>, _)) -> i
    | ("", Some (<:patt< ($lid:i$ : $_$) >>, _)) -> i
    | ("", _) -> error loc "bad ast"
    | _ -> lab ]
  in
  let (p, eo) =
    match peoo with
    [ Some (p, eo) -> (p, uv eo)
    | None -> (<:patt< $lid:lab$ >>, None) ]
  in
  (lab, p, eo)
;

value rec same_type_expr ct ce =
  match (ct, ce) with
  [ (<:ctyp< $lid:s1$ >>, <:expr< $lid:s2$ >>) -> s1 = s2
  | (<:ctyp< $uid:s1$ >>, <:expr< $uid:s2$ >>) -> s1 = s2
  | (<:ctyp< $t1$.$t2$ >>, <:expr< $e1$.$e2$ >>) ->
      same_type_expr t1 e1 && same_type_expr t2 e2
  | _ -> False ]
;

value rec common_id loc t e =
  match (t, e) with
  [ (<:ctyp< $lid:s1$ >>, <:expr< $lid:s2$ >>) when s1 = s2 -> Lident s1
  | (<:ctyp< $uid:s1$ >>, <:expr< $uid:s2$ >>) when s1 = s2 -> Lident s1
  | (<:ctyp< $t1$.$lid:s1$ >>, <:expr< $e1$.$lid:s2$ >>) when s1 = s2 ->
      Ldot (common_id loc t1 e1) s1
  | (<:ctyp< $t1$.$uid:s1$ >>, <:expr< $e1$.$uid:s2$ >>) when s1 = s2 ->
      Ldot (common_id loc t1 e1) s1
  | _ -> error loc "this expression should repeat the class id inherited" ]
;

value rec type_id loc t =
  match t with
  [ <:ctyp< $lid:s1$ >> -> Lident s1
  | <:ctyp< $uid:s1$ >> -> Lident s1
  | <:ctyp< $t1$.$lid:s1$ >> -> Ldot (type_id loc t1) s1
  | <:ctyp< $t1$.$uid:s1$ >> -> Ldot (type_id loc t1) s1
  | _ -> error loc "type identifier expected" ]
;

value rec module_expr_long_id =
  fun
  [ <:module_expr< $me1$ ( $me2$ ) >> ->
      Lapply (module_expr_long_id me1) (module_expr_long_id me2)
  | <:module_expr< $m$ . $uid:s$ >> -> Ldot (module_expr_long_id m) s
  | <:module_expr< $uid:s$ >> -> Lident s
  | t -> error (loc_of_module_expr t) "bad module expr long ident" ]
;

value mkwithc =
  fun
  [ WcTyp loc id tpl pf ct ->
      let (params, var_list) = List.split (uv tpl) in
      let variance = List.map variance_of_var var_list in
      let params = List.map uv params in
      let ct = Some (ctyp ct) in
      let tk = if uv pf then ocaml_ptype_abstract else Ptype_abstract in
      let pf = if uv pf then Private else Public in
      let li = long_id_of_string_list loc (uv id) in
      let wc =
       match
         ocaml_type_declaration params [] tk pf ct (mkloc loc) variance
       with
       [ Some td -> Pwith_type td
       | None -> error loc "no such with constraint in this ocaml version" ]
      in
      (li, wc)
  | WcMod loc id m ->
      (long_id_of_string_list loc (uv id),
       Pwith_module (module_expr_long_id m)) ]
;

value rec patt_fa al =
  fun
  [ PaApp _ f a -> patt_fa [a :: al] f
  | f -> (f, al) ]
;

value rec mkrangepat loc c1 c2 =
  if c1 > c2 then mkrangepat loc c2 c1
  else if c1 = c2 then mkpat loc (Ppat_constant (Const_char c1))
  else
    mkpat loc
      (Ppat_or (mkpat loc (Ppat_constant (Const_char c1)))
         (mkrangepat loc (Char.chr (Char.code c1 + 1)) c2))
;

value rec patt_long_id il =
  fun
  [ <:patt< $p$.$uid:i$ >> -> patt_long_id [i :: il] p
  | p -> (p, il) ]
;

value rec patt_label_long_id =
  fun
  [ <:patt< $m$.$lid:s$ >> -> Ldot (patt_label_long_id m) (conv_lab s)
  | <:patt< $m$.$uid:s$ >> -> Ldot (patt_label_long_id m) s
  | <:patt< $uid:s$ >> -> Lident s
  | <:patt< $lid:s$ >> -> Lident (conv_lab s)
  | p -> error (loc_of_patt p) "bad label" ]
;

value rec patt =
  fun
  [ PaAcc loc p1 p2 ->
      let p =
        match patt_long_id [] p1 with
        [ (<:patt< $uid:i$ >>, il) ->
            match p2 with
            [ <:patt< $uid:s$ >> ->
                Ppat_construct (mkli (conv_con s) [i :: il]) None
                  (not Prtools.no_constructors_arity.val)
            | _ -> error (loc_of_patt p2) "bad access pattern" ]
        | _ -> error (loc_of_patt p2) "bad pattern" ]
      in
      mkpat loc p
  | PaAli loc p1 p2 ->
      let (p, i) =
        match (p1, p2) with
        [ (p, <:patt< $lid:s$ >>) -> (p, s)
        | (<:patt< $lid:s$ >>, p) -> (p, s)
        | _ -> error loc "incorrect alias pattern" ]
      in
      mkpat loc (Ppat_alias (patt p) i)
  | PaAnt _ p -> patt p
  | PaAny loc -> mkpat loc Ppat_any
  | PaApp loc _ _ as f ->
      let (f, al) = patt_fa [] f in
      let al = List.map patt al in
      match (patt f).ppat_desc with
      [ Ppat_construct li None _ ->
          if Prtools.no_constructors_arity.val then
            let a =
              match al with
              [ [a] -> a
              | _ -> mkpat loc (Ppat_tuple al) ]
            in
            mkpat loc (Ppat_construct li (Some a) False)
          else
            let a = mkpat loc (Ppat_tuple al) in
            mkpat loc (Ppat_construct li (Some a) True)
      | p ->
          match ocaml_ppat_variant with
          [ Some (ppat_variant_pat, ppat_variant) ->
              match ppat_variant_pat p with
              [ Some (s, None) ->
                  let a =
                    match al with
                    [ [a] -> a
                    | _ -> mkpat loc (Ppat_tuple al) ]
                  in
                  mkpat loc (ppat_variant (s, Some a))
              | Some _ | None ->
                  error (loc_of_patt f)
                    ("this is not a constructor, " ^
                     "it cannot be applied in a pattern") ]
          | None ->
              error (loc_of_patt f)
                ("this is not a constructor, " ^
                 "it cannot be applied in a pattern") ] ]
  | PaArr loc pl ->
      match ocaml_ppat_array with
      [ Some ppat_array -> mkpat loc (ppat_array (List.map patt (uv pl)))
      | None -> error loc "no array patterns in this ocaml version" ]
  | PaChr loc s ->
      mkpat loc (Ppat_constant (Const_char (char_of_char_token loc (uv s))))
  | PaInt loc s "" ->
      mkpat loc (Ppat_constant (Const_int (int_of_string (uv s))))
  | PaInt loc _ _ -> error loc "special int not impl in patt"
  | PaFlo loc s -> mkpat loc (Ppat_constant (Const_float (uv s)))
  | PaLab loc _ _ -> error loc "labeled pattern not allowed here"
  | PaLaz loc p ->
      match ocaml_ppat_lazy with
      [ Some ppat_lazy -> mkpat loc (ppat_lazy (patt p))
      | None -> error loc "lazy patterns not in this version" ]
  | PaLid loc s -> mkpat loc (Ppat_var (uv s))
  | PaOlb loc _ _ -> error loc "labeled pattern not allowed here"
  | PaOrp loc p1 p2 -> mkpat loc (Ppat_or (patt p1) (patt p2))
  | PaRng loc p1 p2 ->
      match (p1, p2) with
      [ (PaChr loc1 c1, PaChr loc2 c2) ->
          let c1 = char_of_char_token loc1 (uv c1) in
          let c2 = char_of_char_token loc2 (uv c2) in
          mkrangepat loc c1 c2
      | _ -> error loc "range pattern allowed only for characters" ]
  | PaRec loc lpl ->
      mkpat loc (ocaml_ppat_record (List.map mklabpat (uv lpl)))
  | PaStr loc s ->
      mkpat loc
        (Ppat_constant (Const_string (string_of_string_token loc (uv s))))
  | PaTup loc pl -> mkpat loc (Ppat_tuple (List.map patt (uv pl)))
  | PaTyc loc p t -> mkpat loc (Ppat_constraint (patt p) (ctyp t))
  | PaTyp loc sl ->
      match ocaml_ppat_type with
      [ Some ppat_type ->
          mkpat loc (ppat_type (long_id_of_string_list loc (uv sl)))
      | None -> error loc "no #type in this ocaml version" ]
  | PaUid loc s ->
      let ca = not Prtools.no_constructors_arity.val in
      mkpat loc (Ppat_construct (Lident (conv_con (uv s))) None ca)
  | PaVrn loc s ->
      match ocaml_ppat_variant with
      [ Some (_, ppat_variant) -> mkpat loc (ppat_variant (uv s, None))
      | None -> error loc "no variant in this ocaml version" ]
  | IFDEF STRICT THEN
      PaXtr loc _ _ -> error loc "bad ast PaXtr"
    END ]
and mklabpat (lab, p) = (patt_label_long_id lab, patt p);

value rec expr_fa al =
  fun
  [ ExApp _ f a -> expr_fa [a :: al] f
  | f -> (f, al) ]
;

value rec class_expr_fa al =
  fun
  [ CeApp _ ce a -> class_expr_fa [a :: al] ce
  | ce -> (ce, al) ]
;

value rec sep_expr_acc l =
  fun
  [ <:expr< $e1$.$e2$ >> -> sep_expr_acc (sep_expr_acc l e2) e1
  | <:expr< $uid:s$ >> as e ->
      let loc = MLast.loc_of_expr e in
      match l with
      [ [] -> [(loc, [], e)]
      | [(loc2, sl, e) :: l] -> [(Ploc.encl loc loc2, [s :: sl], e) :: l] ]
  | e -> [(loc_of_expr e, [], e) :: l] ]
;

value class_info class_expr ci =
  let (params, var_list) = List.split (uv (snd ci.ciPrm)) in
  let variance = List.map variance_of_var var_list in
  match ocaml_class_infos with
  [ Some class_infos ->
      class_infos (if uv ci.ciVir then Virtual else Concrete)
        (List.map uv params, mkloc (fst ci.ciPrm)) (uv ci.ciNam)
        (class_expr ci.ciExp) (mkloc ci.ciLoc) variance
  | None -> error ci.ciLoc "no class_info in this ocaml version" ]
;

value bigarray_get loc e el =
  match el with
  [ [c1] -> <:expr< Bigarray.Array1.get $e$ $c1$ >>
  | [c1; c2] -> <:expr< Bigarray.Array2.get $e$ $c1$ $c2$ >>
  | [c1; c2; c3] -> <:expr< Bigarray.Array3.get $e$ $c1$ $c2$ $c3$ >>
  | _ -> <:expr< Bigarray.Genarray.get $e$ [| $list:el$ |] >> ]
;

value bigarray_set loc e el v =
  match el with
  [ [c1] -> <:expr< Bigarray.Array1.set $e$ $c1$ $v$ >>
  | [c1; c2] -> <:expr< Bigarray.Array2.set $e$ $c1$ $c2$ $v$ >>
  | [c1; c2; c3] -> <:expr< Bigarray.Array3.set $e$ $c1$ $c2$ $c3$ $v$ >>
  | _ -> <:expr< Bigarray.Genarray.set $e$ [| $list:el$ |] $v$ >> ]
;

value rec expr =
  fun
  [ ExAcc loc x <:expr< val >> ->
      mkexp loc
        (ocaml_pexp_apply (mkexp loc (Pexp_ident (Lident "!")))
           [("", expr x)])
  | ExAcc loc _ _ as e ->
      let (e, l) =
        match sep_expr_acc [] e with
        [ [(loc, ml, <:expr< $uid:s$ >>) :: l] ->
            let ca = not Prtools.no_constructors_arity.val in
            (mkexp loc (Pexp_construct (mkli s ml) None ca), l)
        | [(loc, ml, <:expr< $lid:s$ >>) :: l] ->
            (mkexp loc (Pexp_ident (mkli s ml)), l)
        | [(_, [], e) :: l] -> (expr e, l)
        | _ -> error loc "bad ast" ]
      in
      let (_, e) =
        List.fold_left
          (fun (loc1, e1) (loc2, ml, e2) ->
             match e2 with
             [ <:expr< $lid:s$ >> ->
                 let loc = Ploc.encl loc1 loc2 in
                 (loc, mkexp loc (Pexp_field e1 (mkli (conv_lab s) ml)))
             | _ -> error (loc_of_expr e2) "lowercase identifier expected" ])
          (loc, e) l
      in
      e
  | ExAnt _ e -> expr e
  | ExApp loc _ _ as f ->
      let (f, al) = expr_fa [] f in
      let al = List.map label_expr al in
      match (expr f).pexp_desc with
      [ Pexp_construct li None _ ->
          let al = List.map snd al in
          if Prtools.no_constructors_arity.val then
            let a =
              match al with
              [ [a] -> a
              | _ -> mkexp loc (Pexp_tuple al) ]
            in
            mkexp loc (Pexp_construct li (Some a) False)
          else
            let a = mkexp loc (Pexp_tuple al) in
            mkexp loc (Pexp_construct li (Some a) True)
      | e ->
          match ocaml_pexp_variant with
          [ Some (pexp_variant_pat, pexp_variant) ->
              match pexp_variant_pat e with
              [ Some (s, None) ->
                  let al = List.map snd al in
                  let a =
                    match al with
                    [ [a] -> a
                    | _ -> mkexp loc (Pexp_tuple al) ]
                  in
                  mkexp loc (pexp_variant (s, Some a))
              | Some _ | None ->
                  mkexp loc (ocaml_pexp_apply (expr f) al) ]
          | None -> mkexp loc (ocaml_pexp_apply (expr f) al) ] ]
  | ExAre loc e1 e2 ->
      match e1 with
      [ <:expr< $uid:m$ >> ->
          match ocaml_pexp_open with
          [ Some pexp_open ->
              let li = Lident m in
              mkexp loc (pexp_open li (expr e2))
          | None -> error loc "no expression open in this ocaml version" ]
      | _ ->
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc (Pexp_ident (array_function "Array" "get")))
               [("", expr e1); ("", expr e2)]) ]
  | ExArr loc el -> mkexp loc (Pexp_array (List.map expr (uv el)))
  | ExAss loc e v ->
      match e with
      [ ExAcc loc x <:expr< val >> ->
          mkexp loc
            (ocaml_pexp_apply (mkexp loc (Pexp_ident (Lident ":=")))
               [("", expr x); ("", expr v)])
      | ExAcc loc _ _ ->
          match (expr e).pexp_desc with
          [ Pexp_field e lab -> mkexp loc (Pexp_setfield e lab (expr v))
          | _ -> error loc "bad record access" ]
      | ExAre _ e1 e2 ->
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc (Pexp_ident (array_function "Array" "set")))
               [("", expr e1); ("", expr e2); ("", expr v)])
      | ExBae loc e el -> expr (bigarray_set loc e (uv el) v)
      | <:expr< $lid:lab$ >> -> mkexp loc (Pexp_setinstvar lab (expr v))
      | ExSte _ e1 e2 ->
          mkexp loc
            (ocaml_pexp_apply
               (mkexp loc (Pexp_ident (array_function "String" "set")))
               [("", expr e1); ("", expr e2); ("", expr v)])
      | _ -> error loc "bad left part of assignment" ]
  | ExAsr loc <:expr< False >> ->
      mkexp loc (ocaml_pexp_assertfalse glob_fname.val (mkloc loc))
  | ExAsr loc e ->
      mkexp loc (ocaml_pexp_assert glob_fname.val (mkloc loc) (expr e))
  | ExBae loc e el -> expr (bigarray_get loc e (uv el))
  | ExChr loc s ->
      mkexp loc (Pexp_constant (Const_char (char_of_char_token loc (uv s))))
  | ExCoe loc e t1 t2 ->
      mkexp loc (Pexp_constraint (expr e) (option ctyp t1) (Some (ctyp t2)))
  | ExFlo loc s -> mkexp loc (Pexp_constant (Const_float (uv s)))
  | ExFor loc i e1 e2 df el ->
      let e3 = <:expr< do { $list:uv el$ } >> in
      let df = if uv df then Upto else Downto in
      mkexp loc (Pexp_for (uv i) (expr e1) (expr e2) df (expr e3))
  | ExFun loc pel ->
      match uv pel with
      [ [(PaLab _ lab po, w, e)] ->
          mkexp loc
            (ocaml_pexp_function (uv lab) None
               [(patt (patt_of_lab loc (uv lab) po), when_expr e (uv w))])
      | [(PaOlb _ lab peoo, w, e)] ->
          let (lab, p, eo) = paolab loc (uv lab) peoo in
          mkexp loc
            (ocaml_pexp_function ("?" ^ lab) (option expr eo)
               [(patt p, when_expr e (uv w))])
      | pel ->
          let pel =
            if split_or_patterns_with_bindings then
              Prtools.do_split_or_patterns_with_bindings pel
            else pel
          in
          mkexp loc (ocaml_pexp_function "" None (List.map mkpwe pel)) ]
  | ExIfe loc e1 e2 e3 ->
      mkexp loc (Pexp_ifthenelse (expr e1) (expr e2) (Some (expr e3)))
  | ExInt loc s "" ->
      mkexp loc (Pexp_constant (Const_int (int_of_string (uv s))))
  | ExInt loc s "l" ->
      match ocaml_const_int32 with
      [ Some const_int32 -> mkexp loc (Pexp_constant (const_int32 (uv s)))
      | None -> error loc "no int32 in this ocaml version" ]
  | ExInt loc s "L" ->
      match ocaml_const_int64 with
      [ Some const_int64 -> mkexp loc (Pexp_constant (const_int64 (uv s)))
      | None -> error loc "no int64 in this ocaml version" ]
  | ExInt loc s "n" ->
      match ocaml_const_nativeint with
      [ Some const_nat -> mkexp loc (Pexp_constant (const_nat (uv s)))
      | None -> error loc "no nativeint in this ocaml version" ]
  | ExInt loc _ _ -> error loc "special int not implemented"
  | ExLab loc _ _ -> error loc "labeled expression not allowed here"
  | ExLaz loc e -> mklazy loc (expr e)
  | ExLet loc rf pel e ->
      mkexp loc (Pexp_let (mkrf (uv rf)) (List.map mkpe (uv pel)) (expr e))
  | ExLid loc s -> mkexp loc (Pexp_ident (Lident (uv s)))
  | ExLmd loc i me e ->
      match ocaml_pexp_letmodule with
      [ Some pexp_letmodule ->
          mkexp loc (pexp_letmodule (uv i) (module_expr me) (expr e))
      | None -> error loc "no 'let module' in this ocaml version" ]
  | ExMat loc e pel ->
      let pel = uv pel in
      let pel =
        if split_or_patterns_with_bindings then
          Prtools.do_split_or_patterns_with_bindings pel
        else pel
      in
      mkexp loc (Pexp_match (expr e) (List.map mkpwe pel))
  | ExNew loc id -> mkexp loc (Pexp_new (long_id_of_string_list loc (uv id)))
  | ExObj loc po cfl ->
      match ocaml_pexp_object with
      [ Some pexp_object ->
          let p =
            match uv po with
            [ Some p -> p
            | None -> PaAny loc ]
          in
          let cil = List.fold_right class_str_item (uv cfl) [] in
          mkexp loc (pexp_object (patt p, cil))
      | None -> error loc "no object in this ocaml version" ]
  | ExOlb loc _ _ -> error loc "labeled expression not allowed here"
  | ExOvr loc iel -> mkexp loc (Pexp_override (List.map mkideexp (uv iel)))
  | ExPck loc me mt ->
      match ocaml_pexp_pack with
      [ Some pexp_pack ->
          let pt = package_of_module_type loc mt in
          mkexp loc (pexp_pack (module_expr me) pt)
      | None -> error loc "no '(module ... : ...)' in this ocaml version" ]
  | ExRec loc lel eo ->
      let lel = uv lel in
      if lel = [] then error loc "empty record"
      else if eo <> None && not has_records_with_with then
        match eo with
        [ Some e ->
            match Prtools.record_without_with loc e lel with
            [ Some e -> expr e
            | None -> error loc "cannot convert record" ]
        | None -> assert False ]
      else
        let lel =
          if module_prefix_can_be_in_first_record_label_only then lel
          else do {
            match lel with
            [ [((PaAcc _ (PaUid _ m) _ as p), e) :: rest] ->
                Prtools.expand_module_prefix (uv m) [(p, e)] rest
            | _ -> lel ]
          }
        in
        let eo =
          match eo with
          [ Some e -> Some (expr e)
          | None -> None ]
        in
        mkexp loc (ocaml_pexp_record (List.map mklabexp lel) eo)
  | ExSeq loc el ->
      loop (uv el) where rec loop =
        fun
        [ [] -> expr <:expr< () >>
        | [e] -> expr e
        | [e :: el] ->
            let loc = Ploc.encl (loc_of_expr e) loc in
            mkexp loc (Pexp_sequence (expr e) (loop el)) ]
  | ExSnd loc e s -> mkexp loc (Pexp_send (expr e) (uv s))
  | ExSte loc e1 e2 ->
      mkexp loc
        (ocaml_pexp_apply
           (mkexp loc (Pexp_ident (array_function "String" "get")))
           [("", expr e1); ("", expr e2)])
  | ExStr loc s ->
      mkexp loc
        (Pexp_constant (Const_string (string_of_string_token loc (uv s))))
  | ExTry loc e pel -> mkexp loc (Pexp_try (expr e) (List.map mkpwe (uv pel)))
  | ExTup loc el -> mkexp loc (Pexp_tuple (List.map expr (uv el)))
  | ExTyc loc e t -> mkexp loc (Pexp_constraint (expr e) (Some (ctyp t)) None)
  | ExUid loc s ->
      let ca = not Prtools.no_constructors_arity.val in
      mkexp loc (Pexp_construct (Lident (conv_con (uv s))) None ca)
  | ExVrn loc s ->
      match ocaml_pexp_variant with
      [ Some (_, pexp_variant) -> mkexp loc (pexp_variant (uv s, None))
      | None -> error loc "no variants in this ocaml version" ]
  | ExWhi loc e1 el ->
      let e2 = <:expr< do { $list:uv el$ } >> in
      mkexp loc (Pexp_while (expr e1) (expr e2))
  | IFDEF STRICT THEN
      ExXtr loc _ _ -> error loc "bad ast ExXtr"
    END ]
and label_expr =
  fun
  [ ExLab loc lab eo -> (uv lab, expr (expr_of_lab loc (uv lab) eo))
  | ExOlb loc lab eo -> ("?" ^ uv lab, expr (expr_of_lab loc (uv lab) eo))
  | e -> ("", expr e) ]
and mkpe (p, e) = (patt p, expr e)
and mkpwe (p, w, e) = (patt p, when_expr e (uv w))
and when_expr e =
  fun
  [ Some w -> mkexp (loc_of_expr e) (Pexp_when (expr w) (expr e))
  | None -> expr e ]
and mklabexp (lab, e) = (patt_label_long_id lab, expr e)
and mkideexp (ide, e) = (ide, expr e)
and mktype_decl td =
  let priv = if uv td.tdPrv then Private else Public in
  let cl =
    List.map
      (fun (t1, t2) ->
         let loc = Ploc.encl (loc_of_ctyp t1) (loc_of_ctyp t2) in
         (ctyp t1, ctyp t2, mkloc loc))
      (uv td.tdCon)
  in
  (uv (snd (uv td.tdNam)), type_decl (uv td.tdPrm) priv cl td.tdDef)
and module_type =
  fun
  [ MtAcc loc _ _ as f -> mkmty loc (Pmty_ident (module_type_long_id f))
  | MtApp loc _ _ as f -> mkmty loc (Pmty_ident (module_type_long_id f))
  | MtFun loc n nt mt ->
      mkmty loc (Pmty_functor (uv n) (module_type nt) (module_type mt))
  | MtLid loc s -> mkmty loc (Pmty_ident (Lident (uv s)))
  | MtQuo loc _ -> error loc "abstract module type not allowed here"
  | MtSig loc sl ->
      mkmty loc (Pmty_signature (List.fold_right sig_item (uv sl) []))
  | MtTyo loc me ->
      match ocaml_pmty_typeof with
      [ Some pmty_typeof -> mkmty loc (pmty_typeof (module_expr me))
      | None -> error loc "no 'module type of ..' in this ocaml version" ]
  | MtUid loc s -> mkmty loc (Pmty_ident (Lident (uv s)))
  | MtWit loc mt wcl ->
      mkmty loc (Pmty_with (module_type mt) (List.map mkwithc (uv wcl)))
  | IFDEF STRICT THEN
      MtXtr loc _ _ -> error loc "bad ast MtXtr"
    END ]
and sig_item s l =
  match s with
  [ SgCls loc cd ->
      [mksig loc (Psig_class (List.map (class_info class_type) (uv cd))) :: l]
  | SgClt loc ctd ->
      match ocaml_psig_class_type with
      [ Some psig_class_type ->
          [mksig loc
             (psig_class_type (List.map (class_info class_type) (uv ctd)))
           :: l]
      | None -> error loc "no class type in this ocaml version" ]
  | SgDcl loc sl -> List.fold_right sig_item (uv sl) l
  | SgDir loc _ _ -> l
  | SgExc loc n tl ->
      [mksig loc (Psig_exception (uv n) (List.map ctyp (uv tl))) :: l]
  | SgExt loc n t p ->
      [mksig loc (Psig_value (uv n) (mkvalue_desc t (uv p))) :: l]
  | SgInc loc mt -> [mksig loc (Psig_include (module_type mt)) :: l]
  | SgMod loc rf ntl ->
      if not (uv rf) then
        List.fold_right
          (fun (n, mt) l ->
             [mksig loc (Psig_module (uv n) (module_type mt)) :: l])
          (uv ntl) l
      else
        match ocaml_psig_recmodule with
        [ Some psig_recmodule ->
            let ntl =
              List.map (fun (n, mt) -> (uv n, module_type mt)) (uv ntl)
            in
            [mksig loc (psig_recmodule ntl) :: l]
        | None -> error loc "no recursive module in this ocaml version" ]
  | SgMty loc n mt ->
      let si =
        match mt with
        [ MtQuo _ _ -> Pmodtype_abstract
        | _ -> Pmodtype_manifest (module_type mt) ]
      in
      [mksig loc (Psig_modtype (uv n) si) :: l]
  | SgOpn loc id ->
      [mksig loc (Psig_open (long_id_of_string_list loc (uv id))) :: l]
  | SgTyp loc tdl ->
      [mksig loc (Psig_type (List.map mktype_decl (uv tdl))) :: l]
  | SgUse loc fn sl ->
      Ploc.call_with glob_fname fn
        (fun () -> List.fold_right (fun (si, _) -> sig_item si) sl l) ()
  | SgVal loc n t ->
      [mksig loc (Psig_value (uv n) (mkvalue_desc t [])) :: l]
  | IFDEF STRICT THEN
      SgXtr loc _ _ -> error loc "bad ast SgXtr"
    END ]
and module_expr =
  fun
  [ MeAcc loc _ _ as f -> mkmod loc (Pmod_ident (module_expr_long_id f))
  | MeApp loc me1 me2 ->
      mkmod loc (Pmod_apply (module_expr me1) (module_expr me2))
  | MeFun loc n mt me ->
      mkmod loc (Pmod_functor (uv n) (module_type mt) (module_expr me))
  | MeStr loc sl ->
      mkmod loc (Pmod_structure (List.fold_right str_item (uv sl) []))
  | MeTyc loc me mt ->
      mkmod loc (Pmod_constraint (module_expr me) (module_type mt))
  | MeUid loc s -> mkmod loc (Pmod_ident (Lident (uv s)))
  | MeUnp loc e mt ->
      match ocaml_pmod_unpack with
      [ Some pmod_unpack ->
          let pt = package_of_module_type loc mt in
          mkmod loc (pmod_unpack (expr e) pt)
      | None -> error loc "no module unpack in this ocaml version" ]
  | IFDEF STRICT THEN
      MeXtr loc _ _ -> error loc "bad ast MeXtr"
    END ]
and str_item s l =
  match s with
  [ StCls loc cd ->
      [mkstr loc (Pstr_class (List.map (class_info class_expr) (uv cd))) :: l]
  | StClt loc ctd ->
      match ocaml_pstr_class_type with
      [ Some pstr_class_type ->
          [mkstr loc
             (pstr_class_type (List.map (class_info class_type) (uv ctd))) ::
             l]
      | None -> error loc "no class type in this ocaml version" ]
  | StDcl loc sl -> List.fold_right str_item (uv sl) l
  | StDir loc _ _ -> l
  | StExc loc n tl sl ->
      let si =
        match (uv tl, uv sl) with
        [ (tl, []) -> Pstr_exception (uv n) (List.map ctyp tl)
        | ([], sl) ->
            match ocaml_pstr_exn_rebind with
            [ Some pstr_exn_rebind ->
                pstr_exn_rebind (uv n) (long_id_of_string_list loc sl)
            | None ->
                error loc "no exception renaming in this ocaml version" ]
        | _ -> error loc "bad exception declaration" ]
      in
      [mkstr loc si :: l]
  | StExp loc e -> [mkstr loc (Pstr_eval (expr e)) :: l]
  | StExt loc n t p ->
      [mkstr loc (Pstr_primitive (uv n) (mkvalue_desc t (uv p))) :: l]
  | StInc loc me ->
      match ocaml_pstr_include with
      [ Some pstr_include -> [mkstr loc (pstr_include (module_expr me)) :: l]
      | None -> error loc "no include in this ocaml version" ]
  | StMod loc rf nel ->
      if not (uv rf) then
        List.fold_right
          (fun (n, me) l ->
             [mkstr loc (Pstr_module (uv n) (module_expr me)) :: l])
          (uv nel) l
      else
        match ocaml_pstr_recmodule with
        [ Some pstr_recmodule ->
            let nel =
              List.map
                (fun (n, me) ->
                   let (me, mt) =
                     match me with
                     [ MeTyc _ me mt -> (me, mt)
                     | _ ->
                         error (MLast.loc_of_module_expr me)
                           "module rec needs module types constraints" ]
                   in
                   (uv n, module_type mt, module_expr me))
                (uv nel)
            in
            [mkstr loc (pstr_recmodule nel) :: l]
        | None -> error loc "no recursive module in this ocaml version" ]
  | StMty loc n mt -> [mkstr loc (Pstr_modtype (uv n) (module_type mt)) :: l]
  | StOpn loc id ->
      [mkstr loc (Pstr_open (long_id_of_string_list loc (uv id))) :: l]
  | StTyp loc tdl ->
      [mkstr loc (Pstr_type (List.map mktype_decl (uv tdl))) :: l]
  | StUse loc fn sl ->
      Ploc.call_with glob_fname fn
        (fun () -> List.fold_right (fun (si, _) -> str_item si) sl l) ()
  | StVal loc rf pel ->
      [mkstr loc (Pstr_value (mkrf (uv rf)) (List.map mkpe (uv pel))) :: l]
  | IFDEF STRICT THEN
      StXtr loc _ _ -> error loc "bad ast StXtr"
    END ]
and class_type =
  fun
  [ CtAcc loc _ _ | CtApp loc _ _ | CtIde loc _ as ct ->
      let li =
        longident ct where rec longident =
          fun
          [ CtIde loc s -> Lident (uv s)
          | CtApp loc ct1 ct2 ->
              let li1 = longident ct1 in
              let li2 = longident ct2 in
              Lapply li1 li2
          | CtAcc loc ct1 ct2 ->
              let li1 = longident ct1 in
              let li2 = longident ct2 in
              Lapply li1 li2
          | _ -> failwith "CtAcc is not implemented 5" ]
      in
      match ocaml_pcty_constr with
      [ Some pcty_constr -> mkcty loc (pcty_constr li [])
      | None -> error loc "no class type desc in this ocaml version" ]
  | CtCon loc ct tl ->
      let li = failwith "CtCon not impl" in
      match ocaml_pcty_constr with
      [ Some pcty_constr -> mkcty loc (pcty_constr li (List.map ctyp (uv tl)))
      | None -> error loc "no class type desc in this ocaml version" ]
  | CtFun loc (TyLab _ lab t) ct ->
      match ocaml_pcty_fun with
      [ Some pcty_fun ->
          mkcty loc (pcty_fun (uv lab) (ctyp t) (class_type ct))
      | None -> error loc "no class type desc in this ocaml version" ]
  | CtFun loc (TyOlb loc1 lab t) ct ->
      match ocaml_pcty_fun with
      [ Some pcty_fun ->
          let t =
            let loc = loc1 in
            <:ctyp< option $t$ >>
          in
          mkcty loc (pcty_fun ("?" ^ uv lab) (ctyp t) (class_type ct))
      | None -> error loc "no class type desc in this ocaml version" ]
  | CtFun loc t ct ->
      match ocaml_pcty_fun with
      [ Some pcty_fun -> mkcty loc (pcty_fun "" (ctyp t) (class_type ct))
      | None -> error loc "no class type desc in this ocaml version" ]
  | CtSig loc t_o ctfl ->
      match ocaml_pcty_signature with
      [ Some pcty_signature ->
          let t =
            match uv t_o with
            [ Some t -> t
            | None -> TyAny loc ]
          in
          let cil = List.fold_right class_sig_item (uv ctfl) [] in
          mkcty loc (pcty_signature (ctyp t, cil))
      | None -> error loc "no class type desc in this ocaml version" ]
  | IFDEF STRICT THEN
      CtXtr loc _ _ -> error loc "bad ast CtXtr"
    END ]
and class_sig_item c l =
  match c with
  [ CgCtr loc t1 t2 ->
      match ocaml_pctf_cstr with
      [ Some pctf_cstr ->  [pctf_cstr (ctyp t1, ctyp t2, mkloc loc) :: l]
      | None -> error loc "no class constraint in this ocaml version" ]
  | CgDcl loc cl -> List.fold_right class_sig_item (uv cl) l
  | CgInh loc ct -> [Pctf_inher (class_type ct) :: l]
  | CgMth loc pf s t ->
      [Pctf_meth (uv s, mkprivate (uv pf), add_polytype t, mkloc loc) ::
       l]
  | CgVal loc b s t ->
      [ocaml_pctf_val (uv s, mkmutable (uv b), ctyp t, mkloc loc) :: l]
  | CgVir loc b s t ->
      [Pctf_virt (uv s, mkprivate (uv b), add_polytype t, mkloc loc) ::
       l] ]
and class_expr =
  fun
  [ CeApp loc _ _ as c ->
      match ocaml_pcl_apply with
      [ Some pcl_apply ->
          let (ce, el) = class_expr_fa [] c in
          let el = List.map label_expr el in
          mkpcl loc (pcl_apply (class_expr ce) el)
      | None -> error loc "no class expr desc in this ocaml version" ]
  | CeCon loc id tl ->
      match ocaml_pcl_constr with
      [ Some pcl_constr ->
          mkpcl loc
            (pcl_constr
               (long_id_of_string_list loc (uv id)) (List.map ctyp (uv tl)))
      | None -> error loc "no class expr desc in this ocaml version" ]
  | CeFun loc (PaLab _ lab po) ce ->
      match ocaml_pcl_fun with
      [ Some pcl_fun ->
          mkpcl loc
            (pcl_fun (uv lab) None
               (patt (patt_of_lab loc (uv lab) po)) (class_expr ce))
      | None -> error loc "no class expr desc in this ocaml version" ]
  | CeFun loc (PaOlb _ lab peoo) ce ->
      match ocaml_pcl_fun with
      [ Some pcl_fun ->
          let (lab, p, eo) = paolab loc (uv lab) peoo in
          mkpcl loc
            (pcl_fun ("?" ^ lab) (option expr eo) (patt p) (class_expr ce))
      | None -> error loc "no class expr desc in this ocaml version" ]
  | CeFun loc p ce ->
      match ocaml_pcl_fun with
      [ Some pcl_fun -> mkpcl loc (pcl_fun "" None (patt p) (class_expr ce))
      | None -> error loc "no class expr desc in this ocaml version" ]
  | CeLet loc rf pel ce ->
      match ocaml_pcl_let with
      [ Some pcl_let ->
          mkpcl loc
            (pcl_let (mkrf (uv rf)) (List.map mkpe (uv pel)) (class_expr ce))
      | None -> error loc "no class expr desc in this ocaml version" ]
  | CeStr loc po cfl ->
      match ocaml_pcl_structure with
      [ Some pcl_structure ->
          let p =
            match uv po with
            [ Some p -> p
            | None -> PaAny loc ]
          in
          let cil = List.fold_right class_str_item (uv cfl) [] in
          mkpcl loc (pcl_structure (patt p, cil))
      | None -> error loc "no class expr desc in this ocaml version" ]
  | CeTyc loc ce ct ->
      match ocaml_pcl_constraint with
      [ Some pcl_constraint ->
          mkpcl loc (pcl_constraint (class_expr ce) (class_type ct))
      | None -> error loc "no class expr desc in this ocaml version" ]
  | IFDEF STRICT THEN
      CeXtr loc _ _ -> error loc "bad ast CeXtr"
    END ]
and class_str_item c l =
  match c with
  [ CrCtr loc t1 t2 ->
      match ocaml_pcf_cstr with
      [ Some pcf_cstr -> [pcf_cstr (ctyp t1, ctyp t2, mkloc loc) :: l]
      | None -> error loc "no constraint in this ocaml version" ]
  | CrDcl loc cl -> List.fold_right class_str_item (uv cl) l
  | CrInh loc ce pb -> [ocaml_pcf_inher (class_expr ce) (uv pb) :: l]
  | CrIni loc e ->
      match ocaml_pcf_init with
      [ Some pcf_init -> [pcf_init (expr e) :: l]
      | None -> error loc "no initializer in this ocaml version" ]
  | CrMth loc ovf pf s ot e ->
      let e =
        match ocaml_pexp_poly with
        [ Some pexp_poly ->
            let t = option (fun t -> add_polytype t) (uv ot) in
            mkexp loc (pexp_poly (expr e) t)
        | None ->
            if uv ot = None then expr e
            else error loc "no method with label in this ocaml version" ]
      in
      [ocaml_pcf_meth (uv s, uv pf, uv ovf, e, mkloc loc) :: l]
  | CrVal loc ovf mf s e ->
      [ocaml_pcf_val (uv s, uv mf, uv ovf, expr e, mkloc loc) :: l]
  | CrVir loc b s t ->
      [Pcf_virt (uv s, mkprivate (uv b), add_polytype t, mkloc loc) :: l] ]
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
  [ None -> Pdir_none
  | Some <:expr< $str:s$ >> -> Pdir_string s
  | Some <:expr< $int:i$ >> -> Pdir_int (int_of_string i)
  | Some <:expr< True >> ->
      match ocaml_pdir_bool with
      [ Some pdir_bool -> pdir_bool True
      | None -> error loc "no such kind of directive in this ocaml version" ]
  | Some <:expr< False >> ->
      match ocaml_pdir_bool with
      [ Some pdir_bool -> pdir_bool False
      | None -> error loc "no such kind of directive in this ocaml version" ]
  | Some e ->
      let sl =
        loop e where rec loop =
          fun
          [ <:expr< $lid:i$ >> -> [i]
          | <:expr< $uid:i$ >> -> [i]
          | <:expr< $e$.$lid:i$ >> -> loop e @ [i]
          | <:expr< $e$.$uid:i$ >> -> loop e @ [i]
          | e -> Ploc.raise (loc_of_expr e) (Failure "bad ast") ]
      in
      Pdir_ident (long_id_of_string_list loc sl) ]
;

value phrase =
  fun
  [ StDir loc d dp -> Ptop_dir (uv d) (directive loc (uv dp))
  | si -> Ptop_def (str_item si []) ]
;
