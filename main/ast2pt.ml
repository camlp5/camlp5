(* camlp5r pa_macro.cmo *)
(* $Id: ast2pt.ml,v 1.73 2010/08/18 17:00:04 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

#load "q_MLast.cmo";

open MLast;
open Parsetree;
open Longident;
open Asttypes;

IFDEF
  OCAML_3_08_0 OR OCAML_3_08_1 OR OCAML_3_08_2 OR OCAML_3_08_3 OR OCAML_3_08_4
THEN
  DEFINE OCAML_3_08
END;

IFDEF
  OCAML_3_12_0 OR OCAML_3_12_1 OR OCAML_3_13_0
THEN
  DEFINE AFTER_OCAML_3_12
END;

IFDEF
  OCAML_3_11 OR OCAML_3_11_0 OR OCAML_3_11_1 OR OCAML_3_11_2 OR
  AFTER_OCAML_3_12
THEN
  DEFINE AFTER_OCAML_3_11
END;

IFDEF
  OCAML_3_10 OR OCAML_3_10_0 OR OCAML_3_10_1 OR OCAML_3_10_2 OR
  OCAML_3_10_3 OR AFTER_OCAML_3_11
THEN
  DEFINE AFTER_OCAML_3_10
END;

let ov = Sys.ocaml_version in
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
  Printf.eprintf "- OCaml version is %s\n" Sys.ocaml_version;
  Printf.eprintf "- Camlp5 compiled with ocaml %s\n" Pconfig.ocaml_version;
  Printf.eprintf "\n";
  Printf.eprintf "You need to recompile camlp5.\n";
  Printf.eprintf "\n";
  flush stderr;
  failwith "bad version"
}
else ();

value fast = ref False;
value no_constructors_arity = ref False;

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
  let lnum = Ploc.line_nb loc in
  let bolp = Ploc.bol_pos loc in
  let bp = Ploc.first_pos loc in
  let ep = Ploc.last_pos loc in
  let loc_at n =
    {Lexing.pos_fname = if lnum = -1 then "" else glob_fname.val;
     Lexing.pos_lnum = lnum; Lexing.pos_bol = bolp; Lexing.pos_cnum = n}
  in
  {Location.loc_start = loc_at bp; Location.loc_end = loc_at ep;
   Location.loc_ghost = bp = 0 && ep = 0}
;

value mktyp loc d = {ptyp_desc = d; ptyp_loc = mkloc loc};
value mkpat loc d = {ppat_desc = d; ppat_loc = mkloc loc};
value mkexp loc d = {pexp_desc = d; pexp_loc = mkloc loc};
value mkmty loc d = {pmty_desc = d; pmty_loc = mkloc loc};
value mksig loc d = {psig_desc = d; psig_loc = mkloc loc};
value mkmod loc d = {pmod_desc = d; pmod_loc = mkloc loc};
value mkstr loc d = {pstr_desc = d; pstr_loc = mkloc loc};
value mkfield loc d = {pfield_desc = d; pfield_loc = mkloc loc};
value mkcty loc d = {pcty_desc = d; pcty_loc = mkloc loc};
value mkpcl loc d = {pcl_desc = d; pcl_loc = mkloc loc};
value mkpolytype t =
  match t with
  [ <:ctyp< ! $list:_$ . $_$ >> -> t
  | _ ->
      let loc = MLast.loc_of_ctyp t in
      <:ctyp< ! $list:[]$ . $t$ >> ]
;

value lident s = Lident s;
value ldot l s = Ldot l s;

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
  ldot (lident str) (if fast.val then "unsafe_" ^ name else name)
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
  loop (fun s -> lident s) where rec loop f =
    fun
    [ [i :: il] -> loop (fun s -> ldot (f i) s) il
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
      (is_cls, ldot li s)
  | <:ctyp< $m$.$uid:s$ >> ->
      let (is_cls, li) = ctyp_long_id m in
      (is_cls, ldot li s)
  | <:ctyp< $m1$ $m2$ >> ->
      let (is_cls, li1) = ctyp_long_id m1 in
      let (_, li2) = ctyp_long_id m2 in
      (is_cls, Lapply li1 li2)
  | <:ctyp< $uid:s$ >> -> (False, lident s)
  | <:ctyp< $lid:s$ >> -> (False, lident s)
  | TyCls loc sl -> (True, long_id_of_string_list loc (uv sl))
  | t -> error (loc_of_ctyp t) "incorrect type" ]
;

value rec ctyp =
  fun
  [ TyAcc loc _ _ as f ->
      let (is_cls, li) = ctyp_long_id f in
      if is_cls then mktyp loc (Ptyp_class li [] [])
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
      if is_cls then mktyp loc (Ptyp_class li (List.map ctyp al) [])
      else mktyp loc (Ptyp_constr li (List.map ctyp al))
  | TyArr loc (TyLab loc1 lab t1) t2 ->
      mktyp loc (Ptyp_arrow (uv lab) (ctyp t1) (ctyp t2))
  | TyArr loc (TyOlb loc1 lab t1) t2 ->
      let t1 =
        let loc = loc1 in
        <:ctyp< option $t1$ >>
      in
      mktyp loc (Ptyp_arrow ("?" ^ uv lab) (ctyp t1) (ctyp t2))
  | TyArr loc t1 t2 -> mktyp loc (Ptyp_arrow "" (ctyp t1) (ctyp t2))
  | TyObj loc fl v -> mktyp loc (Ptyp_object (meth_list loc (uv fl) v))
  | TyCls loc id ->
      mktyp loc (Ptyp_class (long_id_of_string_list loc (uv id)) [] [])
  | TyLab loc _ _ -> error loc "labeled type not allowed here"
  | TyLid loc s -> mktyp loc (Ptyp_constr (lident (uv s)) [])
  | TyMan loc _ _ -> error loc "type manifest not allowed here"
  | TyOlb loc lab _ -> error loc "labeled type not allowed here"
  | TyPol loc pl t -> mktyp loc (Ptyp_poly (uv pl) (ctyp t))
  | TyQuo loc s -> mktyp loc (Ptyp_var (uv s))
  | TyRec loc _ -> error loc "record type not allowed here"
  | TySum loc _ -> error loc "sum type not allowed here"
  | TyTup loc tl -> mktyp loc (Ptyp_tuple (List.map ctyp (uv tl)))
  | TyUid loc s -> mktyp loc (Ptyp_constr (lident (uv s)) [])
  | TyVrn loc catl ool ->
      let catl =
        List.map
          (fun
           [ PvTag c a t -> Rtag (uv c) (uv a) (List.map ctyp (uv t))
           | PvInh t -> Rinherit (ctyp t) ])
          (uv catl)
      in
      let (clos, sl) =
        match ool with
        [ None -> (True, None)
        | Some None -> (False, None)
        | Some (Some sl) -> (True, Some (uv sl)) ]
      in
      mktyp loc (Ptyp_variant catl clos sl)
  | IFDEF STRICT THEN
      TyXtr loc _ _ -> error loc "bad ast TyXtr"
    END ]
and meth_list loc fl v =
  match fl with
  [ [] -> if uv v then [mkfield loc Pfield_var] else []
  | [(lab, t) :: fl] ->
      [mkfield loc (Pfield lab (ctyp (mkpolytype t))) :: meth_list loc fl v] ]
;

IFDEF AFTER_OCAML_3_11 THEN
  value mktype loc tl cl tk pf tm =
    let (params, variance) = List.split tl in
    {ptype_params = List.map uv params; ptype_cstrs = cl; ptype_kind = tk;
     ptype_private = pf; ptype_manifest = tm; ptype_loc = mkloc loc;
     ptype_variance = variance}
ELSE
  value mktype loc tl cl tk tm =
    let (params, variance) = List.split tl in
    {ptype_params = List.map uv params; ptype_cstrs = cl; ptype_kind = tk;
     ptype_manifest = tm; ptype_loc = mkloc loc; ptype_variance = variance}
END;
value mkmutable m = if m then Mutable else Immutable;
value mkprivate m = if m then Private else Public;
value mktrecord (loc, n, m, t) =
  IFDEF OCAML_3_08 THEN
    (n, mkmutable m, ctyp (mkpolytype t))
  ELSE
    (n, mkmutable m, ctyp (mkpolytype t), mkloc loc)
  END
;
value mkvariant (loc, c, tl) =
  IFDEF OCAML_3_08 THEN
    (conv_con (uv c), List.map ctyp (uv tl))
  ELSE
    (conv_con (uv c), List.map ctyp (uv tl), mkloc loc)
  END
;

value type_decl tl priv cl =
  fun
  [ TyMan loc t <:ctyp< { $list:ltl$ } >> ->
      IFDEF AFTER_OCAML_3_11 THEN
        mktype loc tl cl (Ptype_record (List.map mktrecord ltl)) priv
          (Some (ctyp t))
      ELSE
        mktype loc tl cl (Ptype_record (List.map mktrecord ltl) priv)
          (Some (ctyp t))
      END
  | TyMan loc t <:ctyp< [ $list:ctl$ ] >> ->
      IFDEF AFTER_OCAML_3_11 THEN
        mktype loc tl cl (Ptype_variant (List.map mkvariant ctl)) priv
          (Some (ctyp t))
      ELSE
        mktype loc tl cl (Ptype_variant (List.map mkvariant ctl) priv)
          (Some (ctyp t))
      END
  | TyRec loc ltl ->
      IFDEF AFTER_OCAML_3_11 THEN
        mktype loc tl cl (Ptype_record (List.map mktrecord (uv ltl))) priv
          None
      ELSE
        mktype loc tl cl (Ptype_record (List.map mktrecord (uv ltl)) priv)
          None
      END
  | TySum loc ctl ->
      IFDEF AFTER_OCAML_3_11 THEN
        mktype loc tl cl (Ptype_variant (List.map mkvariant (uv ctl))) priv
          None
      ELSE
        mktype loc tl cl (Ptype_variant (List.map mkvariant (uv ctl)) priv)
          None
      END
  | t ->
      let m =
        match t with
        [ <:ctyp< '$s$ >> ->
            if List.exists (fun (t, _) -> s = uv t) tl then Some (ctyp t)
            else None
        | _ -> Some (ctyp t) ]
      in
      IFDEF AFTER_OCAML_3_11 THEN
        mktype (loc_of_ctyp t) tl cl Ptype_abstract priv m
      ELSE
        mktype (loc_of_ctyp t) tl cl Ptype_abstract m
      END ]
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
    [ ("", Some (<:patt< $lid:i$ >> | <:patt< ($lid:i$ : $_$) >>, _)) -> i
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
  [ (<:ctyp< $lid:s1$ >>, <:expr< $lid:s2$ >>) when s1 = s2 -> lident s1
  | (<:ctyp< $uid:s1$ >>, <:expr< $uid:s2$ >>) when s1 = s2 -> lident s1
  | (<:ctyp< $t1$.$lid:s1$ >>, <:expr< $e1$.$lid:s2$ >>) when s1 = s2 ->
      ldot (common_id loc t1 e1) s1
  | (<:ctyp< $t1$.$uid:s1$ >>, <:expr< $e1$.$uid:s2$ >>) when s1 = s2 ->
      ldot (common_id loc t1 e1) s1
  | _ -> error loc "this expression should repeat the class id inherited" ]
;

value rec type_id loc t =
  match t with
  [ <:ctyp< $lid:s1$ >> -> lident s1
  | <:ctyp< $uid:s1$ >> -> lident s1
  | <:ctyp< $t1$.$lid:s1$ >> -> ldot (type_id loc t1) s1
  | <:ctyp< $t1$.$uid:s1$ >> -> ldot (type_id loc t1) s1
  | _ -> error loc "type identifier expected" ]
;

value rec module_type_long_id =
  fun
  [ <:module_type< $m$ . $uid:s$ >> -> ldot (module_type_long_id m) s
  | <:module_type< $m$ . $lid:s$ >> -> ldot (module_type_long_id m) s
  | MtApp _ m1 m2 -> Lapply (module_type_long_id m1) (module_type_long_id m2)
  | <:module_type< $lid:s$ >> -> lident s
  | <:module_type< $uid:s$ >> -> lident s
  | t -> error (loc_of_module_type t) "bad module type long ident" ]
;

value rec module_expr_long_id =
  fun
  [ <:module_expr< $m$ . $uid:s$ >> -> ldot (module_expr_long_id m) s
  | <:module_expr< $uid:s$ >> -> lident s
  | t -> error (loc_of_module_expr t) "bad module expr long ident" ]
;

value mkwithc =
  fun
  [ WcTyp loc id tpl pf ct ->
      let (params, variance) = List.split (uv tpl) in
      let tk =
        IFDEF OCAML_3_08 OR AFTER_OCAML_3_11 THEN Ptype_abstract
        ELSE if uv pf then Ptype_private else Ptype_abstract END
      in
      (long_id_of_string_list loc (uv id),
       IFDEF AFTER_OCAML_3_11 THEN
         let pf = if uv pf then Private else Public in
         Pwith_type
           {ptype_params = List.map uv params; ptype_cstrs = [];
            ptype_kind = tk; ptype_private = pf;
            ptype_manifest = Some (ctyp ct); ptype_loc = mkloc loc;
            ptype_variance = variance}
       ELSE
         Pwith_type
           {ptype_params = List.map uv params; ptype_cstrs = [];
            ptype_kind = tk; ptype_manifest = Some (ctyp ct);
            ptype_loc = mkloc loc; ptype_variance = variance}
       END)
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
  [ <:patt< $m$.$lid:s$ >> -> ldot (patt_label_long_id m) (conv_lab s)
  | <:patt< $m$.$uid:s$ >> -> ldot (patt_label_long_id m) s
  | <:patt< $uid:s$ >> -> lident s
  | <:patt< $lid:s$ >> -> lident (conv_lab s)
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
                  (not no_constructors_arity.val)
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
          if no_constructors_arity.val then
            let a =
              match al with
              [ [a] -> a
              | _ -> mkpat loc (Ppat_tuple al) ]
            in
            mkpat loc (Ppat_construct li (Some a) False)
          else
            let a = mkpat loc (Ppat_tuple al) in
            mkpat loc (Ppat_construct li (Some a) True)
      | Ppat_variant s None ->
          let a =
            match al with
            [ [a] -> a
            | _ -> mkpat loc (Ppat_tuple al) ]
          in
          mkpat loc (Ppat_variant s (Some a))
      | _ ->
          error (loc_of_patt f)
            "this is not a constructor, it cannot be applied in a pattern" ]
  | PaArr loc pl -> mkpat loc (Ppat_array (List.map patt (uv pl)))
  | PaChr loc s ->
      mkpat loc (Ppat_constant (Const_char (char_of_char_token loc (uv s))))
  | PaInt loc s "" ->
      mkpat loc (Ppat_constant (Const_int (int_of_string (uv s))))
  | PaInt loc _ _ -> error loc "special int not impl in patt"
  | PaFlo loc s -> mkpat loc (Ppat_constant (Const_float (uv s)))
  | PaLab loc _ _ -> error loc "labeled pattern not allowed here"
  | PaLaz loc p ->
      IFDEF AFTER_OCAML_3_11 THEN
        mkpat loc (Ppat_lazy (patt p))
      ELSE
        error loc "lazy patterns not in this version"
      END
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
      IFDEF AFTER_OCAML_3_12 THEN
        mkpat loc (Ppat_record (List.map mklabpat (uv lpl)) Closed)
      ELSE
        mkpat loc (Ppat_record (List.map mklabpat (uv lpl)))
      END
  | PaStr loc s ->
      mkpat loc
        (Ppat_constant (Const_string (string_of_string_token loc (uv s))))
  | PaTup loc pl -> mkpat loc (Ppat_tuple (List.map patt (uv pl)))
  | PaTyc loc p t -> mkpat loc (Ppat_constraint (patt p) (ctyp t))
  | PaTyp loc sl -> mkpat loc (Ppat_type (long_id_of_string_list loc (uv sl)))
  | PaUid loc s ->
      let ca = not no_constructors_arity.val in
      mkpat loc (Ppat_construct (lident (conv_con (uv s))) None ca)
  | PaVrn loc s -> mkpat loc (Ppat_variant (uv s) None)
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
  let (params, variance) = List.split (uv (snd ci.ciPrm)) in
  {pci_virt = if uv ci.ciVir then Virtual else Concrete;
   pci_params = (List.map uv params, mkloc (fst ci.ciPrm));
   pci_name = uv ci.ciNam; pci_expr = class_expr ci.ciExp;
   pci_loc = mkloc ci.ciLoc; pci_variance = variance}
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
        (Pexp_apply (mkexp loc (Pexp_ident (Lident "!"))) [("", expr x)])
  | ExAcc loc _ _ as e ->
      let (e, l) =
        match sep_expr_acc [] e with
        [ [(loc, ml, <:expr< $uid:s$ >>) :: l] ->
            let ca = not no_constructors_arity.val in
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
          if no_constructors_arity.val then
            let a =
              match al with
              [ [a] -> a
              | _ -> mkexp loc (Pexp_tuple al) ]
            in
            mkexp loc (Pexp_construct li (Some a) False)
          else
            let a = mkexp loc (Pexp_tuple al) in
            mkexp loc (Pexp_construct li (Some a) True)
      | Pexp_variant s None ->
          let al = List.map snd al in
          let a =
            match al with
            [ [a] -> a
            | _ -> mkexp loc (Pexp_tuple al) ]
          in
          mkexp loc (Pexp_variant s (Some a))
      | _ -> mkexp loc (Pexp_apply (expr f) al) ]
  | ExAre loc e1 e2 ->
      mkexp loc
        (Pexp_apply (mkexp loc (Pexp_ident (array_function "Array" "get")))
           [("", expr e1); ("", expr e2)])
  | ExArr loc el -> mkexp loc (Pexp_array (List.map expr (uv el)))
  | ExAss loc e v ->
      match e with
      [ ExAcc loc x <:expr< val >> ->
          mkexp loc
            (Pexp_apply (mkexp loc (Pexp_ident (Lident ":=")))
               [("", expr x); ("", expr v)])
      | ExAcc loc _ _ ->
          match (expr e).pexp_desc with
          [ Pexp_field e lab -> mkexp loc (Pexp_setfield e lab (expr v))
          | _ -> error loc "bad record access" ]
      | ExAre _ e1 e2 ->
          mkexp loc
            (Pexp_apply
               (mkexp loc (Pexp_ident (array_function "Array" "set")))
               [("", expr e1); ("", expr e2); ("", expr v)])
      | ExBae loc e el -> expr (bigarray_set loc e (uv el) v)
      | <:expr< $lid:lab$ >> -> mkexp loc (Pexp_setinstvar lab (expr v))
      | ExSte _ e1 e2 ->
          mkexp loc
            (Pexp_apply
               (mkexp loc (Pexp_ident (array_function "String" "set")))
               [("", expr e1); ("", expr e2); ("", expr v)])
      | _ -> error loc "bad left part of assignment" ]
  | ExAsr loc <:expr< False >> -> mkexp loc Pexp_assertfalse
  | ExAsr loc e -> mkexp loc (Pexp_assert (expr e))
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
            (Pexp_function (uv lab) None
               [(patt (patt_of_lab loc (uv lab) po), when_expr e (uv w))])
      | [(PaOlb _ lab peoo, w, e)] ->
          let (lab, p, eo) = paolab loc (uv lab) peoo in
          mkexp loc
            (Pexp_function ("?" ^ lab) (option expr eo)
               [(patt p, when_expr e (uv w))])
      | pel -> mkexp loc (Pexp_function "" None (List.map mkpwe pel)) ]
  | ExIfe loc e1 e2 e3 ->
      mkexp loc (Pexp_ifthenelse (expr e1) (expr e2) (Some (expr e3)))
  | ExInt loc s "" ->
      mkexp loc (Pexp_constant (Const_int (int_of_string (uv s))))
  | ExInt loc s "l" ->
      mkexp loc (Pexp_constant (Const_int32 (Int32.of_string (uv s))))
  | ExInt loc s "L" ->
      mkexp loc (Pexp_constant (Const_int64 (Int64.of_string (uv s))))
  | ExInt loc s "n" ->
      mkexp loc (Pexp_constant (Const_nativeint (Nativeint.of_string (uv s))))
  | ExInt loc _ _ -> error loc "special int not implemented"
  | ExLab loc _ _ -> error loc "labeled expression not allowed here"
  | ExLaz loc e -> mkexp loc (Pexp_lazy (expr e))
  | ExLet loc rf pel e ->
      mkexp loc (Pexp_let (mkrf (uv rf)) (List.map mkpe (uv pel)) (expr e))
  | ExLid loc s -> mkexp loc (Pexp_ident (lident (uv s)))
  | ExLmd loc i me e ->
      mkexp loc (Pexp_letmodule (uv i) (module_expr me) (expr e))
  | ExMat loc e pel ->
      mkexp loc (Pexp_match (expr e) (List.map mkpwe (uv pel)))
  | ExNew loc id -> mkexp loc (Pexp_new (long_id_of_string_list loc (uv id)))
  | ExObj loc po cfl ->
      let p =
        match uv po with
        [ Some p -> p
        | None -> PaAny loc ]
      in
      let cil = List.fold_right class_str_item (uv cfl) [] in
      mkexp loc (Pexp_object (patt p, cil))
  | ExOlb loc _ _ -> error loc "labeled expression not allowed here"
  | ExOvr loc iel -> mkexp loc (Pexp_override (List.map mkideexp (uv iel)))
  | ExRec loc lel eo ->
      let lel = uv lel in
      if lel = [] then error loc "empty record"
      else
        let eo =
          match eo with
          [ Some e -> Some (expr e)
          | None -> None ]
        in
        mkexp loc (Pexp_record (List.map mklabexp lel) eo)
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
        (Pexp_apply (mkexp loc (Pexp_ident (array_function "String" "get")))
           [("", expr e1); ("", expr e2)])
  | ExStr loc s ->
      mkexp loc
        (Pexp_constant (Const_string (string_of_string_token loc (uv s))))
  | ExTry loc e pel -> mkexp loc (Pexp_try (expr e) (List.map mkpwe (uv pel)))
  | ExTup loc el -> mkexp loc (Pexp_tuple (List.map expr (uv el)))
  | ExTyc loc e t -> mkexp loc (Pexp_constraint (expr e) (Some (ctyp t)) None)
  | ExUid loc s ->
      let ca = not no_constructors_arity.val in
      mkexp loc (Pexp_construct (lident (conv_con (uv s))) None ca)
  | ExVrn loc s -> mkexp loc (Pexp_variant (uv s) None)
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
  (uv (snd td.tdNam), type_decl (uv td.tdPrm) priv cl td.tdDef)
and module_type =
  fun
  [ MtAcc loc _ _ as f -> mkmty loc (Pmty_ident (module_type_long_id f))
  | MtApp loc _ _ as f -> mkmty loc (Pmty_ident (module_type_long_id f))
  | MtFun loc n nt mt ->
      mkmty loc (Pmty_functor (uv n) (module_type nt) (module_type mt))
  | MtLid loc s -> mkmty loc (Pmty_ident (lident (uv s)))
  | MtQuo loc _ -> error loc "abstract module type not allowed here"
  | MtSig loc sl ->
      mkmty loc (Pmty_signature (List.fold_right sig_item (uv sl) []))
  | MtUid loc s -> mkmty loc (Pmty_ident (lident (uv s)))
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
      [mksig loc (Psig_class_type (List.map (class_info class_type) (uv ctd)))
       :: l]
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
        let ntl = List.map (fun (n, mt) -> (uv n, module_type mt)) (uv ntl) in
        [mksig loc (Psig_recmodule ntl) :: l]
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
  | MeUid loc s -> mkmod loc (Pmod_ident (lident (uv s)))
  | IFDEF STRICT THEN
      MeXtr loc _ _ -> error loc "bad ast MeXtr"
    END ]
and str_item s l =
  match s with
  [ StCls loc cd ->
      [mkstr loc (Pstr_class (List.map (class_info class_expr) (uv cd))) :: l]
  | StClt loc ctd ->
      [mkstr loc
         (Pstr_class_type (List.map (class_info class_type) (uv ctd))) ::
       l]
  | StDcl loc sl -> List.fold_right str_item (uv sl) l
  | StDir loc _ _ -> l
  | StExc loc n tl sl ->
      let si =
        match (uv tl, uv sl) with
        [ (tl, []) -> Pstr_exception (uv n) (List.map ctyp tl)
        | ([], sl) -> Pstr_exn_rebind (uv n) (long_id_of_string_list loc sl)
        | _ -> error loc "bad exception declaration" ]
      in
      [mkstr loc si :: l]
  | StExp loc e -> [mkstr loc (Pstr_eval (expr e)) :: l]
  | StExt loc n t p ->
      [mkstr loc (Pstr_primitive (uv n) (mkvalue_desc t (uv p))) :: l]
  | StInc loc me -> [mkstr loc (Pstr_include (module_expr me)) :: l]
  | StMod loc rf nel ->
      if not (uv rf) then
        List.fold_right
          (fun (n, me) l ->
             [mkstr loc (Pstr_module (uv n) (module_expr me)) :: l])
          (uv nel) l
      else
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
        [mkstr loc (Pstr_recmodule nel) :: l]
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
  [ CtCon loc id tl ->
      mkcty loc
        (Pcty_constr (long_id_of_string_list loc (uv id))
           (List.map ctyp (uv tl)))
  | CtFun loc (TyLab _ lab t) ct ->
      mkcty loc (Pcty_fun (uv lab) (ctyp t) (class_type ct))
  | CtFun loc (TyOlb loc1 lab t) ct ->
      let t =
        let loc = loc1 in
        <:ctyp< option $t$ >>
      in
      mkcty loc (Pcty_fun ("?" ^ uv lab) (ctyp t) (class_type ct))
  | CtFun loc t ct -> mkcty loc (Pcty_fun "" (ctyp t) (class_type ct))
  | CtSig loc t_o ctfl ->
      let t =
        match uv t_o with
        [ Some t -> t
        | None -> TyAny loc ]
      in
      let cil = List.fold_right class_sig_item (uv ctfl) [] in
      mkcty loc (Pcty_signature (ctyp t, cil))
  | IFDEF STRICT THEN
      CtXtr loc _ _ -> error loc "bad ast CtXtr"
    END ]
and class_sig_item c l =
  match c with
  [ CgCtr loc t1 t2 -> [Pctf_cstr (ctyp t1, ctyp t2, mkloc loc) :: l]
  | CgDcl loc cl -> List.fold_right class_sig_item (uv cl) l
  | CgInh loc ct -> [Pctf_inher (class_type ct) :: l]
  | CgMth loc s pf t ->
      [Pctf_meth (uv s, mkprivate (uv pf), ctyp (mkpolytype t), mkloc loc) ::
       l]
  | CgVal loc s b t ->
      IFDEF AFTER_OCAML_3_10 THEN
        [Pctf_val (uv s, mkmutable (uv b), Concrete, ctyp t, mkloc loc) :: l]
      ELSE
        [Pctf_val (uv s, mkmutable (uv b), Some (ctyp t), mkloc loc) :: l]
      END
  | CgVir loc s b t ->
      [Pctf_virt (uv s, mkprivate (uv b), ctyp (mkpolytype t), mkloc loc) ::
       l] ]
and class_expr =
  fun
  [ CeApp loc _ _ as c ->
      let (ce, el) = class_expr_fa [] c in
      let el = List.map label_expr el in
      mkpcl loc (Pcl_apply (class_expr ce) el)
  | CeCon loc id tl ->
      mkpcl loc
        (Pcl_constr (long_id_of_string_list loc (uv id))
           (List.map ctyp (uv tl)))
  | CeFun loc (PaLab _ lab po) ce ->
      mkpcl loc
        (Pcl_fun (uv lab) None (patt (patt_of_lab loc (uv lab) po))
           (class_expr ce))
  | CeFun loc (PaOlb _ lab peoo) ce ->
      let (lab, p, eo) = paolab loc (uv lab) peoo in
      mkpcl loc
        (Pcl_fun ("?" ^ lab) (option expr eo) (patt p) (class_expr ce))
  | CeFun loc p ce -> mkpcl loc (Pcl_fun "" None (patt p) (class_expr ce))
  | CeLet loc rf pel ce ->
      mkpcl loc (Pcl_let (mkrf (uv rf)) (List.map mkpe (uv pel))
        (class_expr ce))
  | CeStr loc po cfl ->
      let p =
        match uv po with
        [ Some p -> p
        | None -> PaAny loc ]
      in
      let cil = List.fold_right class_str_item (uv cfl) [] in
      mkpcl loc (Pcl_structure (patt p, cil))
  | CeTyc loc ce ct ->
      mkpcl loc (Pcl_constraint (class_expr ce) (class_type ct))
  | IFDEF STRICT THEN
      CeXtr loc _ _ -> error loc "bad ast CeXtr"
    END ]
and class_str_item c l =
  match c with
  [ CrCtr loc t1 t2 -> [Pcf_cstr (ctyp t1, ctyp t2, mkloc loc) :: l]
  | CrDcl loc cl -> List.fold_right class_str_item (uv cl) l
  | IFDEF AFTER_OCAML_3_12 THEN
      CrInh loc ce pb -> [Pcf_inher Fresh (class_expr ce) (uv pb) :: l]
    ELSE
      CrInh loc ce pb -> [Pcf_inher (class_expr ce) (uv pb) :: l]
    END
  | CrIni loc e -> [Pcf_init (expr e) :: l]
  | CrMth loc s b e t ->
      let t = option (fun t -> ctyp (mkpolytype t)) (uv t) in
      let e = mkexp loc (Pexp_poly (expr e) t) in
      IFDEF AFTER_OCAML_3_12 THEN
        [Pcf_meth (uv s, mkprivate (uv b), Fresh, e, mkloc loc) :: l]
      ELSE
        [Pcf_meth (uv s, mkprivate (uv b), e, mkloc loc) :: l]
      END
  | CrVal loc s b e ->
      IFDEF AFTER_OCAML_3_12 THEN
        [Pcf_val (uv s, mkmutable (uv b), Fresh, expr e, mkloc loc) :: l]
      ELSE
        [Pcf_val (uv s, mkmutable (uv b), expr e, mkloc loc) :: l]
      END
  | CrVir loc s b t ->
      [Pcf_virt (uv s, mkprivate (uv b), ctyp (mkpolytype t), mkloc loc) ::
         l] ]
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
  | Some <:expr< True >> -> Pdir_bool True
  | Some <:expr< False >> -> Pdir_bool False
  | Some e ->
      let sl =
        loop e where rec loop =
          fun
          [ <:expr< $lid:i$ >> | <:expr< $uid:i$ >> -> [i]
          | <:expr< $e$.$lid:i$ >> | <:expr< $e$.$uid:i$ >> ->
              loop e @ [i]
          | e -> Ploc.raise (loc_of_expr e) (Failure "bad ast") ]
      in
      Pdir_ident (long_id_of_string_list loc sl) ]
;

value phrase =
  fun
  [ StDir loc d dp -> Ptop_dir (uv d) (directive loc (uv dp))
  | si -> Ptop_def (str_item si []) ]
;
