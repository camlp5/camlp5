(* camlp5r *)
(* pa_passthru.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";
#load "pa_extfun.cmo";

open Asttools;
open MLast;
open Pa_passthru ;
open Ppxutil ;

value eq_fname arg tyname =
  if tyname = "t" then "equal"
  else "equal_"^tyname
;

value fmt_expression arg param_map ty0 =
  let rec fmtrec = fun [
    <:ctyp:< _ >> -> <:expr< fun a b -> True >>
  | <:ctyp:< unit >> -> <:expr< fun a b -> True >>
  | <:ctyp:< int >> -> <:expr< fun a b -> a=b >>
  | <:ctyp:< int32 >> -> <:expr< fun a b -> a=b >>
  | <:ctyp:< int64 >> -> <:expr< fun a b -> a=b >>
  | <:ctyp:< nativeint >> -> <:expr< fun a b -> a=b >>
  | <:ctyp:< float >> -> <:expr< fun a b -> a=b >>
  | <:ctyp:< bool >> -> <:expr< fun a b -> a=b >>
  | <:ctyp:< char >> -> <:expr< fun a b -> a=b >>
  | <:ctyp:< string >> -> <:expr< fun a b -> a=b >>
  | <:ctyp:< bytes >> -> <:expr< fun a b -> a=b >>

  | <:ctyp:< $t$ [@equal $exp:e$ ;] >> -> e

  | <:ctyp:< list $ty$ >> ->
  let fmt1 = fmtrec ty in
  <:expr< let rec loop x y =
        match (x, y) with [
          ([], []) -> true
        | ([a::x], [b::y]) ->
            ($fmt1$ a b) && (loop x y)
        | _ -> False ] in
      fun x y -> loop x y >>

  | <:ctyp:< array $ty$ >> ->
  let fmt1 = fmtrec ty in
  <:expr< fun x ->
        fun y ->
          let rec loop i =
            (i = (Array.length x)) ||
              (($fmt1$ (x.(i)) (y.(i))) &&
                 (loop (i + 1))) in
          ((Array.length x) = (Array.length y)) && (loop 0) >>

  | (<:ctyp:< ref $ty$ >> | <:ctyp:< Pervasives.ref $ty$ >>) ->
    let fmt1 = fmtrec ty in
    <:expr< fun a b -> $fmt1$ a.val b.val >>

  | <:ctyp:< lazy_t $ty$ >> ->
    let fmt1 = fmtrec ty in
    <:expr< fun [ lazy x -> fun [ lazy y  -> $fmt1$ x y ] ] >>

  | <:ctyp:< option $ty$ >> ->
    let fmt1 = fmtrec ty in
    <:expr< fun x ->
        fun y ->
          match (x, y) with [
            (None, None) -> true
          | (Some a, Some b) -> $fmt1$ a b
          | _ -> False ] >>

| (<:ctyp:< result $ty1$ $ty2$ >> | <:ctyp:< Result.result $ty1$ $ty2$ >>) ->
  <:expr< fun a b -> match (a,b) with [
          (Result.Ok a, Result.Ok b) -> $(fmtrec ty1)$ a b
        | (Result.Error a, Result.Error b) -> $(fmtrec ty2)$ a b
        | _ -> False
      ] >>

| <:ctyp:< $t1$ $t2$ >> -> <:expr< $fmtrec t1$ $fmtrec t2$ >>

| <:ctyp:< '$i$ >> ->
  let fmtf = match List.assoc i param_map with [
    x -> x | exception Not_found -> failwith "pa_deriving.eq: unrecognized param-var in type-decl"
  ] in
  <:expr< $lid:fmtf$ >>

| <:ctyp:< $lid:lid$ [@nobuiltin] >> ->
  let fname = eq_fname arg lid in
  <:expr< $lid:fname$ >>

| <:ctyp:< $lid:lid$ >> ->
  let fname = eq_fname arg lid in
  <:expr< $lid:fname$ >>
| <:ctyp:< $longid:li$ . $lid:lid$ >> ->
  let fname = eq_fname arg lid in
  Expr.prepend_longident li <:expr< $lid:fname$ >>

| <:ctyp:< ( $list:tyl$ ) >> ->
    let vars_fmts = List.mapi (fun i ty ->
        (Printf.sprintf "a_%d" i, Printf.sprintf "b_%d" i, fmtrec ty)) tyl in

    let var1pats = List.map (fun (v, _, _) -> <:patt< $lid:v$ >>) vars_fmts in
    let var2pats = List.map (fun (_, v, _) -> <:patt< $lid:v$ >>) vars_fmts in

    let fldcmps = List.map (fun (v1, v2, fmtf) -> <:expr< $fmtf$ $lid:v1$ $lid:v2$ >>) vars_fmts in
    let cmpexp = match fldcmps with [
      [h::t] -> List.fold_left (fun e1 e2 -> <:expr< $e1$ && $e2$ >>) h t
    | [] -> assert False ] in

    <:expr< fun ( $list:var1pats$ ) ( $list:var2pats$ ) -> $cmpexp$ >>

| <:ctyp:< [ $list:l$ ] >> ->
  let branches = List.map (fun [
    (loc, cid, <:vala< [TyRec _ fields] >>, None, _) ->
    let cid = Pcaml.unvala cid in
    let (rec1pat, rec2pat, body) = fmt_record loc arg (Pcaml.unvala fields) in

    let conspat = <:patt< ($uid:cid$ $rec1pat$, $uid:cid$ $rec2pat$) >> in
    (conspat, <:vala< None >>, body)

  | (loc, cid, tyl, None, attrs) ->
    let cid = Pcaml.unvala cid in
    let tyl = Pcaml.unvala tyl in
    let vars_fmts = List.mapi (fun i ty ->
        (Printf.sprintf "a_%d" i, Printf.sprintf "b_%d" i, fmtrec ty)) tyl in

    let var1pats = List.map (fun (v, _, _) -> <:patt< $lid:v$ >>) vars_fmts in
    let cons1pat = List.fold_left (fun p vp -> <:patt< $p$ $vp$ >>)
        <:patt< $uid:cid$ >> var1pats in
    let var2pats = List.map (fun (_, v, _) -> <:patt< $lid:v$ >>) vars_fmts in
    let cons2pat = List.fold_left (fun p vp -> <:patt< $p$ $vp$ >>)
        <:patt< $uid:cid$ >> var2pats in
    let conspat = <:patt< ($cons1pat$, $cons2pat$) >> in
    
    let fldcmps = List.map (fun (v1, v2, fmtf) -> <:expr< $fmtf$ $lid:v1$ $lid:v2$ >>) vars_fmts in
    let cmpexp = match fldcmps with [
      [h::t] -> List.fold_left (fun e1 e2 -> <:expr< $e1$ && $e2$ >>) h t
    | [] -> <:expr< True >> ] in

    (conspat, <:vala< None >>, cmpexp)

  | (_, _, _, Some _, _) -> assert False
  ]) l in
  let branches = branches @ [ (<:patt< _ >>, <:vala< None >>, <:expr< False >>) ] in
  <:expr< fun a b -> match (a,b) with [ $list:branches$ ] >>


| <:ctyp:< [= $list:l$ ] >> ->
  let branches = List.map (fun [
    PvTag loc cid _ tyl _ ->
    let cid = Pcaml.unvala cid in
    let tyl = Pcaml.unvala tyl in
    let vars_fmts = List.mapi (fun i ty ->
        (Printf.sprintf "a_%d" i, Printf.sprintf "b_%d" i, fmtrec ty)) tyl in

    let var1pats = List.map (fun (v, _, _) -> <:patt< $lid:v$ >>) vars_fmts in
    let cons1pat = List.fold_left (fun p vp -> <:patt< $p$ $vp$ >>)
        <:patt< ` $cid$ >> var1pats in
    let var2pats = List.map (fun (_, v, _) -> <:patt< $lid:v$ >>) vars_fmts in
    let cons2pat = List.fold_left (fun p vp -> <:patt< $p$ $vp$ >>)
        <:patt< ` $cid$ >> var2pats in
    let conspat = <:patt< ($cons1pat$, $cons2pat$) >> in

    let fldcmps = List.map (fun (v1, v2, fmtf) -> <:expr< $fmtf$ $lid:v1$ $lid:v2$ >>) vars_fmts in
    let cmpexp = match fldcmps with [
      [h::t] -> List.fold_left (fun e1 e2 -> <:expr< $e1$ && $e2$ >>) h t
    | [] -> <:expr< True >> ] in

    (conspat, <:vala< None >>, cmpexp)

  | PvInh _ ty ->
    let lili = match ty with [
      <:ctyp< $_lid:lid$ >> -> (None, lid)
    | <:ctyp< $longid:li$ . $_lid:lid$ >> -> (Some li, lid)
    ] in
    let conspat = <:patt< (( # $lilongid:lili$ as a ), ( # $lilongid:lili$ as b )) >> in
    let fmtf = match ty with [
      <:ctyp< $lid:lid$ >> ->
        let f = eq_fname arg lid in
        <:expr< $lid:f$ >>
    | <:ctyp< $longid:li$ . $lid:lid$ >> ->
        let f = eq_fname arg lid in
        Expr.prepend_longident li <:expr< $lid:f$ >>
    ] in
    (conspat, <:vala< None >>, <:expr< $fmtf$ a b >>)
  ]) l in
  let branches = branches @ [ (<:patt< _ >>, <:vala< None >>, <:expr< False >>) ] in
  <:expr< fun a b -> match (a,b) with [ $list:branches$ ] >>

  | <:ctyp:< { $list:fields$ } >> ->
  let (rec1pat, rec2pat, body) = fmt_record loc arg fields in
  <:expr< fun $rec1pat$ -> fun $rec2pat$ -> $body$ >>

  ]
  and fmt_record loc arg fields = 
  let labels_vars_fmts = List.map (fun (_, fname, _, ty, attrs) ->
        let ty = ctyp_wrap_attrs ty (Pcaml.unvala attrs) in
        (fname, Printf.sprintf "a_%s" fname, Printf.sprintf "b_%s" fname, fmtrec ty)) fields in

  let v1_pl = List.map (fun (f, v, _,  _) -> (<:patt< $lid:f$ >>, <:patt< $lid:v$ >>)) labels_vars_fmts in
  let v1pat = <:patt< { $list:v1_pl$ } >> in
  let v2_pl = List.map (fun (f, _, v,  _) -> (<:patt< $lid:f$ >>, <:patt< $lid:v$ >>)) labels_vars_fmts in
  let v2pat = <:patt< { $list:v2_pl$ } >> in
  let fldcmps = List.map (fun (v, v1, v2, fmtf) -> <:expr< $fmtf$ $lid:v1$ $lid:v2$ >>) labels_vars_fmts in
  let cmpexp = match fldcmps with [
    [h::t] -> List.fold_left (fun e1 e2 -> <:expr< $e1$ && $e2$ >>) h t
  | [] -> assert False ]
  in
  (v1pat, v2pat, cmpexp)
 in
  fmtrec ty0
;

value fmt_top arg params = fun [
  <:ctyp< $t1$ == $_priv:_$ $t2$ >> ->
  fmt_expression arg params t2
| t -> fmt_expression arg params t
]
;

value str_item_top_funs arg (loc, tyname) param_map ty =
  let tyname = Pcaml.unvala tyname in
  let eqfname = eq_fname arg tyname in
  let e = fmt_top arg param_map ty in

  let paramfun_patts = List.map (fun (_,eqf) -> <:patt< $lid:eqf$ >>) param_map in
  [(eqfname, Expr.abstract_over paramfun_patts
      <:expr< fun arg -> $e$ arg >>)]
;

value sig_item_top_funs arg (loc, tyname) param_map ty =
  let tyname = Pcaml.unvala tyname in
  let eqfname = eq_fname arg tyname in
  let paramtys = List.map (fun (tyna, _) -> <:ctyp< '$tyna$ >>) param_map in
  let argfmttys = List.map (fun pty -> <:ctyp< $pty$ -> $pty$ -> Stdlib.Bool.t >>) paramtys in  
  let ty = <:ctyp< $lid:tyname$ >> in
  let thety = Ctyp.applist ty paramtys in
  let eqftype = Ctyp.arrows_list loc argfmttys <:ctyp< $thety$ -> $thety$ -> Stdlib.Bool.t >> in
  [(eqfname, eqftype)]
;

value str_item_funs arg ((loc,_) as tyname) params ty =
  let param_map = List.mapi (fun i p ->
    match Pcaml.unvala (fst p) with [
      None -> failwith "cannot derive eq-functions for type decl with unnamed type-vars"
    | Some na -> (na, Printf.sprintf "tp_%d" i)
    ]) params in
  let l = str_item_top_funs arg tyname param_map ty in
  let types = sig_item_top_funs arg tyname param_map ty in
  List.map (fun (fname, body) ->
      let fty = List.assoc fname types in
      let fty = if param_map = [] then fty
        else <:ctyp< ! $list:(List.map fst param_map)$ . $fty$ >> in
      (<:patt< ( $lid:fname$ : $fty$ ) >>, body, <:vala< [] >>)) l
;

value sig_item_funs arg ((loc,_) as tyname) params ty =
  let param_map = List.mapi (fun i p ->
    match Pcaml.unvala (fst p) with [
      None -> failwith "cannot derive eq-functions for type decl with unnamed type-vars"
    | Some na -> (na, Printf.sprintf "tp_%d" i)
    ]) params in
  let l = sig_item_top_funs arg tyname param_map ty in
  List.map (fun (fname, ty) ->
      <:sig_item< value $lid:fname$ : $ty$>>) l
;

value is_deriving_eq attr = Pa_deriving.is_deriving "eq" attr ;
value apply_deriving_eq ctxt attr = Pa_deriving.apply_deriving "eq" ctxt attr ;

value str_item_gen_eq0 arg td =
  let tyname = Pcaml.unvala td.tdNam
  and params = Pcaml.unvala td.tdPrm
  and tk = td.tdDef in
  str_item_funs arg tyname params tk
;

value loc_of_type_decl td = fst (Pcaml.unvala td.tdNam) ;

value str_item_gen_eq arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let loc = loc_of_type_decl (List.hd tdl) in
  let l = List.concat (List.map (str_item_gen_eq0 arg) tdl) in
  <:str_item< value rec $list:l$ >>
| _ -> assert False ]
;

value sig_item_gen_eq0 arg td =
  let tyname = Pcaml.unvala td.tdNam
  and params = Pcaml.unvala td.tdPrm
  and tk = td.tdDef in
  sig_item_funs arg tyname params tk
;

value sig_item_gen_eq arg = fun [
  <:sig_item:< type $_flag:_$ $list:tdl$ >> ->
    let loc = loc_of_type_decl (List.hd tdl) in
    let l = List.concat (List.map (sig_item_gen_eq0 arg) tdl) in
    <:sig_item< declare $list:l$ end >>
| _ -> assert False ]
;

value expr_eq arg = fun [
  <:expr:< [%eq: $type:ty$ ] >> ->
    let loc = loc_of_ctyp ty in
    let e = fmt_top arg [] ty in
    <:expr< fun a b ->  $e$ a b >>
| _ -> assert False ]
;

ef.val := EF.{ (ef.val) with
  str_item = extfun ef.val.str_item with [
    <:str_item:< type $_flag:_$ $list:tdl$ >> as z
    when List.exists (fun td -> List.exists is_deriving_eq (Pcaml.unvala td.tdAttributes)) tdl ->
    fun arg -> do {
    let f = str_item_gen_eq arg z in
      <:str_item< declare $list:[z ; f ]$ end >>
}
  ] }
;

ef.val := EF.{ (ef.val) with
  sig_item = extfun ef.val.sig_item with [
    <:sig_item:< type $_flag:_$ $list:tdl$ >> as z
    when List.exists (fun td -> List.exists is_deriving_eq (Pcaml.unvala td.tdAttributes)) tdl ->
    fun arg -> do {
    let f = sig_item_gen_eq arg z in
      <:sig_item< declare $list:[z ; f ]$ end >>
}
  ] }
;


ef.val := EF.{ (ef.val) with
  expr = extfun ef.val.expr with [
    <:expr:< [%eq: $type:_$ ] >> as z ->
      fun arg -> expr_eq arg z
  ] }
;

value plugin = Pa_deriving.{
  name = "eq"
; options = ["optional"]
; alg_attributes = ["equal"; "nobuiltin"]
; extensions = ["eq"]
; expr = expr_eq
; str_item = str_item_gen_eq
; sig_item = sig_item_gen_eq
}
;
