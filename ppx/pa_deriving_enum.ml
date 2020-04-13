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

value to_fname arg tyname =
  if tyname = "t" then "to_enum"
  else tyname^"_to_enum"
;

value of_fname arg tyname =
  if tyname = "t" then "of_enum"
  else tyname^"_of_enum"
;

value min_fname arg tyname =
  if tyname = "t" then "min"
  else "min_"^tyname
;

value max_fname arg tyname =
  if tyname = "t" then "max"
  else "max_"^tyname
;

value extract_value (attrs : MLast.attributes_no_anti) =
  let ex1 = fun [
    <:attribute_body< "value" $int:i$ ; >> -> Some (int_of_string i)
  | _ -> None
  ] in
  let rec exrec = fun [
    [] -> None
  | [h::t] -> match ex1 (Pcaml.unvala h) with [ Some x -> Some x | None -> exrec t ]
  ] in
  exrec attrs
;

value to_expression arg = fun [
(*
    <:ctyp:< $lid:lid$ >> ->
      let fname = to_fname arg lid in
      <:expr< $lid:fname$ >>
  | <:ctyp:< $longid:li$ . $lid:lid$ >> ->
      let fname = to_fname arg lid in
      Expr.prepend_longident li <:expr< $lid:fname$ >>

  |*) <:ctyp:< [ $list:l$ ] >> ->
  let (_, map,revacc) = List.fold_left (fun (idx, map, revacc) (loc, cid, _, _, attrs) ->
    let idx = match extract_value (Pcaml.unvala attrs) with [
      None -> idx
    | Some n -> n
    ] in
    let cid = Pcaml.unvala cid in

    let conspat = <:patt< $uid:cid$ >> in
    let consexpr = <:expr< $uid:cid$ >> in
    
    let body = <:expr< $int:(string_of_int idx)$ >> in

    (idx+1, [(consexpr,idx) :: map],
     [(conspat, <:vala< None >>, body) :: revacc])) (0,[], []) l in
  let branches = List.rev revacc in
  (map, <:expr< fun [ $list:branches$ ] >>)

  | <:ctyp:< [= $list:l$ ] >> ->
  let (_, map,revacc) = List.fold_left (fun (idx,map,revacc) -> fun [
    PvTag loc cid _ _ attrs ->
    let idx = match extract_value (Pcaml.unvala attrs) with [
      None -> idx | Some n -> n
    ] in
    let cid = Pcaml.unvala cid in
    let conspat = <:patt< ` $cid$ >> in
    let consexpr = <:expr< ` $cid$ >> in
    
    let body = <:expr< $int:(string_of_int idx)$ >> in

    (idx+1, [(consexpr,idx) :: map],
     [(conspat, <:vala< None >>, body) :: revacc])


  | PvInh _ ty -> failwith "deriving.enum only works on variants sans inheritance"
  ]) (0, [], []) l in
  let branches = List.rev revacc in
  (map, <:expr< fun [ $list:branches$ ] >>)
  ]
;

value of_expression arg map t =
  let loc = loc_of_ctyp t in
  let branches = List.map (fun (e,n) ->
    (<:patt< $int:(string_of_int n)$ >>, <:vala< None >>, <:expr< Some $e$ >>)) map in
  let branches = branches @ [ (<:patt< _ >>, <:vala< None >>, <:expr< None >>) ] in
  <:expr< fun [ $list:branches$ ] >>
;

value fmt_top arg t =
  let t = match t with [
    <:ctyp< $t1$ == $_priv:_$ $t2$ >> -> t2
  | t -> t
  ] in
  let (map, toexp) = to_expression arg t in
  let ofexp = of_expression arg map t in
  let vals = List.map snd map in
  let minval = List.fold_left min (List.hd vals) (List.tl vals) in
  let maxval = List.fold_left max (List.hd vals) (List.tl vals) in
  (toexp,ofexp,minval,maxval);

value str_item_top_funs arg (loc, tyname) ty =
  let tyname = Pcaml.unvala tyname in
  let tofname = to_fname arg tyname in
  let offname = of_fname arg tyname in
  let minfname = min_fname arg tyname in
  let maxfname = max_fname arg tyname in
  let (toexp,ofexp,minval,maxval) = fmt_top arg ty in
  [(tofname, toexp);
   (offname, ofexp);
   (minfname, <:expr< $int:(string_of_int minval)$ >>);
   (maxfname, <:expr< $int:(string_of_int maxval)$ >>)]
;

value sig_item_top_funs arg (loc, tyname) ty =
  let tyname = Pcaml.unvala tyname in
  let tofname = to_fname arg tyname in
  let offname = of_fname arg tyname in
  let minfname = min_fname arg tyname in
  let maxfname = max_fname arg tyname in
  let thety = <:ctyp< $lid:tyname$ >> in
  let toftype = <:ctyp< $thety$ -> Stdlib.Int.t >> in
  let offtype = <:ctyp< Stdlib.Int.t -> Stdlib.Option.t $thety$ >> in
  [(tofname, toftype);
   (offname, offtype);
   (minfname, <:ctyp< Stdlib.Int.t >>);
   (maxfname, <:ctyp< Stdlib.Int.t >>)]
;

value str_item_funs arg ((loc,_) as tyname) ty =
  let l = str_item_top_funs arg tyname ty in
  let types = sig_item_top_funs arg tyname ty in
  List.map (fun (fname, body) ->
      let fty = List.assoc fname types in
      (<:patt< ( $lid:fname$ : $fty$ ) >>, body, <:vala< [] >>)) l
;

value sig_item_funs arg ((loc,_) as tyname) ty =
  let l = sig_item_top_funs arg tyname ty in
  List.map (fun (fname, ty) ->
      <:sig_item< value $lid:fname$ : $ty$>>) l
;

value is_deriving_enum attr = match Pcaml.unvala attr with [
  <:attribute_body< deriving $structure:sil$ >> ->
    List.exists (fun [
      <:str_item< enum >> -> True
    | <:str_item< enum $_$ >> -> True
    | <:str_item< ( $list:l$ ) >> ->
      List.exists (fun [
          <:expr< enum >> -> True
        | <:expr< enum $_ $ >> -> True
        | _ -> False ]) l
    | _ -> False ]) sil
| _ -> False
]
;

value str_item_gen_enum0 arg td =
  let tyname = Pcaml.unvala td.tdNam
  and params = Pcaml.unvala td.tdPrm
  and tk = td.tdDef in
  if params <> [] then
    failwith "cannot derive enum-functions for type decl with type-vars"
  else
    str_item_funs arg tyname tk
;

value loc_of_type_decl td = fst (Pcaml.unvala td.tdNam) ;

value str_item_gen_enum arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let loc = loc_of_type_decl (List.hd tdl) in
    let l = List.concat (List.map (str_item_gen_enum0 arg) tdl) in
    <:str_item< value rec $list:l$ >>
| _ -> assert False ]
;

value sig_item_gen_enum0 arg td =
  let tyname = Pcaml.unvala td.tdNam
  and params = Pcaml.unvala td.tdPrm
  and tk = td.tdDef in
  if params <> [] then
    failwith "cannot derive enum-functions for type decl with type-vars"
  else
    sig_item_funs arg tyname tk
;

value sig_item_gen_enum arg = fun [
  <:sig_item:< type $_flag:_$ $list:tdl$ >> ->
    let loc = loc_of_type_decl (List.hd tdl) in
    let l = List.concat (List.map (sig_item_gen_enum0 arg) tdl) in
    <:sig_item< declare $list:l$ end >>
| _ -> assert False ]
;

ef.val := EF.{ (ef.val) with
  str_item = extfun ef.val.str_item with [
    <:str_item:< type $_flag:_$ $list:tdl$ >> as z
    when List.exists (fun td -> List.exists is_deriving_enum (Pcaml.unvala td.tdAttributes)) tdl ->
    fun arg -> do {
    let f = str_item_gen_enum arg z in
      <:str_item< declare $list:[z ; f ]$ end >>
}
  ] }
;

ef.val := EF.{ (ef.val) with
  sig_item = extfun ef.val.sig_item with [
    <:sig_item:< type $_flag:_$ $list:tdl$ >> as z
    when List.exists (fun td -> List.exists is_deriving_enum (Pcaml.unvala td.tdAttributes)) tdl ->
    fun arg -> do {
    let f = sig_item_gen_enum arg z in
      <:sig_item< declare $list:[z ; f ]$ end >>
}
  ] }
;

value plugin = Pa_deriving.{
  name = "enum"
; options = ["optional"]
; alg_attributes = ["value"]
; extensions = []
; expr = (fun _ _ -> assert False)
; str_item = str_item_gen_enum
; sig_item = sig_item_gen_enum
}
;
