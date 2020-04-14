(* camlp5r *)
(* pa_deriving_show.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "q_MLast.cmo";
#load "pa_extfun.cmo";

open Asttools;
open MLast;
open Pa_passthru ;
open Ppxutil ;

module Ctxt = struct
  include Pa_passthru.Ctxt ;

value with_path ctxt =
  match option ctxt "with_path" with [
    <:expr< True >> -> True
  | <:expr< False >> -> False
  | _ -> failwith "Pa_deriving_show.Ctxt.with_path: option with_path had bad value"
  ]
;

value prefixed_name ctxt id =
  if with_path ctxt then Printf.sprintf "%s.%s" ctxt.module_path id
  else id
;

value module_path ctxt li =
  let rec li2string = fun [
    <:longident< $uid:uid$ >> -> uid
  | <:longident< $longid:li$ . $uid:uid$ >> ->
    Printf.sprintf "%s.%s" (li2string li) uid
  | [%unmatched_vala] -> failwith "module_path"
  ] in
  Ctxt.set_module_path ctxt (li2string li)
;

end ;

value pp_fname arg tyname =
  if tyname = "t" then "pp"
  else "pp_"^tyname
;

value show_fname arg tyname =
  if tyname = "t" then "show"
  else "show_"^tyname
;

value extract_printer (attrs : MLast.attributes_no_anti) =
  let ex1 = fun [
    <:attribute_body< printer $exp:e$ ; >> -> Some e
  | _ -> None
  ] in
  let rec exrec = fun [
    [] -> None
  | [h::t] -> match ex1 (Pcaml.unvala h) with [ Some x -> Some x | None -> exrec t ]
  ] in
  exrec attrs
;

value fmt_expression arg param_map ty0 =
  let rec fmtrec = fun [
  <:ctyp:< _ >> -> <:expr< Fmt.(const string "_") >>
| <:ctyp:< unit >> -> <:expr< fun ofmt arg -> Fmt.(pf ofmt "()") >>
| <:ctyp:< int >> -> <:expr< fun ofmt arg -> Fmt.(pf ofmt "%d" arg) >>
| <:ctyp:< bool >> -> <:expr<  Fmt.bool >>
| <:ctyp:< int32 >> -> <:expr< fun ofmt arg -> Fmt.(pf ofmt "%ldl" arg) >>
| <:ctyp:< int64 >> -> <:expr< fun ofmt arg -> Fmt.(pf ofmt "%LdL" arg) >>
| (<:ctyp:< string >> | <:ctyp:< Stdlib.String.t >> | <:ctyp:< String.t >>) ->
  <:expr< fun ofmt arg -> Fmt.(pf ofmt "%S" arg) >>
| <:ctyp:< bytes >> -> <:expr< fun ofmt arg -> Fmt.(pf ofmt "%S" (Bytes.to_string arg)) >>
| <:ctyp:< char >> -> <:expr< fun ofmt arg -> Fmt.(pf ofmt "%C" arg) >>
| <:ctyp:< nativeint >> -> <:expr< fun ofmt arg -> Fmt.(pf ofmt "%an" nativeint arg) >>
| <:ctyp:< float >> -> <:expr< fun ofmt arg -> Fmt.(pf ofmt "%F" arg) >>

| <:ctyp:< $t$ [@opaque] >> -> <:expr< Fmt.(const string "<opaque>") >>
| <:ctyp:< $t$ [@printer $exp:e$ ;] >> -> e
| <:ctyp:< $t$ [@polyprinter $exp:e$ ;] >> ->
  let (t0, argtys) = Ctyp.unapplist t in
  let argfmts = List.map fmtrec argtys in
  Expr.applist <:expr< $e$ >> argfmts

| <:ctyp:< list $ty$ >> ->
  let fmt1 = fmtrec ty in
  <:expr< fun (ofmt : Format.formatter) arg -> Fmt.(pf ofmt $str:"@[<2>[%a@,]@]"$ (list ~{sep=semi} $fmt1$) arg) >>

| <:ctyp:< array $ty$ >> ->
  let fmt1 = fmtrec ty in
  <:expr< fun (ofmt : Format.formatter) arg -> Fmt.(pf ofmt $str:"@[<2>[|%a@,|]@]"$ (array ~{sep=semi} $fmt1$) arg) >>

| (<:ctyp:< ref $ty$ >> | <:ctyp:< Pervasives.ref $ty$ >>) ->
  let fmt1 = fmtrec ty in
  <:expr< fun (ofmt : Format.formatter) arg -> Fmt.(pf ofmt $str:"ref (%a)"$ $fmt1$ arg.val) >>

| <:ctyp:< lazy_t $ty$ >> ->
  let fmt1 = fmtrec ty in
  <:expr< fun (ofmt : Format.formatter) arg ->
    if Lazy.is_val arg then
      $fmt1$ ofmt (Lazy.force arg)
    else Fmt.(const string "<not evaluated>") ofmt () >>

| <:ctyp:< option $ty$ >> ->
  let fmt1 = fmtrec ty in
  <:expr< fun ofmt -> fun [
          None -> Fmt.(const string "None") ofmt ()
        | Some arg -> Fmt.(pf ofmt "(Some %a)" $fmt1$ arg)
      ] >>

| (<:ctyp:< result $ty1$ $ty2$ >> | <:ctyp:< Result.result $ty1$ $ty2$ >>) ->
  <:expr< fun ofmt -> fun [
          Result.Ok ok -> Fmt.(pf ofmt "(Ok %a)" $(fmtrec ty1)$ ok)
        | Result.Error e -> Fmt.(pf ofmt "(Error %a)" $(fmtrec ty2)$ e)
      ] >>

| <:ctyp:< $t1$ $t2$ >> -> <:expr< $fmtrec t1$ $fmtrec t2$ >>

| <:ctyp:< '$i$ >> ->
  let fmtf = match List.assoc i param_map with [
    x -> x | exception Not_found -> failwith "pa_deriving.show: unrecognized param-var in type-decl"
  ] in
  <:expr< $lid:fmtf$ >>

| <:ctyp:< $lid:lid$ [@nobuiltin] >> ->
  let fname = pp_fname arg lid in
  <:expr< $lid:fname$ >>

| <:ctyp:< $lid:lid$ >> ->
  let fname = pp_fname arg lid in
  <:expr< $lid:fname$ >>
| <:ctyp:< $longid:li$ . $lid:lid$ >> ->
  let fname = pp_fname arg lid in
  Expr.prepend_longident li <:expr< $lid:fname$ >>

| <:ctyp:< $_$ -> $_$ >> -> <:expr< Fmt.(const string "<fun>") >>

| <:ctyp:< ( $list:tyl$ ) >> ->
    let vars = List.mapi (fun n _ -> Printf.sprintf "v%d" n) tyl in
    let fmts = List.map fmtrec tyl in
    let fmtstring = Printf.sprintf "(@[%s@])"
        (String.concat ",@ " (List.map (fun _ -> "%a") vars)) in
    let e = List.fold_left2 (fun e f v -> <:expr< $e$ $f$ $lid:v$ >>)
        <:expr< pf ofmt $str:fmtstring$ >> fmts vars in
    let varpats = List.map (fun v -> <:patt< $lid:v$ >>) vars in
    <:expr< fun (ofmt : Format.formatter) ($list:varpats$) -> Fmt.($e$) >>

| <:ctyp:< [ $list:l$ ] >> ->
  let branches = List.map (fun [
    (loc, cid, <:vala< [TyRec _ fields] >>, None, _) ->
    let cid = Pcaml.unvala cid in
    let prefix_txt = (Ctxt.prefixed_name arg cid)^" " in
    let (recpat, body) = fmt_record ~{without_path=True} ~{prefix_txt=prefix_txt} ~{bracket_space=""} loc arg (Pcaml.unvala fields) in

    let conspat = <:patt< $uid:cid$ $recpat$ >> in
    (conspat, <:vala< None >>, body)

  | (loc, cid, tyl, None, attrs) ->
    let cid = Pcaml.unvala cid in
    let tyl = Pcaml.unvala tyl in
    let vars = List.mapi (fun n _ -> Printf.sprintf "v%d" n) tyl in
    let varpats = List.map (fun v -> <:patt< $lid:v$ >>) vars in
    let conspat = List.fold_left (fun p vp -> <:patt< $p$ $vp$ >>)
        <:patt< $uid:cid$ >> varpats in
    match extract_printer (Pcaml.unvala attrs) with [
      Some printerf -> 
      let varexprs = List.map (fun v -> <:expr< $lid:v$ >>) vars in
      let tupleexpr = if varexprs <> [] then <:expr< ( $list:varexprs$ ) >> else <:expr< () >> in
      (conspat, <:vala< None >>, <:expr< $printerf$ ofmt $tupleexpr$ >>)
    | None ->
    let fmts = List.map fmtrec tyl in
    let fmtstring =
      if vars = [] then
        Printf.sprintf "@[<2>%s@]" (Ctxt.prefixed_name arg cid)
      else if List.length vars = 1 then
        Printf.sprintf "(@[<2>%s@ %s)@]" (Ctxt.prefixed_name arg cid)
        (String.concat ",@ " (List.map (fun _ -> "%a") vars))
      else
        Printf.sprintf "(@[<2>%s@ (@,%s@,))@]" (Ctxt.prefixed_name arg cid)
        (String.concat ",@ " (List.map (fun _ -> "%a") vars))
    in
    let e = List.fold_left2 (fun e f v -> <:expr< $e$ $f$ $lid:v$ >>)
        <:expr< pf ofmt $str:fmtstring$ >> fmts vars in
    (conspat, <:vala< None >>, <:expr< Fmt.($e$) >>)
    ]
  | (_, _, _, Some _, _) -> assert False
  ]) l in
  <:expr< fun ofmt -> fun [ $list:branches$ ] >>

| <:ctyp:< [= $list:l$ ] >> ->
  let branches = List.map (fun [
    PvTag loc cid _ tyl _ ->
    let cid = Pcaml.unvala cid in
    let tyl = Pcaml.unvala tyl in
    let vars = List.mapi (fun n _ -> Printf.sprintf "v%d" n) tyl in
    let fmts = List.map fmtrec tyl in
    let fmtstring =
      if vars = [] then
        Printf.sprintf "@[<2>`%s@]" cid
      else if List.length vars = 1 then
        Printf.sprintf "@[<2>`%s (@,%s@,)@]" cid
          (String.concat ",@ " (List.map (fun _ -> "%a") vars))
      else
        Printf.sprintf "@[<2>`%s (@,%s@,)@]" cid
          (String.concat ",@ " (List.map (fun _ -> "%a") vars))
    in
    let varpats = List.map (fun v -> <:patt< $lid:v$ >>) vars in
    let conspat = List.fold_left (fun p vp -> <:patt< $p$ $vp$ >>)
        <:patt< ` $cid$ >> varpats in
    let e = List.fold_left2 (fun e f v -> <:expr< $e$ $f$ $lid:v$ >>)
        <:expr< pf ofmt $str:fmtstring$ >> fmts vars in
    (conspat, <:vala< None >>, <:expr< Fmt.($e$) >>)

  | PvInh _ ty ->
    let lili = match ty with [
      <:ctyp< $_lid:lid$ >> -> (None, lid)
    | <:ctyp< $longid:li$ . $_lid:lid$ >> -> (Some li, lid)
    | [%unmatched_vala] -> failwith "fmt_expression-PvInh"
     ] in
    let conspat = <:patt< ( # $lilongid:lili$ as z ) >> in
    let fmtf = match ty with [
      <:ctyp< $lid:lid$ >> ->
        let f = pp_fname arg lid in
        <:expr< $lid:f$ >>
    | <:ctyp< $longid:li$ . $lid:lid$ >> ->
        let f = pp_fname arg lid in
        Expr.prepend_longident li <:expr< $lid:f$ >>
    | [%unmatched_vala] -> failwith "fmt_expression-PvInh-2"
    ] in
    (conspat, <:vala< None >>, <:expr< Fmt.($fmtf$ ofmt z) >>)
  ]) l in
  <:expr< fun ofmt -> fun [ $list:branches$ ] >>

| <:ctyp:< { $list:fields$ } >> ->
  let (recpat, body) = fmt_record ~{without_path=False} ~{prefix_txt=""} ~{bracket_space=" "} loc arg fields in
  <:expr< fun ofmt $recpat$ -> $body$ >>
| [%unmatched_vala] -> failwith "fmt_expression"
]
and fmt_record ~{without_path} ~{prefix_txt} ~{bracket_space} loc arg fields = 
  let labels_vars_fmts = List.map (fun (_, fname, _, ty, attrs) ->
        let ty = ctyp_wrap_attrs ty (Pcaml.unvala attrs) in
        (fname, Printf.sprintf "v_%s" fname, fmtrec ty)) fields in

  let field_text i f =
    if not without_path && i = 0 then Ctxt.prefixed_name arg f
    else f in
  let fmt = Printf.sprintf "@[<2>%s{%s%s%s}@]"
      prefix_txt
      bracket_space
      (String.concat ";@ " (List.mapi (fun i (f, _, _) ->
                            Printf.sprintf "@[%s =@ %s@]" (field_text i f) "%a") labels_vars_fmts))
      bracket_space
  in
  let e = List.fold_left (fun e (f,v,fmtf) ->
      <:expr< $e$ $fmtf$ $lid:v$ >>)
      <:expr< pf ofmt $str:fmt$ >> labels_vars_fmts in
  let pl = List.map (fun (f, v, _) -> (<:patt< $lid:f$ >>, <:patt< $lid:v$ >>)) labels_vars_fmts in
  (<:patt< { $list:pl$ } >>, <:expr< Fmt.($e$) >>)
in fmtrec ty0
;

value fmt_top arg params = fun [
  <:ctyp< $t1$ == $_priv:_$ $t2$ >> ->
  let arg = match t1 with [
    <:ctyp< $longid:li$ . $lid:_$ >> -> Ctxt.module_path arg li
  | _ -> arg
  ] in
  fmt_expression arg params t2
| t -> fmt_expression arg params t
]
;

value str_item_top_funs arg (loc, tyname) param_map ty =
  let tyname = Pcaml.unvala tyname in
  let ppfname = pp_fname arg tyname in
  let showfname = show_fname arg tyname in
  let e = fmt_top arg param_map ty in

  let paramfun_patts = List.map (fun (_,ppf) -> <:patt< $lid:ppf$ >>) param_map in
  let paramfun_exprs = List.map (fun (_,ppf) -> <:expr< $lid:ppf$ >>) param_map in
  let ppfexp = <:expr< $lid:ppfname$ >> in

  [(ppfname, Expr.abstract_over paramfun_patts
      <:expr< fun (ofmt : Format.formatter) arg -> $e$ ofmt arg >>);
   (showfname, Expr.abstract_over paramfun_patts
      <:expr< fun arg -> Format.asprintf "%a" $(Expr.applist ppfexp paramfun_exprs)$ arg >>)]
;

value sig_item_top_funs arg (loc, tyname) param_map ty =
  let tyname = Pcaml.unvala tyname in
  let ppfname = pp_fname arg tyname in
  let showfname = show_fname arg tyname in
  let paramtys = List.map (fun (tyna, _) -> <:ctyp< '$tyna$ >>) param_map in
  let argfmttys = List.map (fun pty -> <:ctyp< Fmt.t $pty$ >>) paramtys in  
  let ty = <:ctyp< $lid:tyname$ >> in
  let ppftype = Ctyp.arrows_list loc argfmttys <:ctyp< Fmt.t $(Ctyp.applist ty paramtys)$ >> in
  let showftype = Ctyp.arrows_list loc argfmttys <:ctyp< $(Ctyp.applist ty paramtys)$ -> Stdlib.String.t >> in
  [(ppfname, ppftype) ;
   (showfname, showftype)]
;

value str_item_funs arg ((loc,_) as tyname) params ty =
  let param_map = List.mapi (fun i p ->
    match Pcaml.unvala (fst p) with [
      None -> failwith "cannot derive show-functions for type decl with unnamed type-vars"
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
      None -> failwith "cannot derive show-functions for type decl with unnamed type-vars"
    | Some na -> (na, Printf.sprintf "tp_%d" i)
    ]) params in
  let l = sig_item_top_funs arg tyname param_map ty in
  List.map (fun (fname, ty) ->
      <:sig_item< value $lid:fname$ : $ty$>>) l
;

value is_deriving_show attr = Pa_deriving.is_deriving "show" attr ;
value apply_deriving_show ctxt attr = Pa_deriving.apply_deriving "show" ctxt attr ;

value str_item_gen_show0 arg td =
  let arg = List.fold_left apply_deriving_show arg (Pcaml.unvala td.tdAttributes) in
  let tyname = Pcaml.unvala td.tdNam
  and params = Pcaml.unvala td.tdPrm
  and tk = td.tdDef in
  str_item_funs arg tyname params tk
;

value loc_of_type_decl td = fst (Pcaml.unvala td.tdNam) ;

value str_item_gen_show arg = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> ->
    let loc = loc_of_type_decl (List.hd tdl) in
    let l = List.concat (List.map (str_item_gen_show0 arg) tdl) in
    <:str_item< value rec $list:l$ >>
| _ -> assert False ]
;

value sig_item_gen_show0 arg td =
  let tyname = Pcaml.unvala td.tdNam
  and params = Pcaml.unvala td.tdPrm
  and tk = td.tdDef in
  sig_item_funs arg tyname params tk
;

value sig_item_gen_show arg = fun [
  <:sig_item:< type $_flag:_$ $list:tdl$ >> ->
    let loc = loc_of_type_decl (List.hd tdl) in
    let l = List.concat (List.map (sig_item_gen_show0 arg) tdl) in
    <:sig_item< declare $list:l$ end >>
| _ -> assert False ]
;

value expr_show arg = fun [
  <:expr:< [%show: $type:ty$ ] >> ->
    let loc = loc_of_ctyp ty in
    let e = fmt_top arg [] ty in
    <:expr< fun arg -> Format.asprintf "%a" $e$ arg >>
| _ -> assert False ]
;

Pa_deriving.(add_plugin {
  name = "show"
; options = ["with_path"; "optional"]
; default_options = let loc = Ploc.dummy in [ ("optional", <:expr< False >>) ; ("with_path", <:expr< True >>) ]
; alg_attributes = ["opaque"; "printer"; "polyprinter"; "nobuiltin"]
; extensions = ["show"]
; expr = expr_show
; str_item = str_item_gen_show
; sig_item = sig_item_gen_show
})
;

