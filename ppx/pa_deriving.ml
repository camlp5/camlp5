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

value or_option from opt1 opt2 =
  match (opt1, opt2) with [
    (None, None) -> None
  | (Some _, None) -> opt1
  | (None, Some _) -> opt2
  | (Some _, Some _) -> failwith (Printf.sprintf "found more than one derinvig.%s" from)
  ]
;


value extract_deriving name attr =
  let rv = None in
  match Pcaml.unvala attr with [
    <:attribute_body< deriving $structure:sil$ >> ->
      List.fold_left (fun rv -> fun [
        <:str_item< $lid:s$ >> when s = name -> or_option name rv (Some[])
      | <:str_item< $lid:s$ { $list:l$ } >> when s = name -> or_option name rv (Some l)
      | <:str_item< ( $list:l$ ) >> ->
        List.fold_left (fun rv -> fun [
            <:expr< $lid:s$ >> when s = name -> or_option name rv (Some[])
          | <:expr< $lid:s$ { $list:l$ } >> when s = name -> or_option name rv (Some l)
          | _ -> rv ]) rv l
      | _ -> rv ]) rv sil
  | _ -> None
  ]
;

value is_deriving name attr = None <> (extract_deriving name attr) ;

value apply_deriving name ctxt attr =
  let update_ctxt ctxt l =
    let l = List.map (fun [
      (<:patt< $lid:s$ >>, e) -> (s,e)
    | _ -> failwith ("invalid option-label in deriving."^name)
    ]) l in
    Ctxt.{ (ctxt) with options = l @ ctxt.options } in
  match extract_deriving name attr with [
    None -> ctxt
  | Some l -> update_ctxt ctxt l
  ]
;

type plugin_t = {
  name : string
; options : list string
; alg_attributes : list string
; extensions : list string
; expr : Ctxt.t -> expr -> expr
; str_item : Ctxt.t -> str_item -> str_item
; sig_item : Ctxt.t -> sig_item -> sig_item
; default_options : list (string * expr)
}
;

value plugin_registry = ref [] ;
value extension2plugin = ref [] ;
value algattr2plugin = ref [] ;

value push r v = r.val := [v :: r.val] ;

value add_plugin t = do {
  if List.mem_assoc t.name plugin_registry.val then
    failwith (Printf.sprintf "plugin %s already registered" t.name)
  else () ;
  List.iter (fun ename ->
    if List.mem_assoc ename extension2plugin.val then
      failwith (Printf.sprintf "extension %s already registered" ename)
    else ()) t.extensions;
  List.iter (fun aname ->
    if List.mem_assoc aname algattr2plugin.val then
      failwith (Printf.sprintf "algebraic %s already registered" aname)
    else ()) t.alg_attributes ;
  push plugin_registry (t.name, t) ;
  List.iter (fun ename -> push extension2plugin (ename, t.name)) t.extensions ;
  List.iter (fun aname -> push algattr2plugin (aname, t.name)) t.alg_attributes
}
;

value registered_str_item arg pi = fun [
  <:str_item:< type $_flag:_$ $list:tdl$ >> as z ->
    let attrs = Pcaml.unvala (fst (sep_last tdl)).tdAttributes in
    let arg = Ctxt.add_options arg pi.default_options in
    let arg = List.fold_left (apply_deriving pi.name) arg attrs in
    pi.str_item arg z

| _ -> assert False
]
;

value registered_sig_item arg pi = fun [
  <:sig_item:< type $_flag:_$ $list:tdl$ >> as z ->
    let attrs = Pcaml.unvala (fst (sep_last tdl)).tdAttributes in
    let arg = Ctxt.add_options arg pi.default_options in
    let arg = List.fold_left (apply_deriving pi.name) arg attrs in
    pi.sig_item arg z

| _ -> assert False
]
;

value registered_expr_extension arg = fun [
  <:expr:< [% $extension:e$ ] >> as z ->
    let ename = Pcaml.unvala (fst e) in
    let piname = List.assoc ename extension2plugin.val in
    let pi = List.assoc piname plugin_registry.val in
    let arg = Ctxt.add_options arg pi.default_options in
    Some (pi.expr arg z)
| _ -> assert False
]
;


value is_registered_deriving attr =
  List.exists (fun (name, _) -> is_deriving name attr) plugin_registry.val ;

ef.val := EF.{ (ef.val) with
            str_item = extfun ef.val.str_item with [
    <:str_item:< type $_flag:_$ $list:tdl$ >> as z
    when  List.exists is_registered_deriving (Pcaml.unvala (fst (sep_last tdl)).tdAttributes) ->
    fun arg ->
      let attrs = Pcaml.unvala (fst (sep_last tdl)).tdAttributes in
      let ll = plugin_registry.val |> List.map (fun (name, pi) ->
        if List.exists (is_deriving name) attrs then
          [registered_str_item arg pi z]
        else []) in
      let l = List.concat ll in
      Some <:str_item< declare $list:[z :: l ]$ end >>
  ] }
;

ef.val := EF.{ (ef.val) with
            sig_item = extfun ef.val.sig_item with [
    <:sig_item:< type $_flag:_$ $list:tdl$ >> as z
    when  List.exists is_registered_deriving (Pcaml.unvala (fst (sep_last tdl)).tdAttributes) ->
    fun arg ->
      let attrs = Pcaml.unvala (fst (sep_last tdl)).tdAttributes in
      let ll = plugin_registry.val |> List.map (fun (name, pi) ->
        if List.exists (is_deriving name) attrs then
          [registered_sig_item arg pi z]
        else []) in
      let l = List.concat ll in
      Some <:sig_item< declare $list:[z :: l ]$ end >>
  ] }
;

value is_registered_extension attr =
  List.mem_assoc (Pcaml.unvala (fst attr)) extension2plugin.val ;

ef.val := EF.{ (ef.val) with
  expr = extfun ef.val.expr with [
    <:expr:< [% $extension:e$ ] >> as z when is_registered_extension e ->
      fun arg ->
        registered_expr_extension arg z
  ] }
;
