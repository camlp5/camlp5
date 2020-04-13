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
