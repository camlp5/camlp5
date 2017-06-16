(* camlp5r *)
(* pr_extprint.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";

(* heuristic to rebuild the EXTEND_PRINTER statement from the AST *)

open Pcaml;
open Prtools;

(* Extracting *)

value unrules =
  loop [] where rec loop r =
    fun
    [ <:expr< [$rule$ :: $rules$] >> ->
        let (p, wo, e) =
          match rule with
          [ <:expr< ($_$, $_$, $e$) >> ->
              match e with
              [ <:expr< fun [ $p$ $opt:wo$ -> Some $e$ | _ -> None ] >> ->
                  (p, wo, e)
              | <:expr< fun $p$ -> Some $e$ >> ->
                  (p, None, e)
              | _ ->
                  raise Not_found ]
          | _ ->
              raise Not_found ]
        in
        let e =
          match e with
          [ <:expr< fun curr next pc -> $e$ >> -> e
          | _ -> raise Not_found ]
        in
        match (p, wo, e, rules) with
        [ (<:patt< z >>, None, <:expr< next pc z >>, <:expr< [] >>) -> r
        | _ -> loop [(p, wo, e) :: r] rules ]
    | <:expr< [] >> -> r
    | _ -> raise Not_found ]
;

value unextend_body pr pos body =
  let pos =
    match pos with
    [ <:expr< Some $p$ >> ->
        let p =
          match p with
          [ <:expr< Eprinter.First >> -> Eprinter.First
          | <:expr< Eprinter.Last >> -> Eprinter.Last
          | <:expr< Eprinter.Before $str:n$ >> -> Eprinter.Before n
          | <:expr< Eprinter.After $str:n$ >> -> Eprinter.After n
          | <:expr< Eprinter.Level $str:n$ >> -> Eprinter.Level n
          | _ -> raise Not_found ]
        in
        Some p
    | <:expr< None >> -> None
    | _ -> raise Not_found ]
  in
  let ll =
    loop body where rec loop =
      fun
      [ <:expr< [($lab$, $rules$) :: $levs$] >> ->
          let label =
            match lab with
            [ <:expr< Some $str:s$ >> -> Some s
            | <:expr< None >> -> None
            | _ -> raise Not_found ]
          in
          let rules =
            match rules with
            [ <:expr< fun e__ -> Extfun.extend e__ $rules$ >> -> unrules rules
            | _ -> raise Not_found ]
          in
          [(label, rules) :: loop levs]
      | <:expr< [] >> -> []
      | _ -> raise Not_found ]
  in
  (pr, pos, ll)
;

(* Printing *)

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value bar_before elem pc x = pprintf pc "| %p" elem x;

value comm_bef pc loc =
  if flag_comments_in_phrases.val then Prtools.comm_bef pc loc else ""
;

value comm_expr expr pc z =
  let ccc = comm_bef pc.ind (MLast.loc_of_expr z) in
  Pretty.sprintf "%s%s" ccc (expr pc z)
;

value opt_position pc =
  fun
  [ Some p ->
      match p with
      [ Eprinter.First -> pprintf pc " FIRST"
      | Eprinter.Last -> pprintf pc " LAST"
      | Eprinter.Before n -> pprintf pc " BEFORE \"%s\"" n
      | Eprinter.After n -> pprintf pc " AFTER \"%s\"" n
      | Eprinter.Level n -> pprintf pc " LEVEL \"%s\"" n ]
  | None -> pprintf pc "" ]
;

value patt_as pc z =
  match z with
  [ <:patt< ($x$ as $y$) >> -> pprintf pc "%p as @[%p@]" patt x patt y
  | z -> patt pc z ]
;

value rule pc ((p, wo, e), is_last) =
  match wo with
  [ Some e1 ->
      pprintf pc "@[<2>%p@ @[when@;%p ->@]@;%q@]" patt_as p expr e1 expr e
        (if is_last then "" else "|")
  | None ->
      pprintf pc "@[<2>%p ->@;%q@]" patt_as p (comm_expr expr) e
        (if is_last then "" else "|") ]
;

value rule_list pc =
  fun
  [ [] -> pprintf pc "[ ]"
  | rules -> pprintf pc "[ %p ]" (vlist3 rule (bar_before rule)) rules ]
;

value level pc (lab, rules) =
  match lab with
  [ Some lab -> pprintf pc "@[<b>\"%s\"@;%p@]" lab rule_list rules
  | None -> pprintf pc "@[<2>%p@]" rule_list rules ]
;

value level_list pc =
  fun
  [ [] -> pprintf pc "[ ]"
  | ll -> pprintf pc "[ %p ]" (vlist2 level (bar_before level)) ll ]
;

value extend_body pc exl =
  vlist
    (fun pc (pr, pos, ll) ->
       pprintf pc "@[<b>%p:%p@;%p@ ;@]" expr pr opt_position pos
         level_list ll)
    pc exl
;

value rebuild = ref True;

value extend pc =
  fun
  [ <:expr< Eprinter.extend $pr$ $pos$ $body$ >> ->
      try
        let ex = unextend_body pr pos body in
        pprintf pc "EXTEND_PRINTER@;%p@ END" extend_body [ex]
      with
      [ Not_found ->
          let expr = Eprinter.apply_level pr_expr "dot" in
          pprintf pc "Eprinter.extend@;%p@ %p@ %p" expr pr expr pos
            expr body ]
  | <:expr< do { $list:el$ } >> as e ->
      try
        let exl =
          List.map
            (fun
             [ <:expr< Eprinter.extend $pr$ $pos$ $body$ >> ->
                 unextend_body pr pos body
             | _ ->
                 assert False ])
            el
        in
        pprintf pc "EXTEND_PRINTER@;%p@ END" extend_body exl
      with
      [ Not_found ->
          Ploc.call_with rebuild False (fun () -> expr pc e) () ]
  | e -> expr pc e ]
;

value is_extend el =
  rebuild.val &&
  List.for_all
    (fun
     [ <:expr< Eprinter.extend $_$ $_$ $_$ >> -> True
     | _ -> False ])
    el
;

EXTEND_PRINTER
  pr_expr: LEVEL "top"
    [ [ <:expr< do { $list:el$ } >> as e when is_extend el -> next pc e ] ]
  ;
  pr_expr: LEVEL "apply"
    [ [ <:expr< Eprinter.extend $_$ $_$ $_$ >> as e -> next pc e ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< Eprinter.extend $_$ $_$ $_$ >> as e -> extend pc e
      | <:expr< do { $list:el$ } >> as e when is_extend el -> extend pc e ] ]
  ;
END;
