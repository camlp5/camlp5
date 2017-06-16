(* camlp5r *)
(* pr_extfun.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";
#load "pa_macro.cmo";

(* heuristic to rebuild the extfun statement from the AST *)

open Pretty;
open Pcaml;
open Prtools;

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;

value rec un_extfun rpel =
  fun
  [ <:expr< [ ($_$, $_$, fun [ $list:pel$ ]) :: $el$ ] >> ->
      let (p, wo, e) =
        match pel with
        [ [(p, wo, <:expr< Some $e$ >>);
           (<:patt< _ >>, <:vala< None >>, <:expr< None >>)] ->
            (p, wo, e)
        | [(p, wo, <:expr< Some $e$ >>)] -> (p, wo, e)
        | _ -> raise Not_found ]
      in
      let rpel =
        match rpel with
        [ [(p1, wo1, e1) :: pel] ->
            if wo1 = wo && e1 = e then
              let p =
                let loc = MLast.loc_of_patt p1 in
                match (p1, p) with
                [ (<:patt< ($x1$ as $x2$) >>, <:patt< ($y1$ as $y2$) >>) ->
                    if x2 = y2 then <:patt< ($x1$ | $y1$ as $x2$) >>
                    else <:patt< $p1$ | $p$ >>
                | _ -> <:patt< $p1$ | $p$ >> ]
              in
              [(p, wo, e) :: pel]
            else [(p, wo, e) :: rpel]
        | [] -> [(p, wo, e)] ]
      in
      un_extfun rpel el
  | <:expr< [] >> -> List.rev rpel
  | _ -> raise Not_found ]
;

IFDEF OCAML_VERSION <= OCAML_1_07 THEN
  value with_ind = Pprintf.with_ind;
END;

value bar_before elem pc x = pprintf pc "| %p" elem x;

value comm_bef pc loc =
  if flag_comments_in_phrases.val then Prtools.comm_bef pc loc else ""
;

value comm_expr expr pc z =
  let ccc = comm_bef pc.ind (MLast.loc_of_expr z) in
  sprintf "%s%s" ccc (expr pc z)
;

value patt_as pc z =
  match z with
  [ <:patt< ($x$ as $y$) >> -> pprintf pc "%p as @[%p@]" patt x patt y
  | z -> patt pc z ]
;

value match_assoc pc (p, w, e) =
  let pc_dang = if pc.aft = "" then "|" else "" in
  match w with
  [ <:vala< Some e1 >> ->
      pprintf pc "%p@ @[when@;%p ->@]@;%q" patt_as p expr e1
        (comm_expr expr) e pc_dang
  | _ ->
      pprintf pc "%p ->@;%q" patt_as p (comm_expr expr) e pc_dang ]
;

value match_assoc_sh pc pwe = match_assoc {(pc) with ind = pc.ind + 2} pwe;

value match_assoc_list pc pwel =
  if pwel = [] then pprintf pc "[]"
  else
    pprintf pc "[ %p ]" (vlist2 match_assoc_sh (bar_before match_assoc_sh))
      pwel
;

EXTEND_PRINTER
  pr_expr: LEVEL "top"
    [ [ <:expr< Extfun.extend $e$ $list$ >> as ge ->
        try
          let pwel = un_extfun [] list in
          pprintf pc "@[<b>extfun %p with@ %p" expr e match_assoc_list pwel
        with
        [ Not_found -> next pc ge ] ] ]
  ;
END;
