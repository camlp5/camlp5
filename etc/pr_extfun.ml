(* camlp5r q_MLast.cmo ./pa_extfun.cmo ./pa_extprint.cmo ./pa_pprintf.cmo *)
(* $Id: pr_extfun.ml,v 1.17 2008/01/04 14:35:43 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2008 *)

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

(**)
value test = ref False;
Pcaml.add_option "-test" (Arg.Set test) " test";
(**)

value bar_before elem pc x = pprintf pc "| %p" elem x;

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
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s -> %s%s" pc.bef
         (patt_as {(pc) with bef = ""; aft = ""} p)
         (match w with
          [ <:vala< Some e >> ->
              sprintf " when %s" (expr {(pc) with bef = ""; aft = ""} e)
          | _ -> "" ])
         (comm_expr expr {(pc) with bef = ""; aft = ""; dang = pc_dang} e)
         pc.aft)
    (fun () ->
       let patt_arrow k =
         match w with
         [ <:vala< Some e >> ->
             horiz_vertic
               (fun () ->
                  sprintf "%s%s when %s ->%s" pc.bef
                    (patt_as {(pc) with bef = ""; aft = ""} p)
                    (expr {(pc) with bef = ""; aft = ""} e) k)
               (fun () ->
                  let s1 = patt_as {(pc) with aft = ""} p in
                  let s2 =
                    horiz_vertic
                      (fun () ->
                         sprintf "%swhen %s ->%s" (tab pc.ind)
                           (expr {(pc) with bef = ""; aft = ""} e) k)
                      (fun () ->
                         let s1 = sprintf "%swhen" (tab pc.ind) in
                         let s2 =
                           expr
                             {(pc) with ind = pc.ind + 2;
                              bef = tab (pc.ind + 2); aft = sprintf " ->%s" k}
                             e
                         in
                         sprintf "%s\n%s" s1 s2)
                  in
                  sprintf "%s\n%s" s1 s2)
         | _ -> patt_as {(pc) with aft = sprintf " ->%s" k} p ]
       in
       let s1 = patt_arrow "" in
       let s2 =
         comm_expr expr
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
            dang = pc_dang}
           e
       in
       sprintf "%s\n%s" s1 s2)
;

value match_assoc_sh pc pwe = match_assoc {(pc) with ind = pc.ind + 2} pwe;

value match_assoc_list pc pwel =
  if pwel = [] then sprintf "%s[]%s" pc.bef pc.aft
  else
    vlist2 match_assoc_sh (bar_before match_assoc_sh)
      {(pc) with bef = sprintf "%s[ " pc.bef; aft = sprintf " ]%s" pc.aft}
      pwel
;

EXTEND_PRINTER
  pr_expr: LEVEL "top"
    [ [ <:expr< Extfun.extend $e$ $list$ >> as ge ->
        try
          let pwel = un_extfun [] list in
          let s1 =
            sprintf "%sextfun %s with" pc.bef
              (expr {(pc) with bef = ""; aft = ""} e)
          in
          let s2 = match_assoc_list {(pc) with bef = tab pc.ind} pwel in
          sprintf "%s\n%s" s1 s2
        with
        [ Not_found -> next pc ge ] ] ]
  ;
END;
