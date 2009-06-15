(* camlp5r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_extfun.ml,v 1.9 2007/07/11 12:01:39 deraugla Exp $ *)

(* heuristic to rebuild the extfun statement from the AST *)

open Pretty;
open Pcaml.Printers;
open Prtools;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_extfun, not impl: %s; %s\"%s" pc.bef name
    (String.escaped desc) pc.aft
;

value expr pc z = pr_expr.pr_fun "top" pc z;
value patt pc z = pr_patt.pr_fun "top" pc z;

value rec un_extfun rpel =
  fun
  [ <:expr< [ ($_$, $_$, fun [ $list:pel$ ]) :: $el$ ] >> ->
      let (p, wo, e) =
        match pel with
        [ [(p, wo, <:expr< Some $e$ >>);
           (<:patt< _ >>, None, <:expr< None >>)] ->
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

(* copied from pr_r.cmo ; begin *)

value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;

value comm_expr expr pc z =
  let ccc = comm_bef pc (MLast.loc_of_expr z) in
  sprintf "%s%s" ccc (expr pc z)
;

value patt_as pc z =
  match z with
  [ <:patt< ($x$ as $y$) >> ->
      let p1 = patt {(pc) with aft = ""} x in
      let p2 = patt {(pc) with bef = ""} y in
      sprintf "%s as %s" p1 p2
  | z -> patt pc z ]
;

value match_assoc pc (p, w, e) =
  let pc_dang = if pc.aft = "" then "|" else "" in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s -> %s%s" pc.bef
         (patt_as {(pc) with bef = ""; aft = ""} p)
         (match w with
          [ Some e ->
              sprintf " when %s" (expr {(pc) with bef = ""; aft = ""} e)
          | None -> "" ])
         (comm_expr expr {(pc) with bef = ""; aft = ""; dang = pc_dang} e)
         pc.aft)
    (fun () ->
       let patt_arrow k =
         match w with
         [ Some e ->
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
         | None -> patt_as {(pc) with aft = sprintf " ->%s" k} p ]
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
      {(pc) with bef = sprintf "%s[ " pc.bef;
       aft = ("", sprintf " ]%s" pc.aft)}
      pwel
;

(* copied from pr_r.cmo ; end *)

let lev = find_pr_level "top" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< Extfun.extend $e$ $list$ >> as ge ->
      fun curr next pc ->
        try
          let pwel = un_extfun [] list in
          let s1 =
            sprintf "%sextfun %s with" pc.bef
              (expr {(pc) with bef = ""; aft = ""} e)
          in
          let s2 = match_assoc_list {(pc) with bef = tab pc.ind} pwel in
          sprintf "%s\n%s" s1 s2
        with
        [ Not_found -> next pc ge ] ];

