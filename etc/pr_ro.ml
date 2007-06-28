(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_ro.ml,v 1.25 2007/06/28 04:53:06 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* Pretty printing extension for objects and labels *)

open Pretty;
open Pcaml.NewPrinters;
open Prtools;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_ro, not impl: %s; %s\"%s" pc.bef name (String.escaped desc)
    pc.aft
;

value is_infix = do {
  let infixes = Hashtbl.create 73 in
  List.iter (fun s -> Hashtbl.add infixes s True)
    ["!="; "&&"; "*"; "**"; "*."; "+"; "+."; "-"; "-."; "/"; "/."; "<"; "<=";
     "<>"; "="; "=="; ">"; ">="; "@"; "^"; "asr"; "land"; "lor"; "lsl"; "lsr";
     "lxor"; "mod"; "or"; "||"; "~-"; "~-."];
  fun s -> try Hashtbl.find infixes s with [ Not_found -> False ]
};

value is_keyword =
  let keywords = ["value"] in
  fun s -> List.mem s keywords
;

value has_special_chars s =
  if String.length s = 0 then False
  else
    match s.[0] with
    [ '0'..'9' | 'A'..'Z' | 'a'..'z' | '_' -> False
    | _ -> True ]
;

value var_escaped pc v =
  let x =
    if is_infix v || has_special_chars v then "\\" ^ v
    else if is_keyword v then v ^ "__"
    else v
  in
  sprintf "%s%s%s" pc.bef x pc.aft
;

value alone_in_line pc =
  (pc.aft = "" || pc.aft = ";") && pc.bef <> "" &&
  loop 0 where rec loop i =
    if i >= String.length pc.bef then True
    else if pc.bef.[i] = ' ' then loop (i + 1)
    else False
;

value expr pc z = pr_expr.pr_fun "top" pc z;
value patt pc z = pr_patt.pr_fun "top" pc z;
value ctyp pc z = pr_ctyp.pr_fun "top" pc z;
value class_expr pc z = pr_class_expr.pr_fun "top" pc z;
value class_type pc z = pr_class_type.pr_fun "top" pc z;
value class_str_item pc z = pr_class_str_item.pr_fun "top" pc z;
value class_sig_item pc z = pr_class_sig_item.pr_fun "top" pc z;

value rec mod_ident pc sl =
  match sl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [s] -> sprintf "%s%s%s" pc.bef s pc.aft
  | [s :: sl] -> mod_ident {(pc) with bef = sprintf "%s%s." pc.bef s} sl ]
;

value semi_after elem pc x = elem {(pc) with aft = sprintf ";%s" pc.aft} x;
value amp_before elem pc x = elem {(pc) with bef = sprintf "%s& " pc.bef} x;
value and_before elem pc x = elem {(pc) with bef = sprintf "%sand " pc.bef} x;
value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;

value type_var pc (tv, (p, m)) =
  sprintf "%s%s'%s%s" pc.bef (if p then "+" else if m then "-" else "") tv
    pc.aft
;

value class_type_params pc ctp =
  if ctp = [] then sprintf "%s%s" pc.bef pc.aft
  else
    let ctp = List.map (fun ct -> (ct, ",")) ctp in
    plist type_var 1
      {(pc) with bef = sprintf "%s[" pc.bef; aft = sprintf "] %s" pc.aft}
      ctp
;

value class_def_or_type_decl char pc ci =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s%c %s%s" pc.bef
         (if ci.MLast.ciVir then " virtual" else "") ci.MLast.ciNam
         (class_type_params {(pc) with bef = ""; aft = ""}
            (snd ci.MLast.ciPrm))
         char
         (class_type {(pc) with bef = ""; aft = ""} ci.MLast.ciExp) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s%c" pc.bef
           (if ci.MLast.ciVir then " virtual" else "")
           ci.MLast.ciNam
           (class_type_params {(pc) with bef = ""; aft = ""}
              (snd ci.MLast.ciPrm))
           char
       in
       let s2 =
         class_type {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
           ci.MLast.ciExp
       in
       sprintf "%s\n%s" s1 s2)
;
value class_def = class_def_or_type_decl ':';
value class_type_decl = class_def_or_type_decl '=';

value class_type_decl_list pc cd =
  horiz_vertic
    (fun () ->
       sprintf "%sclass type %s%s" pc.bef
         (hlist2 class_type_decl (and_before class_type_decl)
            {(pc) with bef = ""; aft = ("", "")} cd)
         pc.aft)
    (fun () ->
       vlist2 class_type_decl (and_before class_type_decl)
         {(pc) with bef = sprintf "%sclass type " pc.bef; aft = ("", pc.aft)}
         cd)
;

value class_decl pc ci =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s= %s%s" pc.bef
         (if ci.MLast.ciVir then "virtual " else "") ci.MLast.ciNam
         (class_type_params {(pc) with bef = ""; aft = ""}
            (snd ci.MLast.ciPrm))
         (class_expr {(pc) with bef = ""; aft = ""} ci.MLast.ciExp) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s=" pc.bef
           (if ci.MLast.ciVir then "virtual " else "")
           ci.MLast.ciNam
           (class_type_params {(pc) with bef = ""; aft = ""}
              (snd ci.MLast.ciPrm))
       in
       let s2 =
         class_expr
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
           ci.MLast.ciExp
       in
       sprintf "%s\n%s" s1 s2)
;

value variant_decl pc pv =
  match pv with
  [ <:poly_variant< `$s$ >> ->
       sprintf "%s`%s%s" pc.bef s pc.aft
  | <:poly_variant< `$s$ of $opt:ao$ $list:tl$ >> ->
       horiz_vertic
         (fun () ->
            sprintf "%s`%s of %s%s%s" pc.bef s (if ao then "& " else "")
              (hlist2 ctyp (amp_before ctyp)
                 {(pc) with bef = ""; aft = ("", "")} tl) pc.aft)
         (fun () -> not_impl "variant_decl 2 vertic" pc s)
  | <:poly_variant< $t$ >> ->
       ctyp pc t ]
;

value variant_decl_list char pc pvl =
  horiz_vertic
    (fun () ->
       hlist2 variant_decl (bar_before variant_decl)
         {(pc) with bef = sprintf "%s[ %c " pc.bef char;
          aft = ("", sprintf " ]%s" pc.aft)}
         pvl)
    (fun () ->
       vlist2 variant_decl (bar_before variant_decl)
         {(pc) with bef = sprintf "%s[ %c " pc.bef char;
          aft = ("", sprintf " ]%s" pc.aft)}
         pvl)
;

value rec class_longident pc cl =
  match cl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [c] -> sprintf "%s%s%s" pc.bef c pc.aft
  | [c :: cl] ->
      sprintf "%s%s.%s" pc.bef c (class_longident {(pc) with bef = ""} cl) ]
;

value binding elem pc (p, e) =
  horiz_vertic
    (fun () ->
       sprintf "%s %s%s" (patt {(pc) with aft = " ="} p)
         (elem {(pc) with bef = ""; aft = ""} e) pc.aft)
    (fun () ->
       sprintf "%s\n%s" (patt {(pc) with aft = " ="} p)
         (elem {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e))
;

value field pc (s, t) =
  horiz_vertic
    (fun () ->
       sprintf "%s%s : %s%s" pc.bef s (ctyp {(pc) with bef = ""; aft = ""} t)
         pc.aft)
    (fun () ->
       let s1 = sprintf "%s%s :" pc.bef s in
       let s2 = ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t in
       sprintf "%s\n%s" s1 s2)
;

value field_expr pc (s, e) =
  horiz_vertic
    (fun () ->
       sprintf "%s%s = %s%s" pc.bef s (expr {(pc) with bef = ""; aft = ""} e)
         pc.aft)
    (fun () -> not_impl "field expr vertic" pc s)
;

value patt_tcon pc p =
  match p with
  [ <:patt< ($p$ : $t$) >> ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s : %s%s" pc.bef
             (patt {(pc) with bef = ""; aft = ""} p)
             (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
        (fun () -> not_impl "patt_tcon vertic" pc p)
  | p -> patt pc p ]
;

value typevar pc tv = sprintf "%s'%s%s" pc.bef tv pc.aft;

value class_object pc (csp, csl) =
  horiz_vertic
    (fun () ->
       sprintf "%sobject%s %s end%s" pc.bef
         (match csp with
          [ Some (<:patt< ($_$ : $_$) >> as p) ->
              patt {(pc) with bef = " "; aft = ""} p
          | Some p -> patt {(pc) with bef = " ("; aft = ")"} p
          | None -> "" ])
         (hlist (semi_after class_str_item)
            {(pc) with bef = ""; aft = ""} csl) pc.aft)
    (fun () ->
       let s1 =
         match csp with
         [ None -> sprintf "%sobject" pc.bef
         | Some p ->
             horiz_vertic
               (fun () ->
                  sprintf "%sobject %s" pc.bef
                    (match p with
                     [ <:patt< ($_$ : $_$) >> ->
                         patt {(pc) with bef = ""; aft = ""} p
                     | p ->
                         patt {(pc) with bef = "("; aft = ")"} p ]))
               (fun () ->
                  not_impl "class_type vertic 1" {(pc) with aft = ""}
                    p) ]
       in
       let s2 =
         vlist (semi_after class_str_item)
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
            aft = ""}
           csl
       in
       let s3 = sprintf "%send%s" (tab pc.ind) pc.aft in
       sprintf "%s\n%s\n%s" s1 s2 s3)
;

(* *)

let lev = find_pr_level "simple" pr_patt.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:patt< ? $s$ >> ->
      fun curr next pc -> sprintf "%s?%s%s" pc.bef s pc.aft
  | <:patt< ? ($p$ $opt:eo$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s?(%s%s)%s" pc.bef
               (patt_tcon {(pc) with bef = ""; aft = ""} p)
               (match eo with
                [ Some e ->
                    sprintf " = %s" (expr {(pc) with bef = ""; aft = ""} e)
                | None -> "" ])
               pc.aft)
          (fun () -> not_impl "patt ?(p=e) vertic" pc p)
  | <:patt< ? $i$ : ($p$ $opt:eo$) >> ->
      fun curr next pc -> failwith "label in pr_ro 3"
  | <:patt< ~ $s$ >> ->
      fun curr next pc -> sprintf "%s~%s%s" pc.bef s pc.aft
  | <:patt< ~ $s$ : $p$ >> ->
      fun curr next pc -> curr {(pc) with bef = sprintf "%s~%s:" pc.bef s} p
  | <:patt< `$uid:s$ >> ->
      fun curr next pc -> sprintf "%s`%s%s" pc.bef s pc.aft
  | <:patt< # $list:sl$ >> ->
      fun curr next pc ->
        mod_ident {(pc) with bef = sprintf "%s#" pc.bef} sl ]
;

let lev = find_pr_level "apply" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< new $list:cl$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%snew %s%s" pc.bef
               (class_longident {(pc) with bef = ""; aft = ""} cl) pc.aft)
          (fun () -> not_impl "new vertic" pc cl)
  | <:expr< object $opt:csp$ $list:csl$ end >> ->
      fun curr next pc ->
        class_object pc (csp, csl) ]
;

value expr_label =
  extfun Extfun.empty with
  [ <:expr< ? $s$ >> ->
      fun curr next pc -> sprintf "%s?%s%s" pc.bef s pc.aft
  | <:expr< ? $i$ : $e$ >> ->
      fun curr next pc -> curr {(pc) with bef = sprintf "%s?%s:" pc.bef i} e
  | <:expr< ~ $s$ >> ->
      fun curr next pc -> sprintf "%s~%s%s" pc.bef s pc.aft
  | <:expr< ~ $s$ : $e$ >> ->
      fun curr next pc ->
        pr_expr.pr_fun "dot" {(pc) with bef = sprintf "%s~%s:" pc.bef s} e
  | z ->
      fun curr next pc -> next pc z ]
;

let lev = find_pr_level "dot" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< $e$ # $s$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s#%s%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} e) s pc.aft)
          (fun () -> not_impl "# vertic" pc e) ]
;

let lev = find_pr_level "simple" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< ( $e$ : $t$ :> $t2$ ) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s :> %s)%s" pc.bef
               (expr {(pc) with bef = ""; aft = ""} e)
               (ctyp {(pc) with bef = ""; aft = ""} t)
               (ctyp {(pc) with bef = ""; aft = ""} t2) pc.aft)
          (fun () ->
             let s1 =
               expr {(pc) with bef = sprintf "%s(" pc.bef; aft = " :"} e
             in
             let s2 =
               ctyp {(pc) with bef = tab (pc.ind + 1); aft = " :>"} t
             in
             let s3 =
               ctyp
                 {(pc) with bef = tab (pc.ind + 1);
                  aft = sprintf ")%s" pc.aft}
                 t2
             in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:expr< ( $e$ :> $t$ ) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s :> %s)%s" pc.bef
               (expr {(pc) with bef = ""; aft = ""} e)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               expr
                 {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
                  aft = " :>"}
                 e
             in
             let s2 =
               ctyp
                 {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                  aft = sprintf ")%s" pc.aft}
                 t
             in
             sprintf "%s\n%s" s1 s2)
  | <:expr< {< $list:fel$ >} >> ->
      fun curr next pc ->
        if fel = [] then sprintf "%s{< >}%s" pc.bef pc.aft
        else
          let fel = List.map (fun fe -> (fe, ";")) fel in
          plist field_expr 3
            {(pc) with bef = sprintf "%s{< " pc.bef;
             aft = sprintf " >}%s" pc.aft}
            fel
  | <:expr< new $list:_$ >> as z ->
      fun curr next pc ->
        expr
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
          z ]
;

let lev = find_pr_level "simple" pr_ctyp.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:ctyp< ? $i$ : $t$ >> ->
      fun curr next pc -> ctyp {(pc) with bef = sprintf "%s?%s:" pc.bef i} t
  | <:ctyp< ~ $i$ : $t$ >> ->
      fun curr next pc -> ctyp {(pc) with bef = sprintf "%s~%s:" pc.bef i} t
  | <:ctyp< < $list:ml$ $opt:v$ > >> ->
      fun curr next pc ->
        if ml = [] then
          sprintf "%s<%s >%s" pc.bef (if v then " .." else "") pc.aft
        else
          let ml = List.map (fun e -> (e, ";")) ml in
          plist field 0
            {(pc) with ind = pc.ind + 2; bef = sprintf "%s< " pc.bef;
             aft = sprintf "%s >%s" (if v then " .." else "") pc.aft}
            ml
  | <:ctyp< # $list:id$ >> ->
      fun curr next pc ->
        class_longident {(pc) with bef = sprintf "%s#" pc.bef}  id
  | <:ctyp< [ = $list:pvl$ ] >> ->
      fun curr next pc -> variant_decl_list '=' pc pvl
  | <:ctyp< [ > $list:pvl$ ] >> ->
      fun curr next pc -> variant_decl_list '>' pc pvl
  | <:ctyp< [ < $list:pvl$ ] >> ->
      fun curr next pc -> variant_decl_list '<' pc pvl
  | <:ctyp< [ < $list:pvl$ > $list:_$ ] >> ->
      fun curr next pc -> not_impl "variants 4" pc pvl
  | <:ctyp< $_$ as $_$ >> as z ->
      fun curr next pc ->
        ctyp
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
          z ]
;

let lev = find_pr_level "top" pr_sig_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:sig_item< class $list:cd$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass %s%s" pc.bef
               (hlist2 class_def (and_before class_def)
                  {(pc) with bef = ""; aft = ("", "")} cd)
               pc.aft)
          (fun () ->
             vlist2 class_def (and_before class_def)
               {(pc) with bef = sprintf "%sclass " pc.bef; aft = ("", pc.aft)}
               cd)
  | <:sig_item< class type $list:cd$ >> ->
      fun curr next pc -> class_type_decl_list pc cd ]
;

let lev = find_pr_level "top" pr_str_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:str_item< class $list:cd$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass %s%s" pc.bef
               (hlist2 class_decl (and_before class_decl)
                  {(pc) with bef = ""; aft = ("", "")} cd)
               pc.aft)
          (fun () ->
             vlist2 class_decl (and_before class_decl)
               {(pc) with bef = sprintf "%sclass " pc.bef; aft = ("", pc.aft)}
               cd)
  | <:str_item< class type $list:cd$ >> ->
      fun curr next pc -> class_type_decl_list pc cd ]
;

value class_type_top =
  extfun Extfun.empty with
  [ <:class_type< [ $t$ ] -> $ct$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s[%s] -> %s%s" pc.bef
               (ctyp {(pc) with bef = ""; aft = ""} t)
               (curr {(pc) with bef = ""; aft = ""} ct) pc.aft)
          (fun () ->
             let s1 =
               ctyp {(pc) with bef = sprintf "%s[" pc.bef; aft = "] ->"} t
             in
             let s2 =
               curr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} ct
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_type< object $opt:cst$ $list:csi$ end >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             if alone_in_line pc then
               (* Heuristic : I don't like to print it horizontally
                  when alone in a line. *)
               sprintf "\n"
             else
               sprintf "%sobject%s %s end%s" pc.bef
                 (match cst with
                 [ Some t ->
                      sprintf " (%s)" (ctyp {(pc) with bef = ""; aft = ""} t)
                  | None -> "" ])
                 (hlist (semi_after class_sig_item)
                    {(pc) with bef = ""; aft = ""} csi) pc.aft)
          (fun () ->
             let s1 =
               match cst with
               [ None -> sprintf "%sobject" pc.bef
               | Some t ->
                   horiz_vertic
                     (fun () ->
                        sprintf "%sobject (%s)" pc.bef
                          (ctyp {(pc) with bef = ""; aft = ""} t))
                     (fun () ->
                        not_impl "class_type vertic 1" {(pc) with aft = ""}
                          t) ]
             in
             let s2 =
               vlist (semi_after class_sig_item)
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 csi
             in
             let s3 = sprintf "%send%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:class_type< $list:cl$ >> ->
      fun curr next pc -> class_longident pc cl
  | <:class_type< $list:cl$ [ $list:ctcl$ ] >> ->
      fun curr next pc ->
        let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
        horiz_vertic
          (fun  () ->
             sprintf "%s%s [%s]%s" pc.bef
               (class_longident {(pc) with bef = ""; aft = ""} cl)
               (plist ctyp 0 {(pc) with bef = ""; aft = ""} ctcl)
               pc.aft)
          (fun  () -> not_impl "class_type c [t, t] vertic" pc cl)
  | z -> fun curr next pc -> not_impl "class_type" pc z ]
;

value class_expr_top =
  extfun Extfun.empty with
  [ <:class_expr< fun $p$ -> $ce$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sfun %s -> %s%s" pc.bef
               (patt {(pc) with bef = ""; aft = ""} p)
               (curr {(pc) with bef = ""; aft = ""} ce) pc.aft)
          (fun () ->
             let s1 =
               patt {(pc) with bef = sprintf "%sfun " pc.bef; aft = " ->"} p
             in
             let s2 =
               curr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} ce
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_expr< let $opt:rf$ $list:pel$ in $ce$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             let s1 =
               hlist2 (binding expr) (and_before (binding expr))
                 {(pc) with
                  bef = sprintf "%slet %s" pc.bef (if rf then "rec " else "");
                  aft = ("", " in")}
                 pel
             in
             let s2 = class_expr {(pc) with bef = ""} ce in
             sprintf "%s %s" s1 s2)
          (fun () ->
             let s1 =
               vlist2 (binding expr) (and_before (binding expr))
                 {(pc) with
                  bef = sprintf "%slet %s" pc.bef (if rf then "rec " else "");
                  aft = ("", " in")}
                 pel
             in
             let s2 = class_expr {(pc) with bef = tab pc.ind} ce in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next pc -> next pc z ]
;

value class_expr_apply =
  extfun Extfun.empty with
  [ <:class_expr< $ce$ $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s %s%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} ce)
               (pr_expr.pr_fun "label" {(pc) with bef = ""; aft = ""} e)
               pc.aft)
          (fun () -> not_impl "class_expr_apply" pc ce)
  | z -> fun curr next pc -> next pc z ]
;

value class_expr_simple =
  extfun Extfun.empty with
  [ <:class_expr< $list:cl$ >> ->
      fun curr next pc -> class_longident pc cl
  | <:class_expr< $list:cl$ [ $list:ctcl$ ] >> ->
      fun curr next pc ->
        let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
        horiz_vertic
          (fun  () ->
             sprintf "%s%s [%s]%s" pc.bef
               (class_longident {(pc) with bef = ""; aft = ""} cl)
               (plist ctyp 0 {(pc) with bef = ""; aft = ""} ctcl)
               pc.aft)
          (fun  () -> not_impl "class_expr c [t, t] vertic" pc cl)
  | <:class_expr< object $opt:csp$ $list:csl$ end >> ->
      fun curr next pc ->
        class_object pc (csp, csl)      
  | <:class_expr< ($ce$ : $ct$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s)%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} ce)
               (class_type {(pc) with bef = ""; aft = ""} ct) pc.aft)
          (fun () ->
             let s1 =
               curr
                 {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
                  aft = " :"}
                 ce
             in
             let s2 =
               class_type
                 {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                  aft = sprintf ")%s" pc.aft}
                 ct
             in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next pc -> not_impl "class_expr" pc z ]
;

value class_sig_item_top =
  extfun Extfun.empty with
  [ <:class_sig_item< inherit $ct$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sinherit %s%s" pc.bef
               (class_type {(pc) with bef = ""; aft = ""} ct) pc.aft)
          (fun () -> not_impl "class_sig_item inherit vertic" pc ct)
  | <:class_sig_item< method $opt:priv$ $s$ : $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod%s %s : %s%s" pc.bef
               (if priv then " private" else "") s
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () -> not_impl "method vertic 1" pc s)
  | <:class_sig_item< value $opt:mf$ $s$ : $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%svalue%s %s : %s%s" pc.bef
               (if mf then " mutable" else "")
               (var_escaped {(pc) with bef = ""; aft = ""} s)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               sprintf "%svalue%s %s :" pc.bef (if mf then " mutable" else "")
                 (var_escaped {(pc) with bef = ""; aft = ""} s)
             in
             let s2 =
               ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
             in
             sprintf "%s\n%s" s1 s2) 
  | z -> fun curr next pc -> not_impl "class_sig_item" pc z ]
;

value class_str_item_top =
  extfun Extfun.empty with
  [ <:class_str_item< inherit $ce$ $opt:pb$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sinherit %s%s%s" pc.bef
               (class_expr {(pc) with bef = ""; aft = ""} ce)
               (match pb with
                [ Some s -> sprintf " as %s" s
                | None -> "" ]) pc.aft)
          (fun () -> not_impl "inherit vertic" pc ce)
  | <:class_str_item< initializer $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sinitializer %s%s" pc.bef
               (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             let s1 = sprintf "%sinitializer" pc.bef in
             let s2 =
               expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< method virtual $opt:priv$ $s$ : $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod virtual%s %s : %s%s" pc.bef
               (if priv then " private" else "") s
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%smethod virtual%s %s :" pc.bef
                      (if priv then " private" else "") s)
                 (fun () -> not_impl "method vertic 2" pc s)
             in
             let s2 =
               ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< method $opt:priv$ $s$ $opt:topt$ = $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod%s %s%s = %s%s" pc.bef
               (if priv then " private" else "") s
               (match topt with
                [ Some t ->
                    sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
                | None -> "" ])
               (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             let s1 =
               match topt with
               [ None ->
                   sprintf "%smethod%s %s =" pc.bef
                     (if priv then " private" else "") s
               | Some t ->
                   horiz_vertic
                     (fun () ->
                        sprintf "%smethod%s %s : %s =" pc.bef
                          (if priv then " private" else "") s
                          (ctyp {(pc) with bef = ""; aft = ""} t))
                     (fun () ->
                        let s1 =
                          sprintf "%smethod%s %s :" pc.bef
                            (if priv then " private" else "") s
                        in
                        let s2 =
                          ctyp
                            {(pc) with ind = pc.ind + 4;
                             bef = tab (pc.ind + 4); aft = " ="}
                            t
                        in
                        sprintf "%s\n%s" s1 s2) ]
             in
             let s2 =
               expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< type $t1$ = $t2$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%stype %s = %s%s" pc.bef
               (ctyp {(pc) with bef = ""; aft = ""} t1)
               (ctyp {(pc) with bef = ""; aft = ""} t2) pc.aft)
          (fun () -> not_impl "class_str_item type vertic" pc t1)
  | <:class_str_item< value $opt:mf$ $s$ = $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%svalue%s %s = %s%s" pc.bef
               (if mf then " mutable" else "") s
               (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             let s1 =
               sprintf "%svalue%s %s =" pc.bef (if mf then " mutable" else "")
                 s
             in
             let s2 =
               expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
             in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next pc -> not_impl "class_str_item" pc z ]
;

value ctyp_as =
  extfun Extfun.empty with
  [ <:ctyp< $t1$ as $t2$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s as %s%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} t1)
               (next {(pc) with bef = ""; aft = ""} t2) pc.aft)
          (fun () -> not_impl "ctyp as vertic" pc t1)
  | z -> fun curr next pc -> next pc z ]
;

value ctyp_poly =
  extfun Extfun.empty with
  [ <:ctyp< ! $list:pl$ . $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s! %s . %s%s" pc.bef
               (hlist typevar {(pc) with bef = ""; aft = ""} pl)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               sprintf "%s! %s ." pc.bef
                 (hlist typevar {(pc) with bef = ""; aft = ""} pl)
             in
             let s2 =
               ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
             in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next pc -> next pc z ]
;

pr_expr.pr_levels :=
  [find_pr_level "top" pr_expr.pr_levels;
   find_pr_level "ass" pr_expr.pr_levels;
   find_pr_level "bar" pr_expr.pr_levels;
   find_pr_level "amp" pr_expr.pr_levels;
   find_pr_level "less" pr_expr.pr_levels;
   find_pr_level "concat" pr_expr.pr_levels;
   find_pr_level "add" pr_expr.pr_levels;
   find_pr_level "mul" pr_expr.pr_levels;
   find_pr_level "pow" pr_expr.pr_levels;
   find_pr_level "unary" pr_expr.pr_levels;
   find_pr_level "apply" pr_expr.pr_levels;
   {pr_label = "label"; pr_rules = expr_label};
   find_pr_level "dot" pr_expr.pr_levels;
   find_pr_level "simple" pr_expr.pr_levels]
;

pr_ctyp.pr_levels :=
  [find_pr_level "top" pr_ctyp.pr_levels;
   {pr_label = "as"; pr_rules = ctyp_as};
   {pr_label = "poly"; pr_rules = ctyp_poly};
   find_pr_level "arrow" pr_ctyp.pr_levels;
   find_pr_level "apply" pr_ctyp.pr_levels;
   find_pr_level "dot" pr_ctyp.pr_levels;
   find_pr_level "simple" pr_ctyp.pr_levels]
;

pr_class_expr.pr_levels :=
  [{pr_label = "top"; pr_rules = class_expr_top};
   {pr_label = "apply"; pr_rules = class_expr_apply};
   {pr_label = "simple"; pr_rules = class_expr_simple}]
;

pr_class_type.pr_levels :=
  [{pr_label = "top"; pr_rules = class_type_top}]
;

pr_class_sig_item.pr_levels :=
  [{pr_label = "top"; pr_rules = class_sig_item_top}]
;

pr_class_str_item.pr_levels :=
  [{pr_label = "top"; pr_rules = class_str_item_top}]
;
