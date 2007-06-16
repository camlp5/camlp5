(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_ro.ml,v 1.18 2007/06/16 07:44:17 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* Pretty printing extension for objects and labels *)

open Pretty;
open Pcaml.NewPrinters;
open Prtools;

value not_impl name ctx b x k =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_ro, not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value expr ctx b z k = pr_expr.pr_fun "top" ctx b z k;
value patt ctx b z k = pr_patt.pr_fun "top" ctx b z k;
value ctyp ctx b z k = pr_ctyp.pr_fun "top" ctx b z k;
value class_expr ctx b z k = pr_class_expr.pr_fun "top" ctx b z k;
value class_type ctx b z k = pr_class_type.pr_fun "top" ctx b z k;
value class_str_item ctx b z k = pr_class_str_item.pr_fun "top" ctx b z k;
value class_sig_item ctx b z k = pr_class_sig_item.pr_fun "top" ctx b z k;

value semi_after elem ctx b x k = elem ctx b x (sprintf ";%s" k);
value amp_before elem ctx b x k = elem ctx (sprintf "%s& " b) x k;
value and_before elem ctx b x k = elem ctx (sprintf "%sand " b) x k;
value bar_before elem ctx b x k = elem ctx (sprintf "%s| " b) x k;

value class_type_params ctx b ctp k =
  if ctp = [] then sprintf "%s%s" b k
  else not_impl "class_type_params" ctx b ctp k
;

value class_def_or_type_decl char ctx b ci k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s%c %s%s" b
         (if ci.MLast.ciVir then " virtual" else "") ci.MLast.ciNam
         (class_type_params 0 "" (snd ci.MLast.ciPrm) "") char
         (class_type ctx "" ci.MLast.ciExp "") k)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s%c" b (if ci.MLast.ciVir then " virtual" else "")
           ci.MLast.ciNam (class_type_params ctx "" (snd ci.MLast.ciPrm) "")
           char
       in
       let s2 = class_type (shi ctx 2) (tab (shi ctx 2)) ci.MLast.ciExp k in
       sprintf "%s\n%s" s1 s2)
;
value class_def = class_def_or_type_decl ':';
value class_type_decl = class_def_or_type_decl '=';

value class_type_decl_list ctx b cd k =
  horiz_vertic
    (fun () ->
       sprintf "%sclass type %s%s" b
         (hlist2 class_type_decl (and_before class_type_decl) ctx "" cd
            ("", ""))
         k)
    (fun () ->
       vlist2 class_type_decl (and_before class_type_decl) ctx
         (sprintf "%sclass type " b) cd ("", k))
;

value class_decl ctx b ci k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s= %s%s" b (if ci.MLast.ciVir then "virtual " else "")
         ci.MLast.ciNam (class_type_params  ctx "" (snd ci.MLast.ciPrm) "")
         (class_expr ctx "" ci.MLast.ciExp "") k)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s=" b (if ci.MLast.ciVir then "virtual " else "")
           ci.MLast.ciNam (class_type_params  ctx "" (snd ci.MLast.ciPrm) "")
       in
       let s2 = class_expr (shi ctx 2) (tab (shi ctx 2)) ci.MLast.ciExp k in
       sprintf "%s\n%s" s1 s2)
;

value variant_decl ctx b pv k =
  match pv with
  [ <:poly_variant< `$s$ >> ->
       sprintf "%s`%s%s" b s k
  | <:poly_variant< `$s$ of $opt:ao$ $list:tl$ >> ->
       horiz_vertic
         (fun () ->
            sprintf "%s`%s of %s%s%s" b s (if ao then "& " else "")
              (hlist2 ctyp (amp_before ctyp) ctx "" tl ("", "")) k)
         (fun () -> not_impl "variant_decl 2 vertic" ctx b s k)
  | <:poly_variant< $t$ >> ->
       ctyp ctx b t k ]
;

value rec class_longident ctx b cl k =
  match cl with
  [ [] -> sprintf "%s%s" b k
  | [c] -> sprintf "%s%s%s" b c k
  | [c :: cl] -> sprintf "%s%s.%s" b c (class_longident ctx "" cl k) ]
;

value binding elem ctx b (p, e) k =
  horiz_vertic
    (fun () -> sprintf "%s %s%s" (patt ctx b p " =") (elem ctx "" e "") k)
    (fun () ->
       sprintf "%s\n%s" (patt ctx b p " =")
         (elem (shi ctx 2) (tab (shi ctx 2)) e k))
;

value field ctx b (s, t) k =
  horiz_vertic (fun () -> sprintf "%s%s : %s%s" b s (ctyp ctx "" t "") k)
    (fun () -> not_impl "field vertic" ctx b s k)
;

value patt_tcon ctx b p k =
  match p with
  [ <:patt< ($p$ : $t$) >> ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s : %s%s" b (patt ctx "" p "") (ctyp ctx "" t "") k)
        (fun () -> not_impl "patt_tcon vertic" ctx b p k)
  | p -> patt ctx b p k ]
;

value typevar ctx b tv k = sprintf "%s'%s%s" b tv k;

(* *)

let lev = find_pr_level "simple" pr_patt.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:patt< ? $s$ >> ->
      fun curr next ctx b k -> sprintf "%s?%s%s" b s k
  | <:patt< ? ($p$ $opt:eo$) >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s?(%s%s)%s" b (patt_tcon ctx "" p "")
               (match eo with
                [ Some e -> sprintf " = %s" (expr ctx "" e "")
                | None -> "" ])
               k)
          (fun () -> not_impl "patt ?(p=e) vertic" ctx b p k)
  | <:patt< ? $i$ : ($p$ $opt:eo$) >> ->
      fun curr next ctx b k -> failwith "label in pr_ro 3"
  | <:patt< ~ $s$ >> ->
      fun curr next ctx b k -> sprintf "%s~%s%s" b s k
  | <:patt< ~ $s$ : $p$ >> ->
      fun curr next ctx b k -> curr ctx (sprintf "%s~%s:" b s) p k
  | <:patt< `$uid:s$ >> ->
      fun curr next ctx b k -> sprintf "%s`%s%s" b s k ]
;

let lev = find_pr_level "apply" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< new $list:cl$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () -> sprintf "%snew %s%s" b (class_longident ctx "" cl "") k)
          (fun () -> not_impl "new vertic" ctx b cl k) ]
;

let lev = find_pr_level "dot" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< $e$ # $s$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () -> sprintf "%s%s#%s%s" b (curr ctx "" e "") s k)
          (fun () -> not_impl "# vertic" ctx b e k) ]
;

let lev = find_pr_level "simple" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< ( $e$ : $t$ :> $t2$ ) >> ->
      fun curr next ctx b k -> not_impl "expr : :>" ctx b e k
  | <:expr< ( $e$ :> $t$ ) >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s :> %s)%s" b (expr ctx "" e "") (ctyp ctx "" t "")
               k)
          (fun () ->
             let s1 = expr (shi ctx 1) (sprintf "%s(" b) e " :>" in
             let s2 =
               ctyp (shi ctx 1) (tab (shi ctx 1)) t (sprintf ")%s" k)
             in
             sprintf "%s\n%s" s1 s2)
  | <:expr< ? $s$ >> ->
      fun curr next ctx b k -> sprintf "%s?%s%s" b s k
  | <:expr< ~ $s$ >> ->
      fun curr next ctx b k -> sprintf "%s~%s%s" b s k
  | <:expr< ~ $s$ : $e$ >> ->
      fun curr next ctx b k ->
        pr_expr.pr_fun "dot" ctx (sprintf "%s~%s:" b s) e k ]
;

let lev = find_pr_level "simple" pr_ctyp.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:ctyp< ? $i$ : $t$ >> ->
      fun curr next ctx b k -> ctyp ctx (sprintf "%s?%s:" b i) t k
  | <:ctyp< ~ $i$ : $t$ >> ->
      fun curr next ctx b k -> ctyp ctx (sprintf "%s~%s:" b i) t k
  | <:ctyp< < $list:ml$ $opt:v$ > >> ->
      fun curr next ctx b k ->
        if ml = [] then sprintf "%s<%s >%s" b (if v then " .." else "") k
        else
          let ml = List.map (fun e -> (e, ";")) ml in
          plist field 0 (shi ctx 2) (sprintf "%s< " b) ml
            (sprintf "%s >%s" (if v then " .." else "") k)
  | <:ctyp< [ = $list:pvl$ ] >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             hlist2 variant_decl (bar_before variant_decl) ctx
               (sprintf "%s[ = " b) pvl ("", sprintf " ]%s" k))
          (fun () ->
             vlist2 variant_decl (bar_before variant_decl) ctx
               (sprintf "%s[ = " b) pvl ("", sprintf " ]%s" k))
  | <:ctyp< [ > $list:pvl$ ] >> ->
      fun curr next ctx b k -> not_impl "variants 2" ctx b pvl k
  | <:ctyp< [ < $list:pvl$ ] >> ->
      fun curr next ctx b k -> not_impl "variants 3" ctx b pvl k
  | <:ctyp< [ < $list:pvl$ > $list:_$ ] >> ->
      fun curr next ctx b k -> not_impl "variants 4" ctx b pvl k
  | <:ctyp< $_$ as $_$ >> as z ->
      fun curr next ctx b k ->
        ctyp (shi ctx 1) (sprintf "%s(" b) z (sprintf ")%s" k) ]
;

let lev = find_pr_level "top" pr_sig_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:sig_item< class $list:cd$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass %s%s" b
               (hlist2 class_def (and_before class_def) ctx "" cd ("", "")) k)
          (fun () ->
             vlist2 class_def (and_before class_def) ctx
               (sprintf "%sclass " b) cd ("", k))
  | <:sig_item< class type $list:cd$ >> ->
      fun curr next ctx b k -> class_type_decl_list ctx b cd k ]
;

let lev = find_pr_level "top" pr_str_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:str_item< class $list:cd$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass %s%s" b
               (hlist2 class_decl (and_before class_decl) ctx "" cd ("", ""))
               k)
          (fun () ->
             vlist2 class_decl (and_before class_decl) ctx
               (sprintf "%sclass " b) cd ("", k))
  | <:str_item< class type $list:cd$ >> ->
      fun curr next ctx b k -> class_type_decl_list ctx b cd k ]
;

value class_type_top =
  extfun Extfun.empty with
  [ <:class_type< object $opt:cst$ $list:csi$ end >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sobject%s %s end%s" b
               (match cst with
                [ Some t -> sprintf " (%s)" (ctyp ctx "" t "")
                | None -> "" ])
               (hlist (semi_after class_sig_item) ctx "" csi "") k)
          (fun () ->
             let s1 =
               match cst with
               [ None -> sprintf "%sobject" b
               | Some t ->
                   horiz_vertic
                     (fun () -> sprintf "%sobject (%s)" b (ctyp ctx "" t ""))
                     (fun () -> not_impl "class_type vertic 1" ctx b t "") ]
             in
             let s2 =
               vlist (semi_after class_sig_item) (shi ctx 2) (tab (shi ctx 2))
                 csi ""
             in
             let s3 = sprintf "%send%s" (tab ctx) k in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | z -> fun curr next ctx b k -> not_impl "class_type" ctx b z k ]
;

value class_expr_top =
  extfun Extfun.empty with
  [ <:class_expr< let $opt:rf$ $list:pel$ in $ce$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             let s1 =
               hlist2 (binding expr) (and_before (binding expr)) ctx
                 (sprintf "%slet %s" b (if rf then "rec " else ""))
                 pel ("", " in")
             in
             let s2 = class_expr ctx "" ce k in
             sprintf "%s %s" s1 s2)
          (fun () ->
             let s1 =
               vlist2 (binding expr) (and_before (binding expr)) ctx
                 (sprintf "%slet %s" b (if rf then "rec " else ""))
                 pel ("", " in")
             in
             let s2 = class_expr ctx (tab ctx) ce k in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next ctx b k -> next ctx b z k ]
;

value class_expr_simple =
  extfun Extfun.empty with
  [ <:class_expr< $list:cl$ >> ->
      fun curr next ctx b k -> class_longident ctx b cl k
  | <:class_expr< object $opt:csp$ $list:csl$ end >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sobject%s %s end%s" b
               (match csp with
                [ Some (<:patt< ($_$ : $_$) >> as p) -> patt ctx " " p ""
                | Some p -> patt ctx " (" p ")"
                | None -> "" ])
               (hlist (semi_after class_str_item) ctx "" csl "") k)
          (fun () ->
             let s1 =
               match csp with
               [ None -> sprintf "%sobject" b
               | Some p ->
                   horiz_vertic
                     (fun () ->
                        sprintf "%sobject %s" b
                          (match p with
                           [ <:patt< ($_$ : $_$) >> -> patt ctx "" p ""
                           | p -> patt ctx "(" p ")" ]))
                     (fun () -> not_impl "class_type vertic 1" ctx b p "") ]
             in
             let s2 =
               vlist (semi_after class_str_item) (shi ctx 2) (tab (shi ctx 2))
                 csl ""
             in
             let s3 = sprintf "%send%s" (tab ctx) k in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | z -> fun curr next ctx b k -> not_impl "class_expr" ctx b z k ]
;

value class_sig_item_top =
  extfun Extfun.empty with
  [ <:class_sig_item< method $opt:priv$ $s$ : $t$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod%s %s : %s%s" b
               (if priv then " private" else "") s (ctyp ctx "" t "") k)
          (fun () -> not_impl "method vertic 1" ctx b s k)
  | z -> fun curr next ctx b k -> not_impl "class_sig_item" ctx b z k ]
;

value class_str_item_top =
  extfun Extfun.empty with
  [ <:class_str_item< inherit $ce$ $opt:pb$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sinherit %s%s%s" b (class_expr ctx "" ce "")
               (match pb with
                [ Some s -> sprintf " as %s" s
                | None -> "" ]) k)
          (fun () -> not_impl "inherit vertic" ctx b ce k)
  | <:class_str_item< initializer $e$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () -> sprintf "%sinitializer %s%s" b (expr ctx "" e "") k)
          (fun () ->
             let s1 = sprintf "%sinitializer" b in
             let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< method virtual $opt:priv$ $s$ : $t$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod virtual%s %s : %s%s" b
               (if priv then " private" else "") s (ctyp ctx "" t "") k)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%smethod virtual%s %s :" b
                      (if priv then " private" else "") s)
                 (fun () -> not_impl "method vertic 2" ctx b s k)
             in
             let s2 = ctyp (shi ctx 2) (tab (shi ctx 2)) t k in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< method $opt:priv$ $s$ $opt:topt$ = $e$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod%s %s%s = %s%s" b
               (if priv then " private" else "") s
               (match topt with
                [ Some t -> sprintf " : %s" (ctyp ctx "" t "")
                | None -> "" ])
               (expr ctx "" e "") k)
          (fun () ->
             let s1 =
               match topt with
               [ None ->
                   sprintf "%smethod%s %s =" b
                     (if priv then " private" else "") s
               | Some t ->
                   horiz_vertic
                     (fun () ->
                        sprintf "%smethod%s %s : %s =" b
                          (if priv then " private" else "") s
                          (ctyp ctx "" t ""))
                     (fun () ->
                        let s1 =
                          sprintf "%smethod%s %s :" b
                            (if priv then " private" else "") s
                        in
                        let s2 = ctyp (shi ctx 4) (tab (shi ctx 4)) t " =" in
                        sprintf "%s\n%s" s1 s2) ]
             in
             let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< value $opt:mf$ $s$ = $e$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%svalue%s %s = %s%s" b
               (if mf then " mutable" else "") s (expr ctx "" e "") k)
          (fun () ->
             let s1 =
               sprintf "%svalue%s %s =" b (if mf then " mutable" else "") s
             in
             let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next ctx b k -> not_impl "class_str_item" ctx b z k ]
;

value ctyp_as =
  extfun Extfun.empty with
  [ <:ctyp< $t1$ as $t2$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s as %s%s" b (curr ctx "" t1 "") (next ctx "" t2 "")
               k)
          (fun () -> not_impl "ctyp as vertic" ctx b t1 k)
  | z -> fun curr next ctx b k -> next ctx b z k ]
;

value ctyp_poly =
  extfun Extfun.empty with
  [ <:ctyp< ! $list:pl$ . $t$ >> ->
      fun curr next ctx b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s! %s . %s%s" b (hlist typevar ctx "" pl "")
               (ctyp ctx "" t "") k)
          (fun () ->
             let s1 = sprintf "%s! %s ." b (hlist typevar ctx "" pl "") in
             let s2 = ctyp (shi ctx 2) (tab (shi ctx 2)) t k in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next ctx b k -> next ctx b z k ]
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
