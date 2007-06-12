(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_ro.ml,v 1.12 2007/06/12 03:44:24 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* Pretty printing extension for objects and labels *)

open Pcaml.NewPrinter;
open Sformat;

value not_impl name ind b x k =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_ro, not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value expr ind b z k = pr_expr.pr_fun "top" ind b z k;
value patt ind b z k = pr_patt.pr_fun "top" ind b z k;
value ctyp ind b z k = pr_ctyp.pr_fun "top" ind b z k;
value class_expr ind b z k = pr_class_expr.pr_fun "top" ind b z k;
value class_type ind b z k = pr_class_type.pr_fun "top" ind b z k;
value class_str_item ind b z k = pr_class_str_item.pr_fun "top" ind b z k;
value class_sig_item ind b z k = pr_class_sig_item.pr_fun "top" ind b z k;

value zc = {ind = 0};
value shi ctx sh = {ind = ctx.ind + sh};
value tab ctx = String.make ctx.ind ' ';

value rec hlist2 elem elem2 ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] ->
      sprintf "%s %s" (elem ind b x "") (hlist2 elem2 elem2 ind "" xl k) ]
;

value hlist elem ind b xl k = hlist2 elem elem ind b xl k;

value rec vlist2 elem elem2 ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ind b x "")
        (vlist2 elem2 elem2 ind (tab ind) xl k) ]
;

value vlist elem ind b xl k = vlist2 elem elem ind b xl k;

value rec plistl elem eleml ind sh b xl k =
  match xl with
  [ [] -> assert False
  | [(x, _)] -> eleml ind b x k
  | [(x, sep) :: xl] ->
      let s =
        horiz_vertic (fun () -> Some (elem ind b x sep)) (fun () -> None)
      in
      match s with
      [ Some b ->
          loop b xl where rec loop b =
            fun
            [ [] -> assert False
            | [(x, _)] ->
                horiz_vertic (fun () -> eleml ind (sprintf "%s " b) x k)
                  (fun () ->
                     let s = eleml (shi ind sh) (tab (shi ind sh)) x k in
                     sprintf "%s\n%s" b s)
            | [(x, sep) :: xl] ->
                let s =
                  horiz_vertic
                    (fun () -> Some (elem ind (sprintf "%s " b) x sep))
                    (fun () -> None)
                in
                match s with
                [ Some b -> loop b xl
                | None ->
                    let s =
                      plistl elem eleml (shi ind sh) 0 (tab (shi ind sh))
                        [(x, sep) :: xl] k
                    in
                    sprintf "%s\n%s" b s ] ]
      | None ->
          let s1 = elem ind b x sep in
          let s2 = plistl elem eleml (shi ind sh) 0 (tab (shi ind sh)) xl k in
          sprintf "%s\n%s" s1 s2 ] ]
;
value plist elem ind sh b xl k = plistl elem elem ind sh b xl k;

value semi_after elem ind b x k = elem ind b x (sprintf ";%s" k);
value amp_before elem ind b x k = elem ind (sprintf "%s& " b) x k;
value and_before elem ind b x k = elem ind (sprintf "%sand " b) x k;
value bar_before elem ind b x k = elem ind (sprintf "%s| " b) x k;

value class_type_params ind b ctp k =
  if ctp = [] then sprintf "%s%s" b k
  else not_impl "class_type_params" ind b ctp k
;

value class_def_or_type_decl char ind b ci k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s%c %s%s" b
         (if ci.MLast.ciVir then " virtual" else "") ci.MLast.ciNam
         (class_type_params 0 "" (snd ci.MLast.ciPrm) "") char
         (class_type zc "" ci.MLast.ciExp "") k)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s%c" b (if ci.MLast.ciVir then " virtual" else "")
           ci.MLast.ciNam (class_type_params zc "" (snd ci.MLast.ciPrm) "")
           char
       in
       let s2 = class_type (shi ind 2) (tab (shi ind 2)) ci.MLast.ciExp k in
       sprintf "%s\n%s" s1 s2)
;
value class_def = class_def_or_type_decl ':';
value class_type_decl = class_def_or_type_decl '=';

value class_type_decl_list ind b cd k =
  horiz_vertic
    (fun () ->
       sprintf "%sclass type %s%s" b
         (hlist2 class_type_decl (and_before class_type_decl) zc "" cd
            "")
         k)
    (fun () ->
       vlist2 class_type_decl (and_before class_type_decl) ind
         (sprintf "%sclass type " b) cd k)
;

value class_decl ind b ci k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s= %s%s" b (if ci.MLast.ciVir then "virtual " else "")
         ci.MLast.ciNam (class_type_params  zc "" (snd ci.MLast.ciPrm) "")
         (class_expr zc "" ci.MLast.ciExp "") k)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s=" b (if ci.MLast.ciVir then "virtual " else "")
           ci.MLast.ciNam (class_type_params  zc "" (snd ci.MLast.ciPrm) "")
       in
       let s2 = class_expr (shi ind 2) (tab (shi ind 2)) ci.MLast.ciExp k in
       sprintf "%s\n%s" s1 s2)
;

value variant_decl ind b pv k =
  match pv with
  [ <:poly_variant< `$s$ >> ->
       sprintf "%s`%s%s" b s k
  | <:poly_variant< `$s$ of $opt:ao$ $list:tl$ >> ->
       horiz_vertic
         (fun () ->
            sprintf "%s`%s of %s%s%s" b s (if ao then "& " else "")
              (hlist2 ctyp (amp_before ctyp) zc "" tl "") k)
         (fun () -> not_impl "variant_decl 2 vertic" ind b s k)
  | <:poly_variant< $t$ >> ->
       ctyp ind b t k ]
;

value rec class_longident ind b cl k =
  match cl with
  [ [] -> sprintf "%s%s" b k
  | [c] -> sprintf "%s%s%s" b c k
  | [c :: cl] -> sprintf "%s%s.%s" b c (class_longident ind "" cl k) ]
;

value binding elem ind b (p, e) k =
  horiz_vertic
    (fun () -> sprintf "%s %s%s" (patt zc b p " =") (elem zc "" e "") k)
    (fun () ->
       sprintf "%s\n%s" (patt ind b p " =")
         (elem (shi ind 2) (tab (shi ind 2)) e k))
;

value field ind b (s, t) k =
  horiz_vertic (fun () -> sprintf "%s%s : %s%s" b s (ctyp zc "" t "") k)
    (fun () -> not_impl "field vertic" ind b s k)
;

value patt_tcon ind b p k =
  match p with
  [ <:patt< ($p$ : $t$) >> ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s : %s%s" b (patt zc "" p "") (ctyp zc "" t "") k)
        (fun () -> not_impl "patt_tcon vertic" ind b p k)
  | p -> patt ind b p k ]
;

value typevar ind b tv k = sprintf "%s'%s%s" b tv k;

(* *)

let lev = find_pr_level "simple" pr_patt.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:patt< ? $s$ >> ->
      fun curr next ind b k -> sprintf "%s?%s%s" b s k
  | <:patt< ? ($p$ $opt:eo$) >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s?(%s%s)%s" b (patt_tcon zc "" p "")
               (match eo with
                [ Some e -> sprintf " = %s" (expr zc "" e "")
                | None -> "" ])
               k)
          (fun () -> not_impl "patt ?(p=e) vertic" ind b p k)
  | <:patt< ? $i$ : ($p$ $opt:eo$) >> ->
      fun curr next ind b k -> failwith "label in pr_ro 3"
  | <:patt< ~ $s$ >> ->
      fun curr next ind b k -> sprintf "%s~%s%s" b s k
  | <:patt< ~ $s$ : $p$ >> ->
      fun curr next ind b k -> curr ind (sprintf "%s~%s:" b s) p k
  | <:patt< `$uid:s$ >> ->
      fun curr next ind b k -> sprintf "%s`%s%s" b s k ]
;

let lev = find_pr_level "apply" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< new $list:cl$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () -> sprintf "%snew %s%s" b (class_longident zc "" cl "") k)
          (fun () -> not_impl "new vertic" ind b cl k) ]
;

let lev = find_pr_level "dot" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< $e$ # $s$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () -> sprintf "%s%s#%s%s" b (curr zc "" e "") s k)
          (fun () -> not_impl "# vertic" ind b e k) ]
;

let lev = find_pr_level "simple" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< ( $e$ : $t$ :> $t2$ ) >> ->
      fun curr next ind b k -> not_impl "expr : :>" ind b e k
  | <:expr< ( $e$ :> $t$ ) >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s :> %s)%s" b (expr zc "" e "") (ctyp zc "" t "") k)
          (fun () ->
             let s1 = expr (shi ind 1) (sprintf "%s(" b) e " :>" in
             let s2 =
               ctyp (shi ind 1) (tab (shi ind 1)) t (sprintf ")%s" k)
             in
             sprintf "%s\n%s" s1 s2)
  | <:expr< ? $s$ >> ->
      fun curr next ind b k -> sprintf "%s?%s%s" b s k
  | <:expr< ~ $s$ >> ->
      fun curr next ind b k -> sprintf "%s~%s%s" b s k
  | <:expr< ~ $s$ : $e$ >> ->
      fun curr next ind b k ->
        pr_expr.pr_fun "dot" ind (sprintf "%s~%s:" b s) e k ]
;

let lev = find_pr_level "simple" pr_ctyp.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:ctyp< ? $i$ : $t$ >> ->
      fun curr next ind b k -> ctyp ind (sprintf "%s?%s:" b i) t k
  | <:ctyp< ~ $i$ : $t$ >> ->
      fun curr next ind b k -> ctyp ind (sprintf "%s~%s:" b i) t k
  | <:ctyp< < $list:ml$ $opt:v$ > >> ->
      fun curr next ind b k ->
        if ml = [] then sprintf "%s<%s >%s" b (if v then " .." else "") k
        else
          let ml = List.map (fun e -> (e, ";")) ml in
          plist field (shi ind 2) 0 (sprintf "%s< " b) ml
            (sprintf "%s >%s" (if v then " .." else "") k)
  | <:ctyp< [ = $list:pvl$ ] >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             hlist2 variant_decl (bar_before variant_decl) zc
               (sprintf "%s[ = " b) pvl (sprintf " ]%s" k))
          (fun () ->
             vlist2 variant_decl (bar_before variant_decl) ind
               (sprintf "%s[ = " b) pvl (sprintf " ]%s" k))
  | <:ctyp< [ > $list:pvl$ ] >> ->
      fun curr next ind b k -> not_impl "variants 2" ind b pvl k
  | <:ctyp< [ < $list:pvl$ ] >> ->
      fun curr next ind b k -> not_impl "variants 3" ind b pvl k
  | <:ctyp< [ < $list:pvl$ > $list:_$ ] >> ->
      fun curr next ind b k -> not_impl "variants 4" ind b pvl k
  | <:ctyp< $_$ as $_$ >> as z ->
      fun curr next ind b k ->
        ctyp (shi ind 1) (sprintf "%s(" b) z (sprintf ")%s" k) ]
;

let lev = find_pr_level "top" pr_sig_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:sig_item< class $list:cd$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass %s%s" b
               (hlist2 class_def (and_before class_def) zc "" cd "")
               k)
          (fun () ->
             vlist2 class_def (and_before class_def) ind
               (sprintf "%sclass " b) cd k)
  | <:sig_item< class type $list:cd$ >> ->
      fun curr next ind b k -> class_type_decl_list ind b cd k ]
;

let lev = find_pr_level "top" pr_str_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:str_item< class $list:cd$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass %s%s" b
               (hlist2 class_decl (and_before class_decl) zc "" cd "")
               k)
          (fun () ->
             vlist2 class_decl (and_before class_decl) ind
               (sprintf "%sclass " b) cd k)
  | <:str_item< class type $list:cd$ >> ->
      fun curr next ind b k -> class_type_decl_list ind b cd k ]
;

value class_type_top =
  extfun Extfun.empty with
  [ <:class_type< object $opt:cst$ $list:csi$ end >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sobject%s %s end%s" b
               (match cst with
                [ Some t -> sprintf " (%s)" (ctyp zc "" t "")
                | None -> "" ])
               (hlist (semi_after class_sig_item) zc "" csi "") k)
          (fun () ->
             let s1 =
               match cst with
               [ None -> sprintf "%sobject" b
               | Some t ->
                   horiz_vertic
                     (fun () -> sprintf "%sobject (%s)" b (ctyp zc "" t ""))
                     (fun () -> not_impl "class_type vertic 1" ind b t "") ]
             in
             let s2 =
               vlist (semi_after class_sig_item) (shi ind 2) (tab (shi ind 2))
                 csi ""
             in
             let s3 = sprintf "%send%s" (tab ind) k in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | z -> fun curr next ind b k -> not_impl "class_type" ind b z k ]
;

value class_expr_top =
  extfun Extfun.empty with
  [ <:class_expr< let $opt:rf$ $list:pel$ in $ce$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             let s1 =
               hlist2 (binding expr) (and_before (binding expr)) ind
                 (sprintf "%slet %s" b (if rf then "rec " else ""))
                 pel " in"
             in
             let s2 = class_expr zc "" ce k in
             sprintf "%s %s" s1 s2)
          (fun () ->
             let s1 =
               vlist2 (binding expr) (and_before (binding expr)) ind
                 (sprintf "%slet %s" b (if rf then "rec " else ""))
                 pel " in"
             in
             let s2 = class_expr ind (tab ind) ce k in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next ind b k -> next ind b z k ]
;

value class_expr_simple =
  extfun Extfun.empty with
  [ <:class_expr< $list:cl$ >> ->
      fun curr next ind b k -> class_longident ind b cl k
  | <:class_expr< object $opt:csp$ $list:csl$ end >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sobject%s %s end%s" b
               (match csp with
                [ Some (<:patt< ($_$ : $_$) >> as p) -> patt ind " " p ""
                | Some p -> patt ind " (" p ")"
                | None -> "" ])
               (hlist (semi_after class_str_item) zc "" csl "") k)
          (fun () ->
             let s1 =
               match csp with
               [ None -> sprintf "%sobject" b
               | Some p ->
                   horiz_vertic
                     (fun () ->
                        sprintf "%sobject %s" b
                          (match p with
                           [ <:patt< ($_$ : $_$) >> -> patt ind "" p ""
                           | p -> patt ind "(" p ")" ]))
                     (fun () -> not_impl "class_type vertic 1" ind b p "") ]
             in
             let s2 =
               vlist (semi_after class_str_item) (shi ind 2) (tab (shi ind 2))
                 csl ""
             in
             let s3 = sprintf "%send%s" (tab ind) k in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | z -> fun curr next ind b k -> not_impl "class_expr" ind b z k ]
;

value class_sig_item_top =
  extfun Extfun.empty with
  [ <:class_sig_item< method $opt:priv$ $s$ : $t$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod%s %s : %s%s" b
               (if priv then " private" else "") s (ctyp zc "" t "") k)
          (fun () -> not_impl "method vertic 1" ind b s k)
  | z -> fun curr next ind b k -> not_impl "class_sig_item" ind b z k ]
;

value class_str_item_top =
  extfun Extfun.empty with
  [ <:class_str_item< inherit $ce$ $opt:pb$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sinherit %s%s%s" b (class_expr zc "" ce "")
               (match pb with
                [ Some s -> sprintf " as %s" s
                | None -> "" ]) k)
          (fun () -> not_impl "inherit vertic" ind b ce k)
  | <:class_str_item< initializer $e$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () -> sprintf "%sinitializer %s%s" b (expr zc "" e "") k)
          (fun () ->
             let s1 = sprintf "%sinitializer" b in
             let s2 = expr (shi ind 2) (tab (shi ind 2)) e k in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< method virtual $opt:priv$ $s$ : $t$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod virtual%s %s : %s%s" b
               (if priv then " private" else "") s (ctyp zc "" t "") k)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%smethod virtual%s %s :" b
                      (if priv then " private" else "") s)
                 (fun () -> not_impl "method vertic 2" ind b s k)
             in
             let s2 = ctyp (shi ind 2) (tab (shi ind 2)) t k in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< method $opt:priv$ $s$ $opt:topt$ = $e$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod%s %s%s = %s%s" b
               (if priv then " private" else "") s
               (match topt with
                [ Some t -> sprintf " : %s" (ctyp zc "" t "")
                | None -> "" ])
               (expr zc "" e "") k)
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
                          (ctyp zc "" t ""))
                     (fun () ->
                        let s1 =
                          sprintf "%smethod%s %s :" b
                            (if priv then " private" else "") s
                        in
                        let s2 = ctyp (shi ind 4) (tab (shi ind 4)) t " =" in
                        sprintf "%s\n%s" s1 s2) ]
             in
             let s2 = expr (shi ind 2) (tab (shi ind 2)) e k in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< value $opt:mf$ $s$ = $e$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%svalue%s %s = %s%s" b
               (if mf then " mutable" else "") s (expr zc "" e "") k)
          (fun () ->
             let s1 =
               sprintf "%svalue%s %s =" b (if mf then " mutable" else "") s
             in
             let s2 = expr (shi ind 2) (tab (shi ind 2)) e k in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next ind b k -> not_impl "class_str_item" ind b z k ]
;

value ctyp_as =
  extfun Extfun.empty with
  [ <:ctyp< $t1$ as $t2$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s as %s%s" b (curr zc "" t1 "") (next zc "" t2 "") k)
          (fun () -> not_impl "ctyp as vertic" ind b t1 k)
  | z -> fun curr next ind b k -> next ind b z k ]
;

value ctyp_poly =
  extfun Extfun.empty with
  [ <:ctyp< ! $list:pl$ . $t$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s! %s . %s%s" b (hlist typevar zc "" pl "")
               (ctyp zc "" t "") k)
          (fun () ->
             let s1 = sprintf "%s! %s ." b (hlist typevar zc "" pl "") in
             let s2 = ctyp (shi ind 2) (tab (shi ind 2)) t k in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next ind b k -> next ind b z k ]
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
