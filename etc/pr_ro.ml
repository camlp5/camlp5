(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_ro.ml,v 1.3 2007/05/30 20:30:13 deraugla Exp $ *)
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
value class_type ind b z k = pr_class_type.pr_fun "top" ind b z k;
value class_sig_item ind b z k = pr_class_sig_item.pr_fun "top" ind b z k;

value tab ind = String.make ind ' ';

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

value semi_after elem ind b x k = elem ind b x (sprintf ";%s" k);
value and_before elem ind b x k = elem ind (sprintf "%sand " b) x k;

value class_type_params ind b ctp k =
  if ctp = [] then sprintf "%s%s" b k
  else not_impl "class_type_params" ind b ctp k
;

value class_type_decl ind b ci k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s= %s%s" b (if ci.MLast.ciVir then " virtual" else "")
         ci.MLast.ciNam (class_type_params  0 "" (snd ci.MLast.ciPrm) "")
         (class_type 0 "" ci.MLast.ciExp "") k)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s=" b (if ci.MLast.ciVir then " virtual" else "")
           ci.MLast.ciNam (class_type_params  0 "" (snd ci.MLast.ciPrm) "")
       in
       let s2 = class_type (ind + 2) (tab (ind + 2)) ci.MLast.ciExp k in
       sprintf "%s\n%s" s1 s2)
;

let lev = find_pr_level "simple" pr_patt.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:patt< ? $s$ >> ->
      fun curr next ind b k -> sprintf "%s?%s%s" b s k
  | <:patt< ? ($p$ = $e$) >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s?(%s = %s)%s" b (patt 0 "" p "") (expr 0 "" e "") k)
          (fun () -> not_impl "patt ?(p=e) vertic" ind b p k)
  | <:patt< ? $i$ : ($p$ = $eo$) >> ->
      fun curr next ind b k -> failwith "label in pr_ro 3"
  | <:patt< ~ $s$ >> ->
      fun curr next ind b k -> sprintf "%s?%s%s" b s k ]
;

let lev = find_pr_level "simple" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< ? $s$ >> ->
      fun curr next ind b k -> sprintf "%s?%s%s" b s k
  | <:expr< ~ $s$ >> ->
      fun curr next ind b k -> sprintf "%s~%s%s" b s k
  | <:expr< ~ $s$ : $e$ >> ->
      fun curr next ind b k -> curr ind (sprintf "%s~%s:" b s) e k ]
;

let lev = find_pr_level "simple" pr_ctyp.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:ctyp< ? $i$ : $t$ >> ->
      fun curr next ind b k -> ctyp ind (sprintf "%s?%s:" b i) t k ]
;

let lev = find_pr_level "top" pr_sig_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:sig_item< class type $list:cd$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass type %s%s" b
               (hlist2 class_type_decl (and_before class_type_decl) 0 "" cd
                  "")
               k)
          (fun () ->
             vlist2 class_type_decl (and_before class_type_decl) ind
               (sprintf "%sclass type " b) cd k) ]
;

value class_type_top =
  extfun Extfun.empty with
  [ <:class_type< object $opt:cst$ $list:csi$ end >> as z ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sobject%s %s end%s" b
               (match cst with
                [ Some t -> sprintf " (%s)" (ctyp 0 "" t "")
                | None -> "" ])
               (hlist (semi_after class_sig_item) 0 "" csi "") k)
          (fun () -> not_impl "class_type object vertic" ind b z k)
  | z -> fun curr next ind b k -> not_impl "class_type" ind b z k ]
;

value class_sig_item_top =
  extfun Extfun.empty with
  [ <:class_sig_item< method $opt:priv$ $s$ : $t$ >> ->
      fun curr next ind b k -> not_impl "method" ind b s k
  | z -> fun curr next ind b k -> not_impl "class_sig_item" ind b z k ]
;

pr_class_type.pr_levels :=
  [{pr_label = "top"; pr_rules = class_type_top}]
;

pr_class_sig_item.pr_levels :=
  [{pr_label = "top"; pr_rules = class_sig_item_top}]
;
