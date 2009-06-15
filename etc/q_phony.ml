(* camlp4r -I . *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: q_phony.ml,v 1.9 2007/07/10 09:05:15 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;

value t = ref "";

Quotation.add ""
  (Quotation.ExAst
     (fun s ->
        let t =
          if t.val = "" then "<<" ^ s ^ ">>"
          else "<:" ^ t.val ^ "<" ^ s ^ ">>"
        in
        let loc = Stdpp.dummy_loc in
        <:expr< $uid:t$ >>,
      fun s ->
        let t =
          if t.val = "" then "<<" ^ s ^ ">>"
          else "<:" ^ t.val ^ "<" ^ s ^ ">>"
        in
        let loc = Stdpp.dummy_loc in
        <:patt< $uid:t$ >>))
;

Quotation.default.val := "";
Quotation.translate.val := fun s -> do { t.val := s; "" };

EXTEND
  GLOBAL: str_item expr;
  str_item: FIRST
    [ [ x = macro_def -> <:str_item< $exp:x$ >> ] ]
  ;
  expr: FIRST
    [ [ x = macro_def -> x ] ]
  ;
  macro_def:
    [ [ "DEFINE"; i = UIDENT -> <:expr< DEFINE $uid:i$ >>
      | "IFDEF"; e = dexpr; "THEN"; d = expr_or_macro; "END" ->
          <:expr< IFDEF $e$ $d$ >>
      | "IFDEF"; e = dexpr; "THEN"; d1 = expr_or_macro; "ELSE";
        d2 = expr_or_macro; "END" ->
          <:expr< IFDEF $e$ $d1$ $d2$ >> ] ]
  ;
  expr_or_macro:
    [ [ d = macro_def -> d
      | e = expr -> e ] ]
  ;
  dexpr:
    [ [ x = SELF; "OR"; y = SELF -> <:expr< $x$ || $y$ >> ]
    | [ x = SELF; "AND"; y = SELF -> <:expr< $x$ && $y$ >> ]
    | [ "NOT"; x = SELF -> <:expr< NOT $x$ >> ]
    | [ i = UIDENT -> <:expr< $uid:i$ >>
      | "("; x = SELF; ")" -> x ] ]
  ;
END;

#load "pa_extfun.cmo";

open Pretty;
open Pcaml.Printers;
open Prtools;

value expr pc e = pr_expr.pr_fun "top" pc e;

value rec dexpr pc =
  fun
  [ <:expr< $x$ || $y$ >> ->
      sprintf "%s%s OR %s%s" pc.bef
        (dexpr {(pc) with bef = ""; aft = ""} x)
        (dexpr1 {(pc) with bef = ""; aft = ""} y) pc.aft
  | z -> dexpr1 pc z ]
and dexpr1 pc =
  fun
  [ z -> dexpr2 pc z ]
and dexpr2 pc =
  fun
  [ z -> dexpr3 pc z ]
and dexpr3 pc =
  fun
  [ <:expr< $uid:i$ >> -> sprintf "%s%s%s" pc.bef i pc.aft
  | _ -> sprintf "%sdexpr not impl%s" pc.bef pc.aft ]
;

value expr_or_macro pc =
  fun
  [ <:expr< DEFINE $uid:i$ >> -> sprintf "%sDEFINE %s%s" pc.bef i pc.aft
  | e -> expr pc e ]
;

value macro_def pc =
  fun
  [ <:expr< IFDEF $e$ $d$ >> ->
      horiz_vertic
        (fun () ->
           sprintf "%sIFDEF %s THEN %s END%s" pc.bef
             (dexpr {(pc) with bef = ""; aft = ""} e)
             (expr_or_macro {(pc) with bef = ""; aft = ""} d) pc.aft)
        (fun () ->
           let s1 =
             sprintf "%sIFDEF %s THEN" pc.bef
               (dexpr {(pc) with bef = ""; aft = ""} e)
           in
           let s2 =
             expr_or_macro {(pc) with bef = tab (pc.ind + 2); aft = ""} d
           in
           let s3 = sprintf "%sEND%s" (tab pc.ind) pc.aft in
           sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:expr< IFDEF $e$ $d1$ $d2$ >> ->
      horiz_vertic
        (fun () ->
           sprintf "%sIFDEF %s THEN %s ELSE %s END%s" pc.bef
             (dexpr {(pc) with bef = ""; aft = ""} e)
             (expr_or_macro {(pc) with bef = ""; aft = ""} d1)
             (expr_or_macro {(pc) with bef = ""; aft = ""} d2) pc.aft)
        (fun () ->
           let s1 =
             sprintf "%sIFDEF %s THEN" pc.bef
               (dexpr {(pc) with bef = ""; aft = ""} e)
           in
           let s2 =
             expr_or_macro {(pc) with bef = tab (pc.ind + 2); aft = ""} d1
           in
           let s3 = sprintf "%sELSE" (tab pc.ind) in
           let s4 =
             expr_or_macro {(pc) with bef = tab (pc.ind + 2); aft = ""} d2
           in
           let s5 = sprintf "%sEND%s" (tab pc.ind) pc.aft in
           sprintf "%s\n%s\n%s\n%s\n%s" s1 s2 s3 s4 s5)
  | _ -> assert False ]
;
               

let lev = find_pr_level "apply" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< IFDEF $_$ $_$ >> as z ->
      fun curr next pc -> macro_def pc z
  | <:expr< IFDEF $_$ $_$ $_$ >> as z ->
      fun curr next pc -> macro_def pc z ];
