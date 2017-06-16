(* camlp5r *)
(* q_phony.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "pa_extend.cmo";
#load "pa_extprint.cmo";
#load "q_MLast.cmo";
#load "pa_pprintf.cmo";

open Pcaml;

value t = ref "";

Quotation.add ""
  (Quotation.ExAst
     (fun s ->
        let t =
          if t.val = "" then "<<" ^ s ^ ">>"
          else "<:" ^ t.val ^ "<" ^ s ^ ">>"
        in
        let loc = Ploc.dummy in
        <:expr< $uid:t$ >>,
      fun s ->
        let t =
          if t.val = "" then "<<" ^ s ^ ">>"
          else "<:" ^ t.val ^ "<" ^ s ^ ">>"
        in
        let loc = Ploc.dummy in
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
          <:expr< if $e$ then $d$ else () >>
      | "IFDEF"; e = dexpr; "THEN"; d1 = expr_or_macro; "ELSE";
        d2 = expr_or_macro; "END" ->
          <:expr< if $e$ then $d1$ else $d2$ >>
      | "IFNDEF"; e = dexpr; "THEN"; d = expr_or_macro; "END" ->
          <:expr< if $e$ then $d$ else () >>
      | "IFNDEF"; e = dexpr; "THEN"; d1 = expr_or_macro; "ELSE";
        d2 = expr_or_macro; "END" ->
          <:expr< if $e$ then $d1$ else $d2$ >> ] ]
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
open Pcaml;
open Prtools;

value expr = Eprinter.apply pr_expr;

value rec dexpr pc =
  fun
  [ <:expr< $x$ || $y$ >> -> pprintf pc "%p OR %p" dexpr x dexpr1 y
  | z -> dexpr1 pc z ]
and dexpr1 pc =
  fun
  [ z -> dexpr2 pc z ]
and dexpr2 pc =
  fun
  [ z -> dexpr3 pc z ]
and dexpr3 pc =
  fun
  [ <:expr< $uid:i$ >> -> pprintf pc "%s" i
  | _ -> pprintf pc "dexpr not impl" ]
;

value expr_or_macro pc =
  fun
  [ <:expr< DEFINE $uid:i$ >> -> pprintf pc "DEFINE %s" i
  | e -> expr pc e ]
;

value macro_def pc =
  fun
  [ <:expr< IFDEF $e$ $d$ >> ->
      pprintf pc "@[<a>IFDEF %p THEN@;%p@ END@]" dexpr e expr_or_macro d
  | <:expr< IFDEF $e$ $d1$ $d2$ >> ->
      pprintf pc "@[<a>IFDEF %p THEN@;%p@ ELSE@;%p@ END@]" dexpr e
        expr_or_macro d1 expr_or_macro d2
  | _ -> assert False ]
;

try
  EXTEND_PRINTER
    pr_expr: LEVEL "apply"
      [ [ <:expr< IFDEF $_$ $_$ >> as z -> macro_def pc z
        | <:expr< IFDEF $_$ $_$ $_$ >> as z -> macro_def pc z ] ]
    ;
  END
with
[ Failure _ -> () ];
