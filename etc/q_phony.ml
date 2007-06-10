(* camlp4r pa_extend.cmo q_MLast.cmo *)
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

(* $Id: q_phony.ml,v 1.6 2007/06/10 03:38:51 deraugla Exp $ *)

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

if Pcaml.syntax_name.val <> "Scheme" then
  EXTEND
    GLOBAL: expr;
    expr: LEVEL "top"
      [ [ "IFDEF"; c = dexpr; "THEN"; e1 = expr; "ELSE"; e2 = expr; "END" ->
            <:expr< if DEF $c$ then $e1$ else $e2$ >>
        | "IFNDEF"; c = dexpr; "THEN"; e1 = expr; "ELSE"; e2 = expr; "END" ->
            <:expr< if NDEF $c$ then $e1$ else $e2$ >> ] ]
    ;
    dexpr:
      [ [ x = SELF; "OR"; y = SELF -> <:expr< $x$ || $y$ >> ]
      | [ x = SELF; "AND"; y = SELF -> <:expr< $x$ && $y$ >> ]
      | [ "NOT"; x = SELF ->  <:expr< not $x$ >> ]
      | [ i = UIDENT -> <:expr< $uid:i$ >>
      | "("; x = SELF; ")" -> x ] ]
    ;
  END
else ();
