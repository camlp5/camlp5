(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_ro.ml,v 1.1 2007/05/30 11:52:10 deraugla Exp $ *)
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
