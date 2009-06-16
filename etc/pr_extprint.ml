(* camlp5r q_MLast.cmo -I . pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo *)
(* $Id: pr_extprint.ml,v 1.2 2008/01/05 10:11:47 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2008 *)

(* heuristic to rebuild the EXTEND_PRINTER statement from the AST *)

open Pcaml;
open Prtools;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      "\"" ^ Obj.magic x ^ "\""
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  pprintf pc "\"pr_extprint, not impl: %s; %s\"" name (String.escaped desc)
;

(**)
value test = ref False;
Pcaml.add_option "-test" (Arg.Set test) " test";
(**)

(* Extracting *)

value loc = Ploc.dummy;

value unrules =
  loop where rec loop =
    fun
    [ <:expr< [$rule$ :: $rules$] >> ->
        let (p, wo, e) =
          match rule with
          [ <:expr< ($_$, False, $e$) >> ->
              match e with
              [ <:expr< fun [ $p$ $opt:wo$ -> Some $e$ | _ -> None ] >> ->
                  (p, wo, e)
              | <:expr< fun $p$ -> Some $e$ >> ->
                  (p, None, e)
              | _ ->
                  raise Not_found ]
          | _ ->
              raise Not_found ]
        in
        let e =
          match e with
          [ <:expr< fun curr next pc -> $e$ >> -> e
          | _ -> raise Not_found ]
        in
        [(p, wo, e) ::  loop rules]
    | <:expr< [] >> -> []
    | _ -> raise Not_found ]
;

value unextend_body pr pos body =
  let pos =
    match pos with
    [ <:expr< Some $p$ >> ->
        let p =
          match p with
          [ <:expr< Eprinter.First >> -> Eprinter.First
          | <:expr< Eprinter.Last >> -> Eprinter.Last
          | <:expr< Eprinter.Before $str:n$ >> -> Eprinter.Before n
          | <:expr< Eprinter.After $str:n$ >> -> Eprinter.After n
          | <:expr< Eprinter.Level $str:n$ >> -> Eprinter.Level n
          | _ -> raise Not_found ]
        in
        Some p
    | <:expr< None >> -> None
    | _ -> raise Not_found ]
  in
  let ll =
    loop body where rec loop =
      fun
      [ <:expr< [($lab$, $rules$) :: $levs$] >> ->
          let label =
            match lab with
            [ <:expr< Some $str:s$ >> -> Some s
            | <:expr< None >> -> None
            | _ -> raise Not_found ]
          in
          let rules =
            match rules with
            [ <:expr< fun e__ -> Extfun.extend e__ $rules$ >> -> unrules rules
            | _ -> raise Not_found ]
          in
          [(label, rules) :: loop levs]
      | <:expr< [] >> -> []
      | _ -> raise Not_found ]
  in
  (pr, pos, ll)
;

(* Printing *)

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value bar_before elem pc x = pprintf pc "| %p" elem x;

value opt_position pc =
  fun
  [ Some p ->
      match p with
      [ Eprinter.First -> pprintf pc " FIRST"
      | Eprinter.Last -> pprintf pc " LAST"
      | Eprinter.Before n -> pprintf pc " BEFORE \"%s\"" n
      | Eprinter.After n -> pprintf pc " AFTER \"%s\"" n
      | Eprinter.Level n -> pprintf pc " LEVEL \"%s\"" n ]
  | None -> pprintf pc "" ]
;

value patt_as pc z =
  match z with
  [ <:patt< ($x$ as $y$) >> -> pprintf pc "%p as @[%p@]" patt x patt y
  | z -> patt pc z ]
;

value rule pc (p, wo, e) = pprintf pc "@[<2>%p ->@;%p@]" patt_as p expr e;

value rule_list pc =
  fun
  [ [] -> pprintf pc "[ ]"
  | rules -> pprintf pc "[ %p ]" (vlist2 rule (bar_before rule)) rules ]
;

value level pc (lab, rules) =
  match lab with
  [ Some lab -> pprintf pc "@[<b>\"%s\"@;%p@]" lab rule_list rules
  | None -> pprintf pc "@[<2>%p@]" rule_list rules ]
;

value level_list pc =
  fun
  [ [] -> pprintf pc "[ ]"
  | ll -> pprintf pc "[ %p ]" (vlist2 level (bar_before level)) ll ]
;

value extend_body pc (pr, pos, ll) =
  pprintf pc "@[<b>%p:%p@;%p@]" expr pr opt_position pos level_list ll
;

value extend pc =
  fun
  [ <:expr< Eprinter.extend $pr$ $pos$ $body$ >> ->
      if test.val then
      pprintf pc "test"
      else
      try
        let ex = unextend_body pr pos body in
        pprintf pc "EXTEND_PRINTER@;%p@ END" extend_body ex
      with
      [ Not_found ->
          let expr = Eprinter.apply_level pr_expr "dot" in
          pprintf pc "Eprinter.extend@;%p@ %p@ %p@" expr pr expr pos
            expr body ]
  | e -> expr pc e ]
;

EXTEND_PRINTER
  pr_expr: LEVEL "apply"
    [ [ <:expr< Eprinter.extend $_$ $_$ $_$ >> as e -> next pc e ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< Eprinter.extend $_$ $_$ $_$ >> as e -> extend pc e ] ]
  ;
END;
