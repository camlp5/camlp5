(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

(* Heuristic to rebuild parsers and streams from the AST *)

open Pcaml.NewPrinter;
open Sformat;

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and option MLast.expr
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpLhd of MLast.loc and list (list MLast.patt)
  | SpStr of MLast.loc and MLast.patt ]
;

value strm_n = "strm__";
value peek_fun loc = <:expr< Stream.peek >>;
value junk_fun loc = <:expr< Stream.junk >>;

value not_impl name ind b x k =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_rp, not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value tab ind = String.make ind ' ';

(* vertical list with different function from 2nd element on *)
value rec vlist2 elem elem2 ind b xl k0 k =
  match xl with
  [ [] -> invalid_arg "vlist2"
  | [x] -> elem ind b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ind b x k0)
        (vlist2 elem2 elem2 ind (tab ind) xl k0 k) ]
;

value bar_before elem ind b x k = elem ind (sprintf "%s| " b) x k;

(* Rebuilding syntax tree *)

value unparser_body e =
  let (po, e) =
    match e with
    [ <:expr< let $lid:bp$ = Stream.count $lid:strm_n$ in $e$ >> ->
        (Some bp, e)
    | _ -> (None, e) ]
  in
  (po, [([], None, e)])
;

(* Printing *)

value expr ind b z k = pr_expr.pr_fun "top" ind b z k;

value parser_case ind b (sp, po, e) k =
  not_impl "parser_case" ind b sp k
;

value parser_body ind b (po, spel) k =
  let s1 =
    match po with
    [ Some s -> sprintf " %s" s
    | None -> "" ]
  in
  let s2 =
    vlist2 parser_case (bar_before parser_case) ind (sprintf "%s[ " (tab ind))
      spel "" (sprintf " ]%s" k)
  in
  sprintf "%sparser%s\n%s" b s1 s2
;

(* Main *)

value print_parser ind b e k =
  match e with
  [ <:expr< fun (strm__ : Stream.t _) -> $e$ >> ->
      let pa = unparser_body e in
      parser_body ind b pa k
  | e -> expr ind b e k ]
;

pr_expr_fun_args.val :=
  extfun pr_expr_fun_args.val with
  [ <:expr< fun (strm__ : $_$) -> $_$ >> as e -> ([], e) ];

let lev = find_pr_level "top" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< fun (strm__ : Stream.t _) -> $_$ >> as e ->
      fun curr next ind b k -> print_parser ind b e k ]
;

