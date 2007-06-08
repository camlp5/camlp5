(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

(* heuristic to rebuild the EXTEND statement from the AST *)

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
  sprintf "%s\"pr_extend, not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value tab ind = String.make ind ' ';

value expr ind b z k = pr_expr.pr_fun "top" ind b z k;

(* *)

(* horizontal list *)
value rec hlist elem ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] -> sprintf "%s %s" (elem ind b x "") (hlist elem ind "" xl k) ]
;

(* vertical list *)
value rec vlist elem ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ind b x "") (vlist elem ind (tab ind) xl k) ]
;

(* Extracting *)

type symbol =
  [ Snterm of MLast.expr
  | Snterml of MLast.expr and string
  | Slist0 of symbol
  | Slist0sep of symbol and symbol
  | Slist1 of symbol
  | Slist1sep of symbol and symbol
  | Sopt of symbol
  | Sself
  | Snext
  | Stoken of Token.pattern
  | Srules of list (list (option MLast.patt * symbol) * option MLast.expr) ]
;

value rec get_globals =
  fun
  [ [(<:patt< _ >>, <:expr< ($e$ : $uid:gmod1$.Entry.e '$_$) >>) :: pel] ->
      let (gmod, gl) = get_globals pel in
      if gmod = "" || gmod = gmod1 then (gmod1, [e :: gl])
      else raise Not_found
  | [] -> ("", [])
  | _ -> raise Not_found ]
;

value rec get_locals =
  fun
  [ [(<:patt< $_$ >>,
      <:expr< (grammar_entry_create $_$ : $_$) >>) :: pel] ->
        get_locals pel
  | [] -> ()
  | _ -> raise Not_found ]
;

value unposition =
  fun
  [ <:expr< None >> -> None
  | <:expr< Some Gramext.First >> -> Some Gramext.First
  | <:expr< Some Gramext.Last >> -> Some Gramext.Last
  | <:expr< Some (Gramext.Before $str:s$) >> -> Some (Gramext.Before s)
  | <:expr< Some (Gramext.After $str:s$) >> -> Some (Gramext.After s)
  | <:expr< Some (Gramext.Level $str:s$) >> -> Some (Gramext.Level s)
  | _ -> raise Not_found ]
;

value unlabel =
  fun
  [ <:expr< None >> -> None
  | <:expr< Some $str:s$ >> -> Some s
  | _ -> raise Not_found ]
;

value unassoc =
  fun
  [ <:expr< None >> -> None
  | <:expr< Some Gramext.NonA >> -> Some Gramext.NonA
  | <:expr< Some Gramext.LeftA >> -> Some Gramext.LeftA
  | <:expr< Some Gramext.RightA >> -> Some Gramext.RightA
  | _ -> raise Not_found ]
;

value rec unaction =
  fun
  [ <:expr< fun ($lid:locp$ : Token.location) -> ($a$ : $_$) >>
    when locp = Stdpp.loc_name.val ->
      let ao =
        match a with
        [ <:expr< () >> -> None
        | _ -> Some a ]
      in
      ([], ao)
  | <:expr< fun ($p$ : $_$) -> $e$ >> ->
      let (pl, a) = unaction e in ([p :: pl], a)
  | <:expr< fun _ -> $e$ >> ->
      let (pl, a) = unaction e in
      (let loc = Stdpp.dummy_loc in [<:patt< _ >> :: pl], a)
  | _ -> raise Not_found ]
;

value untoken =
  fun
  [ <:expr< ($str:x$, $str:y$) >> -> (x, y)
  | _ -> raise Not_found ]
;

value rec unrule_list rl =
  fun
  [ <:expr< [$e$ :: $el$] >> -> unrule_list [unrule e :: rl] el
  | <:expr< [] >> -> rl
  | _ -> raise Not_found ]
and unrule =
  fun
  [ <:expr< ($e1$, Gramext.action $e2$) >> ->
      let (pl, a) =
        match unaction e2 with
        [ ([], None) -> let loc = Stdpp.dummy_loc in ([], Some <:expr< () >>)
        | x -> x ]
      in
      let sl = unpsymbol_list (List.rev pl) e1 in
      (sl, a)
  | _ -> raise Not_found ]
and unpsymbol_list pl e =
  match (pl, e) with
  [ ([], <:expr< [] >>) -> []
  | ([p :: pl], <:expr< [$e$ :: $el$] >>) ->
      let op =
        match p with
        [ <:patt< _ >> -> None
        | _ -> Some p ]
      in
      [(op, unsymbol e) :: unpsymbol_list pl el]
  | _ -> raise Not_found ]
and unsymbol =
  fun
  [ <:expr< Gramext.Snterm ($uid:_$.Entry.obj ($e$ : $_$)) >> -> Snterm e
  | <:expr< Gramext.Snterml ($uid:_$.Entry.obj ($e$ : $_$)) $str:s$ >> ->
      Snterml e s
  | <:expr< Gramext.Snterml ($uid:_$.Entry.obj ($e$ : $_$), $str:s$) >> ->
      Snterml e s
  | <:expr< Gramext.Slist0 $e$ >> -> Slist0 (unsymbol e)
  | <:expr< Gramext.Slist0sep $e1$ $e2$ >> ->
      Slist0sep (unsymbol e1) (unsymbol e2)
  | <:expr< Gramext.Slist0sep ($e1$, $e2$) >> ->
      Slist0sep (unsymbol e1) (unsymbol e2)
  | <:expr< Gramext.Slist1 $e$ >> -> Slist1 (unsymbol e)
  | <:expr< Gramext.Slist1sep $e1$ $e2$ >> ->
      Slist1sep (unsymbol e1) (unsymbol e2)
  | <:expr< Gramext.Slist1sep ($e1$, $e2$) >> ->
      Slist1sep (unsymbol e1) (unsymbol e2)
  | <:expr< Gramext.Sopt $e$ >> -> Sopt (unsymbol e)
  | <:expr< Gramext.Sself >> -> Sself
  | <:expr< Gramext.Snext >> -> Snext
  | <:expr< Gramext.Stoken $e$ >> -> Stoken (untoken e)
  | <:expr< Gramext.srules $e$ >> -> Srules (unrule_list [] e)
  | _ -> raise Not_found ]
;

value unlevel =
  fun
  [ <:expr< ($e1$, $e2$, $e3$) >> ->
      (unlabel e1, unassoc e2, unrule_list [] e3)
  | _ -> raise Not_found ]
;

value rec unlevel_list =
  fun
  [ <:expr< [$e$ :: $el$] >> -> [unlevel e :: unlevel_list el]
  | <:expr< [] >> -> []
  | _ -> raise Not_found ]
;

value unentry =
  fun
  [ <:expr< (Grammar.Entry.obj ($e$ : Grammar.Entry.e '$_$), $pos$, $ll$) >> ->
      (e, unposition pos, unlevel_list ll)
  | _ -> raise Not_found ]
;

value rec unentry_list =
  fun
  [ <:expr< [$e$ :: $el$] >> -> [unentry e :: unentry_list el]
  | <:expr< [] >> -> []
  | _ -> raise Not_found ]
;

value unextend_body e =
  let ((_, globals), e) =
    match e with
    [ <:expr< let $list:pel$ in $e1$ >> ->
        try (get_globals pel, e1) with
        [ Not_found -> (("", []), e) ]
    | _ -> (("", []), e) ]
  in
  let e =
    match e with
    [ <:expr<
        let grammar_entry_create s =
          Grammar.Entry.create (Grammar.of_entry $_$) s
        in
        $e$ >> ->
       let e =
         match e with
         [ <:expr< let $list:pel$ in $e1$ >> ->
             try let _ = get_locals pel in e1 with
             [ Not_found -> e ]
         | _ -> e ]
       in
       e
    | _ -> e ]
  in
  let el = unentry_list e in
  (globals, el)
;

(* Printing *)

value string s = sprintf "\"%s\"" s;

value position ind b pos k =
  match pos with
  [ None -> sprintf "%s%s" b k
  | Some Gramext.First -> sprintf "%sFIRST%s" b k
  | Some Gramext.Last -> sprintf "%sLAST%s" b k
  | Some (Gramext.Before s) -> sprintf "%sBEFORE%s" b k
  | Some (Gramext.After s) -> sprintf "%sAFTER %s%s" b (string s) k
  | Some (Gramext.Level s) -> sprintf "%sLEVEL %s%s" b (string s) k ]
;

value rule ind b (sl, a) k = not_impl "rule" ind b sl k;

value label =
  fun
  [ Some s -> sprintf " \"%s\"" s
  | None -> "" ]
;

value assoc =
  fun
  [ Some Gramext.NonA -> " NONA"
  | Some Gramext.LeftA -> " LEFTA"
  | Some Gramext.RightA -> " RIGHTA"
  | None -> "" ]
;

value level ind b (lab, ass, rl) k =
  match (lab, ass) with
  [ (None, None) ->
      if rl = [] then sprintf "%s[ ]%s" b k
      else vlist rule ind (sprintf "%s[ " b) rl (sprintf " ]%s" k)
  | _ ->
      let s1 = sprintf "%s%s%s" b (label lab) (assoc ass) in
      let s2 =
        if rl = [] then sprintf "%s[ ]%s" (tab ind) k
        else vlist rule ind (sprintf "%s[ " (tab ind)) rl (sprintf " ]%s" k)
      in
      sprintf "%s\n%s" s1 s2 ]
;

value entry ind b (e, pos, ll) k =
  sprintf "%s%s:%s\n%s\n;" b (expr ind "" e "") (position ind "" pos "")
    (vlist level (ind + 2) (tab (ind + 2)) ll "")
;

value extend_body ind b (globals, entries) k =
  match globals with
  [ [] -> vlist entry ind b entries k
  | _ ->
      let s1 = sprintf "%sGLOBAL: %s;" b (hlist expr ind "" globals "") in
      let s2 = vlist entry ind (tab ind) entries k in
      sprintf "%s\n%s" s1 s2 ]
;

value extend ind b e k =
  match e with
  [ <:expr< Grammar.extend $e$ >> ->
      try
        let ex = unextend_body e in
        let s = extend_body (ind + 2) (tab (ind + 2)) ex "" in
        sprintf "EXTEND\n%s\nEND%s" s k
      with
      [ Not_found ->
          sprintf "%sGrammar.extend\n%s" b
            (expr (ind + 2) (sprintf "%s(" (tab (ind + 2))) e k) ]
  | e -> expr ind b e k ]
;

let lev = find_pr_level "apply" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< Grammar.extend $_$ >> as e ->
      fun curr next ind b k -> next ind b e k ];

let lev = find_pr_level "simple" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< Grammar.extend $_$ >> as e ->
      fun curr next ind b k -> extend ind b e k ];
