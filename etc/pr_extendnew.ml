(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

(* heuristic to rebuild the EXTEND statement from the AST *)

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
  sprintf "%s\"pr_extend, not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value bar_before elem ctx b x k = elem ctx (sprintf "%s| " b) x k;
value semi_after elem ctx b x k = elem ctx b x (sprintf ";%s" k);

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
  | Stoken of alt Token.pattern MLast.expr
  | Srules of list (list (option MLast.patt * symbol) * option MLast.expr) ]
and alt 'a 'b =
  [ Left of 'a
  | Right of 'b ]
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
  [ [(<:patt< $_$ >>, <:expr< (grammar_entry_create $_$ : $_$) >>) :: pel] ->
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
      let (pl, a) = unaction e in
      ([p :: pl], a)
  | <:expr< fun _ -> $e$ >> ->
      let (pl, a) = unaction e in
      (let loc = Stdpp.dummy_loc in [<:patt< _ >> :: pl], a)
  | _ -> raise Not_found ]
;

value untoken =
  fun
  [ <:expr< ($str:x$, $str:y$) >> -> Left (x, y)
  | <:expr< ($str:_$, $lid:_$) >> as e -> Right e
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
  [ <:expr<
      (Grammar.Entry.obj ($e$ : Grammar.Entry.e '$_$), $pos$, $ll$)
    >> ->
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
        try (get_globals pel, e1) with [ Not_found -> (("", []), e) ]
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

value expr ctx b z k = pr_expr.pr_fun "top" ctx b z k;
value patt ctx b z k = pr_patt.pr_fun "top" ctx b z k;

value string ctx b s k = sprintf "%s\"%s\"%s" b s k;

value position ctx b pos k =
  match pos with
  [ None -> sprintf "%s%s" b k
  | Some Gramext.First -> sprintf "%s FIRST%s" b k
  | Some Gramext.Last -> sprintf "%s LAST%s" b k
  | Some (Gramext.Before s) -> sprintf "%s BEFORE%s" b k
  | Some (Gramext.After s) ->
      sprintf "%s AFTER %s%s" b (string ctx "" s "") k
  | Some (Gramext.Level s) ->
      sprintf "%s LEVEL %s%s" b (string ctx "" s "") k ]
;

value action expr ctx b a k = expr ctx b a k;

value token ctx b tok k =
  match tok with
  [ Left (con, prm) ->
      if con = "" then string ctx b prm k
      else if prm = "" then sprintf "%s%s%s" b con k
      else sprintf "%s%s %s%s" b con (string ctx "" prm "") k
  | Right <:expr< ($str:con$, $x$) >> ->
      sprintf "%s%s $%s$%s" b con (expr ctx "" x "") k
  | Right _ -> assert False ]
;

value ind i = {ind = i};

value rec rule ctx b (sl, a) k =
  match a with
  [ None -> not_impl "rule 1" ctx b sl k
  | Some a ->
      if sl = [] then
        action expr (shi ctx 4)
          (sprintf "%s->%s " b (comm_bef (ind 1) (MLast.loc_of_expr a))) a k
      else
        match
          horiz_vertic
            (fun () ->
               let s = hlistl (semi_after psymbol) psymbol ctx "" sl "" in
               Some (sprintf "%s%s ->" b s))
            (fun () -> None)
        with
        [ Some s1 ->
            horiz_vertic
              (fun () -> sprintf "%s %s%s" s1 (action expr ctx "" a "") k)
              (fun () ->
                 let s2 = action expr (shi ctx 4) (tab (shi ctx 4)) a k in
                 sprintf "%s\n%s" s1 s2)
        | None ->
            let sl = List.map (fun s -> (s, ";")) sl in
            let s1 = plist psymbol 0 (shi ctx 2) b sl " ->" in
            let s2 = action expr (shi ctx 4) (tab (shi ctx 4)) a k in
            sprintf "%s\n%s" s1 s2 ] ]
and psymbol ctx b (p, s) k =
  match p with
  [ None -> symbol ctx b s k
  | Some p ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s = %s%s" b (patt ctx "" p "") (symbol ctx "" s "") k)
        (fun () ->
           let s1 = patt ctx b p " =" in
           let s2 = symbol (shi ctx 2) (tab (shi ctx 2)) s k in
           sprintf "%s\n%s" s1 s2) ]
and symbol ctx b sy k =
  match sy with
  [ Snterm e -> expr ctx b e k
  | Snterml e s -> expr ctx b e (sprintf " LEVEL \"%s\"%s" s k)
  | Slist0 sy -> sprintf "%sLIST0 %s" b (simple_symbol ctx "" sy k)
  | Slist0sep sy sep ->
      sprintf "%sLIST0 %s SEP %s" b (simple_symbol ctx "" sy "")
        (simple_symbol ctx "" sep k)
  | Slist1 sy -> sprintf "%sLIST1 %s" b (simple_symbol ctx "" sy k)
  | Slist1sep sy sep ->
      sprintf "%sLIST1 %s SEP %s" b (simple_symbol ctx "" sy "")
        (simple_symbol ctx "" sep k)
  | Sopt sy -> sprintf "%sOPT %s" b (simple_symbol ctx "" sy k)
  | Stoken tok -> token ctx b tok k
  | sy -> simple_symbol ctx b sy k ]
and simple_symbol ctx b sy k =
  match sy with  
  [ Snterm <:expr< $lid:s$ >> -> sprintf "%s%s%s" b s k
  | Sself -> sprintf "%sSELF%s" b k
  | Snext -> sprintf "%sNEXT%s" b k
  | Srules rl ->
      horiz_vertic
        (fun () ->
           hlist2 rule (bar_before rule) ctx (sprintf "%s[ " b) rl
             ("", sprintf " ]%s" k))
        (fun () ->
           vlist2 rule (bar_before rule) ctx (sprintf "%s[ " b) rl
             ("", sprintf " ]%s" k))
  | Stoken (Left ("", _) | Left (_, "")) -> symbol ctx b sy k
  | Snterml _ _ | Slist0 _ | Slist0sep _ _ | Slist1 _ | Slist1sep _ _ ->
      symbol ctx (sprintf "%s(" b) sy (sprintf ")%s" k)
  | sy -> not_impl "simple_symbol" ctx b sy k ]
;

value label =
  fun
  [ Some s -> sprintf "\"%s\"" s
  | None -> "" ]
;

value assoc =
  fun
  [ Some Gramext.NonA -> "NONA"
  | Some Gramext.LeftA -> "LEFTA"
  | Some Gramext.RightA -> "RIGHTA"
  | None -> "" ]
;

value level ctx b (lab, ass, rl) k =
  match (lab, ass) with
  [ (None, None) ->
      if rl = [] then sprintf "%s[ ]%s" b k
      else
        vlist2 rule (bar_before rule) (shi ctx 2) (sprintf "%s[ " b) rl
          ("", sprintf " ]%s" k)
  | _ ->
      let s1 =
        match (lab, ass) with
        [ (Some _, None) -> sprintf "%s%s" b (label lab)
        | (None, Some _) -> sprintf "%s%s" b (assoc ass)
        | (Some _, Some _) -> sprintf "%s%s %s" b (label lab) (assoc ass)
        | _ -> assert False ]
      in
      let s2 =
        if rl = [] then not_impl "level" ctx "" rl k
        else
          vlist2 rule (bar_before rule) (shi ctx 2)
            (sprintf "%s[ " (tab (shi ctx 2))) rl ("", sprintf " ]%s" k)
      in
      sprintf "%s\n%s" s1 s2 ]
;

value entry ctx b (e, pos, ll) k =
  sprintf "%s%s%s:%s\n%s\n%s;%s" (comm_bef ctx (MLast.loc_of_expr e)) b
    (expr ctx "" e "") (position ctx "" pos "")
    (vlist2 level (bar_before level) (shi ctx 2)
       (sprintf "%s[ " (tab (shi ctx 2))) ll ("", " ]")) (tab ctx) k
;

value extend_body ctx b (globals, entries) k =
  match globals with
  [ [] -> vlist entry ctx b entries k
  | _ ->
      let globals = List.map (fun g -> (g, "")) globals in
      let s1 = plist expr 2 ctx (sprintf "%sGLOBAL: " b) globals ";" in
      let s2 = vlist entry ctx (tab ctx) entries k in
      sprintf "%s\n%s" s1 s2 ]
;

value extend ctx b e k =
  match e with
  [ <:expr< Grammar.extend $e$ >> ->
      try
        let ex = unextend_body e in
        let s = extend_body (shi ctx 2) (tab (shi ctx 2)) ex "" in
        sprintf "%sEXTEND\n%s\n%sEND%s" b s (tab ctx) k
      with
      [ Not_found ->
          sprintf "%sGrammar.extend\n%s" b
            (expr (shi ctx 2) (sprintf "%s(" (tab (shi ctx 2))) e k) ]
  | e -> expr ctx b e k ]
;

let lev = find_pr_level "apply" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< Grammar.extend $_$ >> as e ->
      fun curr next ctx b k -> next ctx b e k ];

let lev = find_pr_level "simple" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< Grammar.extend $_$ >> as e ->
      fun curr next ctx b k -> extend ctx b e k ];
