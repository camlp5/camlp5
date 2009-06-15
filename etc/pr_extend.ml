(* camlp5r q_MLast.cmo ./pa_extfun.cmo ./pa_extprint.cmo *)
(* $Id: pr_extend.ml,v 1.38 2007/09/13 13:21:24 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* heuristic to rebuild the EXTEND statement from the AST *)

open Pretty;
open Pcaml;
open Prtools;

value no_slist = ref False;
Pcaml.strict_mode.val := True;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_extend, not impl: %s; %s\"%s" pc.bef name
    (String.escaped desc) pc.aft
;

value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;
value semi_after elem pc x = elem {(pc) with aft = sprintf ";%s" pc.aft} x;

(* Extracting *)

type symbol =
  [ Snterm of MLast.expr
  | Snterml of MLast.expr and string
  | Slist0 of symbol
  | Slist0sep of symbol and symbol
  | Slist1 of symbol
  | Slist1sep of symbol and symbol
  | Sopt of symbol
  | Sflag of symbol
  | Sself
  | Snext
  | Stoken of alt Plexing.pattern MLast.expr
  | Srules of list (list (option MLast.patt * symbol) * option MLast.expr)
  | Svala of symbol ]
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
  [ <:expr< fun ($lid:locp$ : Ploc.t) -> ($a$ : $_$) >>
    when locp = Ploc.name.val ->
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
      (let loc = Ploc.dummy in [<:patt< _ >> :: pl], a)
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
        [ ([], None) -> let loc = Ploc.dummy in ([], Some <:expr< () >>)
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
  | <:expr< Gramext.Sflag $e$ >> -> Sflag (unsymbol e)
  | <:expr< Gramext.Sself >> -> Sself
  | <:expr< Gramext.Snext >> -> Snext
  | <:expr< Gramext.Stoken $e$ >> -> Stoken (untoken e)
  | <:expr< Gramext.srules $e$ >> -> Srules (unrule_list [] e)
  | <:expr< Gramext.Svala $e$ >> -> Svala (unsymbol e)
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
        let grammar_entry_create s = $_$ (Grammar.of_entry $_$) s in
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

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;

value string pc s = sprintf "%s\"%s\"%s" pc.bef s pc.aft;

value position pc pos =
  match pos with
  [ None -> sprintf "%s%s" pc.bef pc.aft
  | Some Gramext.First -> sprintf "%s FIRST%s" pc.bef pc.aft
  | Some Gramext.Last -> sprintf "%s LAST%s" pc.bef pc.aft
  | Some (Gramext.Before s) -> sprintf "%s BEFORE%s" pc.bef pc.aft
  | Some (Gramext.After s) ->
      sprintf "%s AFTER %s%s" pc.bef (string {(pc) with bef = ""; aft = ""} s)
        pc.aft
  | Some (Gramext.Level s) ->
      sprintf "%s LEVEL %s%s" pc.bef (string {(pc) with bef = ""; aft = ""} s)
        pc.aft ]
;

value action expr pc a = expr pc a;

value token pc tok =
  match tok with
  [ Left (con, prm) ->
      if con = "" then string pc prm
      else if prm = "" then sprintf "%s%s%s" pc.bef con pc.aft
      else
        sprintf "%s%s %s%s" pc.bef con
          (string {(pc) with bef = ""; aft = ""} prm) pc.aft
  | Right <:expr< ("", $x$) >> ->
      sprintf "%s$%s$%s" pc.bef (expr {(pc) with bef = ""; aft = ""} x)
        pc.aft
  | Right <:expr< ($str:con$, $x$) >> ->
      sprintf "%s%s $%s$%s" pc.bef con (expr {(pc) with bef = ""; aft = ""} x)
        pc.aft
  | Right _ -> assert False ]
;

value rec rule pc (sl, a) =
  match a with
  [ None -> not_impl "rule 1" pc sl
  | Some a ->
      if sl = [] then
        action expr
          {(pc) with ind = pc.ind + 4;
           bef =
             sprintf "%s->%s " pc.bef (comm_bef pc (MLast.loc_of_expr a));
           dang = "|"}
          a
      else
        match
          horiz_vertic
            (fun () ->
               let s =
                 hlistl (semi_after psymbol) psymbol
                   {(pc) with bef = ""; aft = ""} sl
               in
               Some (sprintf "%s%s ->" pc.bef s))
            (fun () -> None)
        with
        [ Some s1 ->
            horiz_vertic
              (fun () ->
                 sprintf "%s %s%s" s1
                   (action expr {(pc) with bef = ""; aft = ""; dang = "|"} a)
                   pc.aft)
              (fun () ->
                 let s2 =
                   action expr
                     {(pc) with ind = pc.ind + 4; bef = tab (pc.ind + 4);
                      dang = "|"}
                     a
                 in
                 sprintf "%s\n%s" s1 s2)
        | None ->
            let sl = List.map (fun s -> (s, ";")) sl in
            let s1 =
              plist psymbol 0 {(pc) with ind = pc.ind + 2; aft = " ->"} sl
            in
            let s2 =
              action expr
                {(pc) with ind = pc.ind + 4; bef = tab (pc.ind + 4);
                 dang = "|"}
                a
            in
            sprintf "%s\n%s" s1 s2 ] ]
and psymbol pc (p, s) =
  match p with
  [ None -> symbol pc s
  | Some p ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s = %s%s" pc.bef
             (pattern {(pc) with bef = ""; aft = ""} p)
             (symbol {(pc) with bef = ""; aft = ""} s) pc.aft)
        (fun () ->
           let s1 = pattern {(pc) with aft = " ="} p in
           let s2 =
             symbol {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} s
           in
           sprintf "%s\n%s" s1 s2) ]
and pattern pc p =
  match p with
  [ <:patt< $lid:i$ >> -> sprintf "%s%s%s" pc.bef i pc.aft
  | <:patt< _ >> -> sprintf "%s_%s" pc.bef pc.aft
  | <:patt< ($list:pl$) >> ->
      let pl = List.map (fun p -> (p, ",")) pl in
      plist patt 1
        {(pc) with bef = sprintf "%s(" pc.bef; aft = sprintf ")%s" pc.aft}
        pl
  | p ->
      patt
        {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
         aft = sprintf ")%s" pc.aft}
        p ]
and symbol pc sy =
  match sy with
  [ Snterm e -> expr pc e
  | Snterml e s -> expr {(pc) with aft = sprintf " LEVEL \"%s\"%s" s pc.aft} e
  | Slist0 sy ->
      sprintf "%sLIST0 %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Slist0sep sy sep ->
      sprintf "%sLIST0 %s SEP %s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
        (simple_symbol {(pc) with bef = ""} sep)
  | Slist1 sy ->
      sprintf "%sLIST1 %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Slist1sep sy sep ->
      sprintf "%sLIST1 %s SEP %s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
        (simple_symbol {(pc) with bef = ""} sep)
  | Sopt sy ->
      sprintf "%sOPT %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Sflag sy ->
      sprintf "%sFLAG %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Srules rl ->
      match check_slist rl with
      [ Some s -> s_symbol pc s
      | None -> simple_symbol pc sy ]
  | Stoken tok -> token pc tok
  | Svala sy -> symbol {(pc) with bef = "V " ^ pc.bef} sy
  | sy -> simple_symbol pc sy ]
and simple_symbol pc sy =
  match sy with  
  [ Snterm <:expr< $lid:s$ >> -> sprintf "%s%s%s" pc.bef s pc.aft
  | Sself -> sprintf "%sSELF%s" pc.bef pc.aft
  | Snext -> sprintf "%sNEXT%s" pc.bef pc.aft
  | Srules rl ->
      match check_slist rl with
      [ Some _ ->
          symbol
            {(pc) with bef = sprintf "%s(" pc.bef; aft = sprintf ")%s" pc.aft}
            sy
      | None ->
          horiz_vertic
            (fun () ->
               hlist2 rule (bar_before rule)
                 {(pc) with bef = sprintf "%s[ " pc.bef;
                  aft = sprintf " ]%s" pc.aft}
                 rl)
            (fun () ->
               vlist2 rule (bar_before rule)
                 {(pc) with bef = sprintf "%s[ " pc.bef;
                  aft = sprintf " ]%s" pc.aft}
                 rl) ]
  | Stoken (Left ("", _) | Left (_, "")) -> symbol pc sy
  | Snterml _ _ | Slist0 _ | Slist0sep _ _ | Slist1 _ | Slist1sep _ _ ->
      symbol
        {(pc) with bef = sprintf "%s(" pc.bef; aft = sprintf ")%s" pc.aft}
        sy
  | sy -> not_impl "simple_symbol" pc sy ]
and s_symbol pc =
  fun
  [ Slist0 sy ->
      sprintf "%sSLIST0 %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Slist1 sy ->
      sprintf "%sSLIST1 %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Slist0sep sy sep ->
      sprintf "%sSLIST0 %s SEP %s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
        (simple_symbol {(pc) with bef = ""} sep)
  | Slist1sep sy sep ->
      sprintf "%sSLIST1 %s SEP %s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
        (simple_symbol {(pc) with bef = ""} sep)
  | Sopt s ->
      let sy =
        match s with
        [ Srules
            [([(Some <:patt< x >>, Stoken (Left ("", str)))],
              Some <:expr< Qast.Str x >>)] ->
            Stoken (Left ("", str))
        | s -> s ]
      in
      sprintf "%sSOPT %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Sflag sy ->
      sprintf "%sSFLAG %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Svala (Sflag sy) ->
      sprintf "%sSV FLAG %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Svala (Sopt sy) ->
      sprintf "%sSV OPT %s" pc.bef (simple_symbol {(pc) with bef = ""} sy)
  | Svala (Slist0 sy) ->
      sprintf "%sSV LIST0 %s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
  | Svala (Slist0sep sy sep) ->
      sprintf "%sSV LIST0 %s SEP %s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
        (simple_symbol {(pc) with bef = ""} sep)
  | Svala (Slist1 sy) ->
      sprintf "%sSV LIST1 %s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
  | Svala (Slist1sep sy sep) ->
      sprintf "%sSV LIST1 %s SEP %s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
        (simple_symbol {(pc) with bef = ""} sep)
  | _ -> assert False ]
and check_slist rl =
  if no_slist.val then None
  else
    match rl with
    [ [([(Some <:patt< a >>, Snterm <:expr< a_list >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>,
          ((Slist0 _ | Slist1 _ | Slist0sep _ _ | Slist1sep _ _) as s))],
          Some <:expr< Qast.List a >>)] ->
        Some s
    | [([(Some <:patt< a >>, Snterm <:expr< a_list2 >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>,
          ((Slist0 _ | Slist1 _ | Slist0sep _ _ | Slist1sep _ _) as s))],
          Some <:expr< Qast.Node "Qast.Vala" [Qast.List a] >>)] ->
        Some (Svala s)
    | [([(Some <:patt< a >>, Snterm <:expr< a_opt >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>, Sopt s)], Some <:expr< Qast.Option a >>)] ->
        Some (Sopt s)
    | [([(Some <:patt< a >>, Snterm <:expr< a_flag >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>, Sflag s)], Some <:expr< Qast.Bool a >>)] ->
        Some (Sflag s)
    | [([(Some <:patt< a >>, Snterm <:expr< a_flag2 >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>, (Sflag _ as s))],
          Some <:expr< Qast.Node "Qast.Vala" [Qast.Bool a] >>)] ->
        Some (Svala s)
    | [([(Some <:patt< a >>, Snterm <:expr< a_opt2 >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>, (Sopt _ as s))],
          Some <:expr< Qast.Node "Qast.Vala" [Qast.Option a] >>)] ->
        Some (Svala s)
    | _ -> None ]
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

value level pc (lab, ass, rl) =
  match (lab, ass) with
  [ (None, None) ->
      if rl = [] then sprintf "%s[ ]%s" pc.bef pc.aft
      else
        vlist2 rule (bar_before rule)
          {(pc) with ind = pc.ind + 2; bef = sprintf "%s[ " pc.bef;
           aft = sprintf " ]%s" pc.aft}
          rl
  | _ ->
      let s1 =
        match (lab, ass) with
        [ (Some _, None) -> sprintf "%s%s" pc.bef (label lab)
        | (None, Some _) -> sprintf "%s%s" pc.bef (assoc ass)
        | (Some _, Some _) -> sprintf "%s%s %s" pc.bef (label lab) (assoc ass)
        | _ -> assert False ]
      in
      let s2 =
        if rl = [] then not_impl "level" {(pc) with bef = ""} rl
        else
          vlist2 rule (bar_before rule)
            {(pc) with ind = pc.ind + 2;
             bef = sprintf "%s[ " (tab (pc.ind + 2));
             aft = sprintf " ]%s" pc.aft} rl
      in
      sprintf "%s\n%s" s1 s2 ]
;

value entry pc (e, pos, ll) =
  sprintf "%s%s%s:%s\n%s\n%s;%s" (comm_bef pc (MLast.loc_of_expr e)) pc.bef
    (expr {(pc) with bef = ""; aft = ""} e)
    (position {(pc) with bef = ""; aft = ""} pos)
    (vlist2 level (bar_before level)
       {(pc) with ind = pc.ind + 2; bef = sprintf "%s[ " (tab (pc.ind + 2));
        aft = " ]"}
        ll)
    (tab pc.ind) pc.aft
;

value extend_body pc (globals, entries) =
  match globals with
  [ [] -> vlist entry pc entries
  | _ ->
      let globals = List.map (fun g -> (g, "")) globals in
      let s1 =
        plist expr 2 {(pc) with bef = sprintf "%sGLOBAL: " pc.bef; aft = ";"}
          globals
      in
      let s2 = vlist entry {(pc) with bef = tab pc.ind} entries in
      sprintf "%s\n%s" s1 s2 ]
;

value extend pc e =
  match e with
  [ <:expr< Grammar.extend $e$ >> ->
      try
        let ex = unextend_body e in
        let s =
          extend_body
            {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""} ex
        in
        sprintf "%sEXTEND\n%s\n%sEND%s" pc.bef s (tab pc.ind) pc.aft
      with
      [ Not_found ->
          sprintf "%sGrammar.extend\n%s" pc.bef
            (expr
               {(pc) with ind = pc.ind + 2;
                bef = sprintf "%s(" (tab (pc.ind + 2));
                aft = sprintf ")%s" pc.aft}
               e) ]
  | e -> expr pc e ]
;

EXTEND_PRINTER
  pr_expr: LEVEL "apply"
    [ [ <:expr< Grammar.extend $_$ >> as e -> next pc e ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< Grammar.extend $_$ >> as e -> extend pc e ] ]
  ;
END;

Pcaml.add_option "-no_slist" (Arg.Set no_slist)
  "Don't reconstruct SLIST, SOPT, SFLAG";
