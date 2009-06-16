(* camlp5r q_MLast.cmo ./pa_extfun.cmo ./pa_extprint.cmo ./pa_pprintf.cmo *)
(* $Id: pr_extend.ml,v 1.56 2008/01/03 13:45:33 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2008 *)

(* heuristic to rebuild the EXTEND statement from the AST *)

open Pretty;
open Pcaml;
open Prtools;

value no_slist = ref False;
Pcaml.strict_mode.val := True;

(**)
value test = ref False;
Pcaml.add_option "-test" (Arg.Set test) " test";
(**)

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      "\"" ^ Obj.magic x ^ "\""
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  pprintf pc "\"pr_extend, not impl: %s; %s\"" name (String.escaped desc)
;

value bar_before elem pc x = pprintf pc "| %p" elem x;
value semi_after elem pc x = pprintf pc "%p;" elem x;

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
  | Svala of list string and option string and symbol ]
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
  | <:expr< Some (Gramext.Like $str:s$) >> -> Some (Gramext.Like s)
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

value rec unlist unelem =
  fun
  [ <:expr< [$e$ :: $el$] >> -> [unelem e :: unlist unelem el]
  | <:expr< [] >> -> []
  | _ -> raise Not_found ]
;

value rec rev_unlist unelem list =
  fun
  [ <:expr< [$e$ :: $el$] >> -> rev_unlist unelem [unelem e :: list] el
  | <:expr< [] >> -> list
  | _ -> raise Not_found ]
;

value unstring =
  fun
  [ <:expr< $str:s$ >> -> s
  | _ -> assert False ]
;

value untoken =
  fun
  [ <:expr< ($str:x$, $str:y$) >> -> Left (x, y)
  | <:expr< ($str:_$, $lid:_$) >> as e -> Right e
  | _ -> raise Not_found ]
;

value rec unrule =
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
  [ <:expr< Gramext.Sfacto $e$ >> -> unsymbol e
  | <:expr< Gramext.Snterm ($uid:_$.Entry.obj ($e$ : $_$)) >> -> Snterm e
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
  | <:expr< Gramext.srules $e$ >> -> Srules (rev_unlist unrule [] e)
  | <:expr< Gramext.Svala $ls$ $e$ >> ->
      Svala (unlist unstring ls) None (unsymbol e)
  | _ -> raise Not_found ]
;

value unlevel =
  fun
  [ <:expr< ($e1$, $e2$, $e3$) >> ->
      (unlabel e1, unassoc e2, rev_unlist unrule [] e3)
  | _ -> raise Not_found ]
;

value unentry =
  fun
  [ <:expr<
      (Grammar.Entry.obj ($e$ : Grammar.Entry.e '$_$), $pos$, $ll$)
    >> ->
      (e, unposition pos, unlist unlevel ll)
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

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;

value string pc s = pprintf pc "\"%s\"" s;

value position pc pos =
  match pos with
  [ None -> pprintf pc ""
  | Some Gramext.First -> pprintf pc " FIRST"
  | Some Gramext.Last -> pprintf pc " LAST"
  | Some (Gramext.Before s) -> pprintf pc " BEFORE"
  | Some (Gramext.After s) -> pprintf pc " AFTER %p" string s
  | Some (Gramext.Like s) -> pprintf pc " LIKE %p" string s
  | Some (Gramext.Level s) -> pprintf pc " LEVEL %p" string s ]
;

value action expr pc a = expr pc a;

value token pc tok =
  match tok with
  [ Left (con, prm) ->
      if con = "" then string pc prm
      else if prm = "" then pprintf pc "%s" con
      else pprintf pc "%s %p" con string prm
  | Right <:expr< ("", $x$) >> -> pprintf pc "$%p$" expr x
  | Right <:expr< ($str:con$, $x$) >> -> pprintf pc "%s $%p$" con expr x
  | Right _ -> assert False ]
;

value rec string_list pc =
  fun
  [ [s :: sl] -> pprintf pc " \"%s\"%p" s string_list sl
  | [] -> pprintf pc "" ]
;

value anti_anti n =
  if n <> "" && (n.[0] = '~' || n.[0] = '?') then
    String.make 1 n.[0] ^ "_" ^ String.sub n 1 (String.length n - 1)
  else "_" ^ n
;

value anti_of_tok =
  fun
  [ "CHAR" -> ["chr"]
  | "FLOAT" -> ["flo"]
  | "INT" -> ["int"]
  | "INT_l" -> ["int32"]
  | "INT_L" -> ["int64"]
  | "INT_n" -> ["nativeint"]
  | "LIDENT" -> ["lid"; ""]
  | "QUESTIONIDENT" -> ["?"]
  | "QUESTIONIDENTCOLON" -> ["?:"]
  | "STRING" -> ["str"]
  | "TILDEIDENT" -> ["~"]
  | "TILDEIDENTCOLON" -> ["~:"]
  | "UIDENT" -> ["uid"; ""]
  | s -> [] ]
;

value rec rule force_vertic pc (sl, a) =
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
                 if force_vertic then sprintf "\n"
                 else
                   sprintf "%s %s%s" s1
                     (action expr {(pc) with bef = ""; aft = ""; dang = "|"}
                        a)
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
  | Svala sl _ sy ->
      sprintf "%sV %s%s%s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft = ""} sy)
        (string_list {(pc) with bef = ""; aft = ""} sl)
        pc.aft
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
               hlist2 (rule False) (bar_before (rule False))
                 {(pc) with bef = sprintf "%s[ " pc.bef;
                  aft = sprintf " ]%s" pc.aft}
                 rl)
            (fun () ->
               vlist2 (rule False) (bar_before (rule False))
                 {(pc) with bef = sprintf "%s[ " pc.bef;
                  aft = sprintf " ]%s" pc.aft}
                 rl) ]
  | Stoken (Left ("", _) | Left (_, "")) -> symbol pc sy
  | Snterml _ _ | Slist0 _ | Slist0sep _ _ | Slist1 _ | Slist1sep _ _ |
    Sflag _ | Sopt _ ->
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
  | Svala ls oe s ->
      sprintf "%sSV %s%s%s%s" pc.bef
        (simple_symbol {(pc) with bef = ""; aft= ""} s)
        (string_list {(pc) with bef = ""; aft = ""} ls)
        (match oe with
         [ Some e -> " " ^ e
         | None -> "" ])
        pc.aft
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
          Some <:expr< Qast.VaVal (Qast.List a) >>)] ->
        Some (Svala [] None s)

    | [([(Some <:patt< a >>, Snterm <:expr< a_opt >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>, Sopt s)], Some <:expr< Qast.Option a >>)] ->
        Some (Sopt s)
    | [([(Some <:patt< a >>, Snterm <:expr< a_opt2 >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>, (Sopt _ as s))],
          Some <:expr< Qast.VaVal (Qast.Option a) >>)] ->
        Some (Svala [] None s)

    | [([(Some <:patt< a >>, Snterm <:expr< a_flag >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>, Sflag s)], Some <:expr< Qast.Bool a >>)] ->
        Some (Sflag s)
    | [([(Some <:patt< a >>, Snterm <:expr< a_flag2 >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>, (Sflag _ as s))],
          Some <:expr< Qast.VaVal (Qast.Bool a) >>)] ->
        Some (Svala [] None s)

    | rl ->
        loop [] rl where rec loop ls =
          fun
          [ [([(Some <:patt< a >>, Stoken (Left ("ANTIQUOT", n)))],
              Some <:expr< Qast.VaVal (Qast.VaAnt $str:_$ loc a) >>);
             ([(Some <:patt< a >>, Stoken (Left ("ANTIQUOT", a_n)))],
              Some <:expr< Qast.VaAnt $str:_$ loc a >>) :: rl]
            when a_n = anti_anti n ->
              loop [n :: ls] rl
          | [([(Some <:patt< a >>, s)], Some <:expr< Qast.VaVal $_$ >>)] ->
              let ls = List.rev ls in
              let ls =
                match (s, ls) with
                [ (Sflag _, ["flag"; "opt"]) -> []
                | ((Slist0 _ | Slist0sep _ _), ["list"]) -> []
                | ((Slist1 _ | Slist1sep _ _), ["list"]) -> []
                | (Sopt _, ["opt"]) -> []
                | (Stoken (Left (s, "")), _) ->
                    if ls = anti_of_tok s then [] else ls
                | _ -> ls ]                   
              in
              Some (Svala ls None s)
          | [([(Some <:patt< a >>, s)], Some <:expr< Qast.VaVal $_$ >>);
             ([(Some <:patt< a >>, Snterm <:expr< $lid:e$ >>)],
              Some <:expr< a >>)] ->
              Some (Svala ls (Some e) s)
          | _ -> None ] ]
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

value level force_vertic pc (lab, ass, rl) =
  match (lab, ass) with
  [ (None, None) ->
      if rl = [] then sprintf "%s[ ]%s" pc.bef pc.aft
      else
        vlist2 (rule force_vertic) (bar_before (rule force_vertic))
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
          vlist2 (rule force_vertic) (bar_before (rule force_vertic))
            {(pc) with ind = pc.ind + 2;
             bef = sprintf "%s[ " (tab (pc.ind + 2));
             aft = sprintf " ]%s" pc.aft} rl
      in
      sprintf "%s\n%s" s1 s2 ]
;

value entry pc (e, pos, ll) =
  let force_vertic =
    if flag_equilibrate_cases.val then
      let has_vertic =
        let f = bar_before (bar_before (rule False)) pc in
        List.exists
          (fun (_, _, rl) ->
             List.exists
               (fun r ->
                  horiz_vertic
                    (fun () ->
                       let _ : string = f r in
                       False)
                    (fun () -> True))
               rl)
          ll
      in
      has_vertic
    else False
  in
  sprintf "%s%s%s:%s\n%s\n%s;%s" (comm_bef pc (MLast.loc_of_expr e)) pc.bef
    (expr {(pc) with bef = ""; aft = ""} e)
    (position {(pc) with bef = ""; aft = ""} pos)
    (vlist2 (level force_vertic) (bar_before (level force_vertic))
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
