(* camlp5r *)
(* pr_extend.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";
#load "pa_macro.cmo";

(* heuristic to rebuild the EXTEND statement from the AST *)

open Pretty;
open Pcaml;
open Prtools;

value no_slist = ref False;
Pcaml.strict_mode.val := True;

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

IFDEF OCAML_VERSION <= OCAML_1_07 THEN
  value with_ind = Pprintf.with_ind;
  value with_bef = Pprintf.with_bef;
  value with_aft = Pprintf.with_aft;
END;

value bar_before elem pc x = pprintf pc "| %p" elem x;
value semi_after elem pc x = pprintf pc "%p;" elem x;

(* Extracting *)

type symbol =
  [ Snterm of MLast.expr
  | Snterml of MLast.expr and string
  | Slist0 of symbol
  | Slist0sep of symbol and symbol and bool
  | Slist1 of symbol
  | Slist1sep of symbol and symbol and bool
  | Sopt of symbol
  | Sflag of symbol
  | Sself
  | Snext
  | Scut
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

value unbool =
  fun
  [ <:expr< True >> -> True
  | <:expr< False >> -> False
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
  | <:expr< Grammar.production ($e1$, $e2$) >> ->
      let (pl, a) =
        match unaction e2 with
        [ ([], None) -> let loc = Ploc.dummy in ([], Some <:expr< () >>)
        | x -> x ]
      in
      let e1 =
        loop [] e1 where rec loop rel =
          fun
          [ <:expr< Grammar.r_next $el$ $e$ >> -> loop [e :: rel] el
          | <:expr< Grammar.r_stop >> -> rel
          | <:expr:< Grammar.r_cut $el$ >> -> loop [<:expr< cut >> :: rel] el
          | _ -> raise Not_found ]
      in
      let sl = safe_unpsymbol_list (List.rev pl) e1 in
      (sl, a)
  | _ -> raise Not_found ]
and safe_unpsymbol_list pl el =
  match (pl, el) with
  | ([], []) -> []
  | (pl, [<:expr< cut >> :: el]) ->
      [(None, Scut) :: safe_unpsymbol_list pl el]
  | ([p :: pl], [e :: el]) ->
      let op = match p with [ <:patt< _ >> -> None | _ -> Some p ] in
      [(op, safe_unsymbol e) :: safe_unpsymbol_list pl el]
  | _ -> raise Not_found
  end
and unpsymbol_list pl e =
  match (pl, e) with
  [ ([], <:expr< [] >>) -> []
  | (_, <:expr< [Gramext.Scut :: $el$] >>) ->
      [(None, Scut) :: unpsymbol_list pl el]
  | ([p :: pl], <:expr< [$e$ :: $el$] >>) ->
      let op =
        match p with
        [ <:patt< _ >> -> None
        | _ -> Some p ]
      in
      [(op, unsymbol e) :: unpsymbol_list pl el]
  | _ -> raise Not_found ]
and safe_unsymbol =
  fun
  | <:expr< Grammar.s_facto $e$ >> -> safe_unsymbol e
  | <:expr< Grammar.s_nterm ($e$ : $_$) >> -> Snterm e
  | <:expr< Grammar.s_nterml ($e$ : $_$) $str:s$ >> -> Snterml e s
  | <:expr< Grammar.s_list0 $e$ >> -> Slist0 (safe_unsymbol e)
  | <:expr< Grammar.s_list0sep $e1$ $e2$ $b$ >> ->
      Slist0sep (safe_unsymbol e1) (safe_unsymbol e2) (unbool b)
  | <:expr< Grammar.s_list1 $e$ >> -> Slist1 (safe_unsymbol e)
  | <:expr< Grammar.s_list1sep $e1$ $e2$ $b$ >> ->
      Slist1sep (safe_unsymbol e1) (safe_unsymbol e2) (unbool b)
  | <:expr< Grammar.s_opt $e$ >> -> Sopt (safe_unsymbol e)
  | <:expr< Grammar.s_flag $e$ >> -> Sflag (safe_unsymbol e)
  | <:expr< Grammar.s_self >> -> Sself
  | <:expr< Grammar.s_next >> -> Snext
  | <:expr< Grammar.s_token $e$ >> -> Stoken (untoken e)
  | <:expr< Grammar.s_rules $e$ >> -> Srules (rev_unlist unrule [] e)
  | <:expr< Grammar.s_vala $ls$ $e$ >> ->
      Svala (unlist unstring ls) None (safe_unsymbol e)
  | _ -> raise Not_found
  end
and unsymbol =
  fun
  [ <:expr< Gramext.Sfacto $e$ >> -> unsymbol e
  | <:expr< Gramext.Snterm ($uid:_$.Entry.obj ($e$ : $_$)) >> -> Snterm e
  | <:expr< Gramext.Snterml ($uid:_$.Entry.obj ($e$ : $_$)) $str:s$ >> ->
      Snterml e s
  | <:expr< Gramext.Snterml ($uid:_$.Entry.obj ($e$ : $_$), $str:s$) >> ->
      Snterml e s
  | <:expr< Gramext.Slist0 $e$ >> -> Slist0 (unsymbol e)
  | <:expr< Gramext.Slist0sep $e1$ $e2$ $b$ >> ->
      Slist0sep (unsymbol e1) (unsymbol e2) (unbool b)
  | <:expr< Gramext.Slist0sep ($e1$, $e2$, $b$) >> ->
      Slist0sep (unsymbol e1) (unsymbol e2) (unbool b)
  | <:expr< Gramext.Slist1 $e$ >> -> Slist1 (unsymbol e)
  | <:expr< Gramext.Slist1sep $e1$ $e2$ $b$ >> ->
      Slist1sep (unsymbol e1) (unsymbol e2) (unbool b)
  | <:expr< Gramext.Slist1sep ($e1$, $e2$, $b$) >> ->
      Slist1sep (unsymbol e1) (unsymbol e2) (unbool b)
  | <:expr< Gramext.Sopt $e$ >> -> Sopt (unsymbol e)
  | <:expr< Gramext.Sflag $e$ >> -> Sflag (unsymbol e)
  | <:expr< Gramext.Sself >> -> Sself
  | <:expr< Gramext.Snext >> -> Snext
  | <:expr< Gramext.Scut >> -> Scut
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
  | <:expr<
      Grammar.extension ($e$ : Grammar.Entry.e '$_$) $pos$ $ll$
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
  | Some (Gramext.Before s) -> pprintf pc " BEFORE %p" string s
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

value comment pc loc = pprintf pc "%s" (Prtools.comm_bef pc.ind loc);

value rec rule force_vertic pc (sl, a) =
  match a with
  [ None -> not_impl "rule 1" pc sl
  | Some a ->
      if sl = [] then
        pprintf pc "@[<4>→%p %q@]" comment (MLast.loc_of_expr a)
          (action expr) a "|"
      else
        match
          horiz_vertic
            (fun () ->
               let s =
                 let pc = {(pc) with aft = ""} in
                 pprintf pc "%p →" (hlistl (semi_after psymbol) psymbol) sl
               in
               Some s)
            (fun () -> None)
        with
        [ Some s1 ->
            let pc = {(pc) with bef = ""} in
            horiz_vertic
              (fun () ->
                 if force_vertic then sprintf "\n"
                 else pprintf pc "%s %q" s1 (action expr) a "|")
              (fun () ->
                 pprintf pc "%s@;<1 4>%q" s1 (action expr) a "|")
        | None ->
            let sl = List.map (fun s -> (s, ";")) sl in
            pprintf pc "@[<2>%p →@;%q@]" (plist psymbol 0) sl
              (action expr) a "|" ] ]
and psymbol pc (p, s) =
  match p with
  [ None -> symbol pc s
  | Some p -> pprintf pc "%p =@;%p" pattern p symbol s ]
and pattern pc p =
  match p with
  [ <:patt< $lid:i$ >> -> pprintf pc "%s" i
  | <:patt< _ >> -> pprintf pc "_"
  | <:patt< ($list:pl$) >> ->
      let pl = List.map (fun p -> (p, ",")) pl in
      pprintf pc "(%p)" (plist patt 1) pl
  | p ->
      pprintf pc "@[<1>(%p)@]" patt p ]
and symbol pc sy =
  match sy with
  [ Snterm e -> expr pc e
  | Snterml e s -> pprintf pc "%p LEVEL \"%s\"" expr e s
  | Slist0 sy ->
      pprintf pc "LIST0@;%p" simple_symbol sy
  | Slist0sep sy sep b ->
      pprintf pc "LIST0@;%p@ @[SEP@;%p%s@]" simple_symbol sy simple_symbol sep
        (if b then " OPT_SEP" else "")
  | Slist1 sy ->
      pprintf pc "LIST1@;%p" simple_symbol sy
  | Slist1sep sy sep b ->
      pprintf pc "LIST1@;%p@ @[SEP@;%p%s@]" simple_symbol sy simple_symbol sep
        (if b then " OPT_SEP" else "")
  | Sopt sy ->
      pprintf pc "OPT@;%p" simple_symbol sy
  | Sflag sy ->
      pprintf pc "FLAG@;%p" simple_symbol sy
  | Srules rl ->
      match check_slist rl with
      [ Some s -> s_symbol pc s
      | None -> simple_symbol pc sy ]
  | Stoken tok -> token pc tok
  | Svala sl _ sy ->
      pprintf pc "V @[<2>%p%p@]" simple_symbol sy string_list sl
  | sy -> simple_symbol pc sy ]
and simple_symbol pc sy =
  match sy with
  [ Snterm <:expr< $lid:s$ >> -> pprintf pc "%s" s
  | Sself -> pprintf pc "SELF"
  | Snext -> pprintf pc "NEXT"
  | Scut -> pprintf pc "/"
  | Srules rl ->
      match check_slist rl with
      [ Some _ -> pprintf pc "(%p)" symbol sy
      | None ->
          horiz_vertic
            (fun () ->
               pprintf pc "[ %p ]"
                 (hlist2 (rule False) (bar_before (rule False))) rl)
            (fun () ->
               pprintf pc "[ %p ]"
                 (vlist2 (rule False) (bar_before (rule False))) rl) ]
  | Stoken (Left ("", _) | Left (_, "")) -> symbol pc sy
  | Snterml _ _ | Slist0 _ | Slist0sep _ _ _ | Slist1 _ | Slist1sep _ _ _ |
    Sflag _ | Sopt _ ->
      pprintf pc "@[<1>(%p)@]" symbol sy
  | sy -> not_impl "simple_symbol" pc sy ]
and s_symbol pc =
  fun
  [ Slist0 sy -> pprintf pc "SLIST0@;%p" simple_symbol sy
  | Slist1 sy -> pprintf pc "SLIST1@;%p" simple_symbol sy
  | Slist0sep sy sep b ->
      pprintf pc "SLIST0@;%p@ @[SEP@;%p%s@]" simple_symbol sy simple_symbol
        sep (if b then " OPT_SEP" else "")
  | Slist1sep sy sep b ->
      pprintf pc "SLIST1@;%p@ @[SEP@;%p%s@]" simple_symbol sy simple_symbol
        sep (if b then " OPT_SEP" else "")
  | Sopt s ->
      let sy =
        match s with
        [ Srules
            [([(Some <:patt< x >>, Stoken (Left ("", str)))],
              Some <:expr< Qast.Str x >>)] ->
            Stoken (Left ("", str))
        | s -> s ]
      in
      pprintf pc "SOPT@;%p" simple_symbol sy
  | Sflag sy ->
      pprintf pc "SFLAG@;%p" simple_symbol sy
  | Svala ls oe s ->
      pprintf pc "SV@;%p%p%s" simple_symbol s string_list ls
        (match oe with
         [ Some e -> " " ^ e
         | None -> "" ])
  | _ -> assert False ]
and check_slist rl =
  if no_slist.val then None
  else
    match rl with
    [ [([(Some <:patt< a >>, Snterm <:expr< a_list >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>,
          ((Slist0 _ | Slist1 _ | Slist0sep _ _ _ | Slist1sep _ _ _) as s))],
          Some <:expr< Qast.List a >>)] ->
        Some s
    | [([(Some <:patt< a >>, Snterm <:expr< a_list2 >>)], Some <:expr< a >>);
       ([(Some <:patt< a >>,
          ((Slist0 _ | Slist1 _ | Slist0sep _ _ _ | Slist1sep _ _ _) as s))],
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
                | ((Slist0 _ | Slist0sep _ _ _), ["list"]) -> []
                | ((Slist1 _ | Slist1sep _ _ _), ["list"]) -> []
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

value label pc =
  fun
  [ Some s -> pprintf pc "\"%s\"" s
  | None -> pprintf pc "" ]
;

value assoc pc =
  fun
  [ Some Gramext.NonA -> pprintf pc "NONA"
  | Some Gramext.LeftA -> pprintf pc "LEFTA"
  | Some Gramext.RightA -> pprintf pc "RIGHTA"
  | None -> pprintf pc "" ]
;

value level force_vertic pc (lab, ass, rl) =
  match (lab, ass) with
  [ (None, None) ->
      if rl = [] then pprintf pc "[ ]"
      else
        pprintf pc "@[<2>[ %p ]@]"
          (vlist2 (rule force_vertic) (bar_before (rule force_vertic))) rl
  | _ ->
      pprintf pc "@[<b>%p@;[ %p ]@]"
        (fun pc ->
           fun
           [ (Some _, None) -> label pc lab
           | (None, Some _) -> assoc pc ass
            | (Some _, Some _) -> pprintf pc "%p %p" label lab assoc ass
            | _ -> assert False ])
        (lab, ass)
        (vlist2 (rule force_vertic) (bar_before (rule force_vertic))) rl ]
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
  comm_bef pc.ind (MLast.loc_of_expr e) ^
  pprintf pc "@[<b>%p:%p@;[ %p ]@ ;@]" expr e position pos
    (vlist2 (level force_vertic) (bar_before (level force_vertic))) ll
;

value extend_body pc (globals, entries) =
  match globals with
  [ [] -> vlist entry pc entries
  | _ ->
      let globals = List.map (fun g -> (g, "")) globals in
      pprintf pc "@[<b>GLOBAL: %p;@ %p@]" (plist expr 2) globals
        (vlist entry) entries ]
;

value extend pc e =
  match e with
  [ <:expr< Grammar.extend $e$ >> ->
      try
        let ex = unextend_body e in
        pprintf pc "EXTEND@;%p@ END" extend_body ex
      with
      [ Not_found -> pprintf pc "Grammar.extend@;@[<1>(%p)@]" expr e ]
  | <:expr< Grammar.safe_extend $e$ >> ->
      try
        let ex = unextend_body e in
        pprintf pc "EXTEND@;%p@ END" extend_body ex
      with
      [ Not_found -> pprintf pc "Grammar.safe_extend@;@[<1>(%p)@]" expr e ]
  | e -> expr pc e ]
;

EXTEND_PRINTER
  pr_expr: LEVEL "apply"
    [ [ <:expr< Grammar.extend $_$ >> as e -> next pc e
      | <:expr< Grammar.safe_extend $_$ >> as e -> next pc e ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< Grammar.extend $_$ >> as e -> extend pc e
      | <:expr< Grammar.safe_extend $_$ >> as e -> extend pc e ] ]
  ;
END;

Pcaml.add_option "-no_slist" (Arg.Set no_slist)
  "Don't reconstruct SLIST, SOPT, SFLAG";
