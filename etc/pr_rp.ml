(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_rp.ml,v 1.1 2007/07/03 13:36:01 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* Heuristic to rebuild parsers and streams from the AST *)

open Pretty;
open Pcaml.Printers;
open Prtools;

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and option MLast.expr
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpLet of MLast.loc and MLast.patt and MLast.expr
  | SpLhd of MLast.loc and list (list MLast.patt)
  | SpStr of MLast.loc and MLast.patt ]
;

type spat_comp_opt =
  [ SpoNoth
  | SpoBang
  | SpoQues of MLast.expr ]
;

type alt 'a 'b =
  [ Left of 'a
  | Right of 'b ]
;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_rp, not impl: %s; %s\"%s" pc.bef name (String.escaped desc)
    pc.aft
;

value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;
value semi_after elem pc x = elem {(pc) with aft = sprintf ";%s" pc.aft} x;

(* Rebuilding syntax tree *)

value loc = Token.dummy_loc;

value rec handle_failure e =
  match e with
  [ <:expr< match $e$ with [ $list:pel$ ] >> ->
      handle_failure e &&
      List.for_all
        (fun
         [ (p, None, e) -> handle_failure e
         | _ -> False ])
        pel
  | <:expr< raise $e$ >> ->
      match e with
      [ <:expr< Stream.Failure >> -> False
      | _ -> True ]
  | <:expr< try $te$ with [ Stream.Failure -> $e$] >> -> handle_failure e
  | <:expr< $f$ $e$ >> ->
      no_raising_failure_fun f && handle_failure f && handle_failure e
  | <:expr< $lid:_$ >> | <:expr< $uid:_$ >> -> True
  | _ -> False ]
and no_raising_failure_fun =
  fun
  [ <:expr< $x$ $y$ >> -> no_raising_failure_fun x && handle_failure y
  | <:expr< $uid:_$ >> -> True
  | _ -> False ]
;

value rec contains_strm__ =
  fun
  [ <:expr< $e1$ $e2$ >> -> contains_strm__ e1 || contains_strm__ e2
  | <:expr< strm__ >> -> True
  | <:expr< let $opt:_$ $list:pel$ in $e$ >> -> contains_strm__ e
  | <:expr< try $e$ with [ $list:pel$ ] >> -> contains_strm__ e
  | <:expr< match $e$ with [ $list:pel$ ] >> -> contains_strm__ e
  | _ -> False ]
;

value err =
  fun
  [ <:expr< "" >> -> SpoNoth
  | e -> SpoQues e ]
;

value rec unstream_pattern_kont =
  fun
  [ <:expr<
      let $p$ =
        try $f$ with [ Stream.Failure -> raise (Stream.Error $e2$) ]
      in
      $e$
    >> ->
      let f =
        match f with
        [ <:expr< $f$ strm__ >> -> f
        | _ -> <:expr< fun (strm__ : Stream.t _) -> $f$ >> ]
      in
      let (sp, epo, e) = unstream_pattern_kont e in
      ([(SpNtr loc p f, err e2) :: sp], epo, e)
  | <:expr< let $lid:p$ = Stream.count strm__ in $e$ >> ->
      ([], Some p, e)
  | <:expr< let $p$ = strm__ in $e$ >> ->
      let (sp, epo, e) = unstream_pattern_kont e in
      ([(SpStr loc p, SpoNoth) :: sp], epo, e)
  | <:expr< let $p$ = $e1$ in $e2$ >> as ge ->
      if contains_strm__ e1 then
        let (f, err) =
          match e1 with
          [ <:expr< $f$ strm__ >> -> (f, SpoBang)
          | _ ->
              let f = <:expr< fun (strm__ : Stream.t _) -> $e1$ >> in
              let err = if handle_failure e1 then SpoNoth else SpoBang in
              (f, err) ]
        in
        let (sp, epo, e) = unstream_pattern_kont e2 in
        ([(SpNtr loc p f, err) :: sp], epo, e)
      else
        let (sp, epo, e) = unstream_pattern_kont e2 in
        if sp = [] then ([], None, ge)
        else ([(SpLet loc p e1, SpoNoth) :: sp], epo, e)
  | <:expr<
      match Stream.peek strm__ with
      [ Some $p$ -> do { Stream.junk strm__; $e$ }
      | _ -> raise (Stream.Error $e2$) ]
    >> ->
      let (sp, epo, e) = unstream_pattern_kont e in
      let sp = [(SpTrm loc p None, err e2) :: sp] in
      (sp, epo, e)
  | <:expr< match Stream.peek strm__ with [ $list:_$ ] >> |
    <:expr<
      match try Some ($_$ strm__) with [ Stream.Failure -> None ] with
      [ Some $_$ -> $_$
      | _ -> $_$ ]
    >> as ge ->
      let f = <:expr< fun (strm__ : Stream.t _) -> $ge$ >> in
      let err = if handle_failure ge then SpoNoth else SpoBang in
      ([(SpNtr loc <:patt< a >> f, err)], None, <:expr< a >>)
  | <:expr<
      try $f$ strm__ with [ Stream.Failure -> raise (Stream.Error $e$) ]
    >> ->
      ([(SpNtr loc <:patt< a >> f, err e)], None, <:expr< a >>)
  | <:expr< try $f$ with [ Stream.Failure -> raise (Stream.Error $e$) ] >> ->
      let f = <:expr< fun (strm__ : Stream.t _) -> $f$ >> in
      ([(SpNtr loc <:patt< a >> f, err e)], None, <:expr< a >>)
  | <:expr< $f$ strm__ >> ->
      ([(SpNtr loc <:patt< a >> f, SpoBang)], None, <:expr< a >>)
  | e -> ([], None, e) ]
;

value rec unparser_cases_list =
  fun
  [ <:expr<
      let $p$ = try $f$ strm__ with [ Stream.Failure -> raise $e2$ ] in $e1$
    >> ->
      let spe1 =
        let (sp, epo, e) = unstream_pattern_kont e1 in
        ([(SpNtr loc p f, SpoNoth) :: sp], epo, e)
      in
      let spe2 = ([], None, <:expr< raise $e2$ >>) in
      [spe1; spe2]
  | <:expr< let $p$ = $f$ strm__ in $e$ >> ->
      let (sp, epo, e) = unstream_pattern_kont e in
      [([(SpNtr loc p f, SpoNoth) :: sp], epo, e)]
  | <:expr< match Stream.peek strm__ with [ $list:pel$ ] >> as ge ->
      loop [] pel where rec loop rev_spel =
        fun
        [ [(<:patt< _ >>, None, e)] ->
            List.rev_append rev_spel (unparser_cases_list e)
        | [(<:patt< Some $p$ >>, eo,
            <:expr< do { Stream.junk strm__; $e$ } >>) ::
           pel] ->
            let spe =
              let (sp, epo, e) = unstream_pattern_kont e in
              let sp = [(SpTrm loc p eo, SpoNoth) :: sp] in
              (sp, epo, e)
            in
            loop [spe :: rev_spel] pel
        | _ ->
            [([], None, ge)] ]
  | <:expr<
      match try Some ($f$ strm__) with [ Stream.Failure -> None ] with
      [ Some $p1$ -> $e1$
      | _ -> $e2$ ]
    >> ->
      let spe =
        let (sp, epo, e) = unstream_pattern_kont e1 in
        let sp = [(SpNtr loc p1 f, SpoNoth) :: sp] in
        (sp, epo, e)
      in
      let spel = unparser_cases_list e2 in
      [spe :: spel]
  | <:expr< try $f$ strm__ with [ Stream.Failure -> $e$ ] >> ->
      let spe = ([(SpNtr loc <:patt< a >> f, SpoNoth)], None, <:expr< a >>) in
      let spel = unparser_cases_list e in
      [spe :: spel]
  | <:expr< try Some ($f$ strm__) with [ Stream.Failure -> $e$ ] >> ->
      let spe =
        ([(SpNtr loc <:patt< a >> f, SpoNoth)], None, <:expr< Some a >>)
      in
      let spel = unparser_cases_list e in
      [spe :: spel]
  | <:expr< try $f$ with [ Stream.Failure -> $e$ ] >> ->
      let f = <:expr< fun (strm__ : Stream.t _) -> $f$ >> in
      let spe = ([(SpNtr loc <:patt< a >> f, SpoNoth)], None, <:expr< a >>) in
      let spel = unparser_cases_list e in
      [spe :: spel]
  | <:expr< $f$ strm__ >> ->
      let spe = ([(SpNtr loc <:patt< a >> f, SpoNoth)], None, <:expr< a >>) in
      [spe]
  | <:expr< raise Stream.Failure >> ->
      []
  | e ->
      [([], None, e)] ]
;

value unparser_body e =
  let (po, e) =
    match e with
    [ <:expr< let $lid:bp$ = Stream.count $lid:strm_n$ in $e$ >> ->
        (Some bp, e)
    | _ -> (None, e) ]
  in
  let spel = unparser_cases_list e in
  (po, spel)
;

(* Printing *)

value expr pc z = pr_expr.pr_fun "top" pc z;
value patt pc z = pr_patt.pr_fun "top" pc z;

value sequence_box pc expr el =
  let s1 = pc.bef " do {" in
  let s2 =
    vlistl (semi_after expr) expr
      {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""} el
  in
  let s3 = sprintf "%s%s%s" (tab pc.ind) "}" pc.aft in
  sprintf "%s\n%s\n%s" s1 s2 s3
;

value ident_option =
  fun
  [ Some s -> sprintf " %s" s
  | None -> "" ]
;

value stream_patt_comp pc spc =
  match spc with
  [ SpTrm _ p None ->
      patt {(pc) with ind = pc.ind + 1; bef = sprintf "%s`" pc.bef} p
  | SpTrm _ p (Some e) ->
      horiz_vertic
        (fun () ->
           sprintf "%s`%s when %s%s" pc.bef
             (patt {(pc) with ind = pc.ind + 1; bef = ""; aft = ""} p)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 = patt {(pc) with bef = sprintf "%s`" pc.bef; aft = ""} p in
           let s2 =
             horiz_vertic
               (fun () ->
                  sprintf "%swhen %s%s" (tab (pc.ind + 1))
                    (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
               (fun () ->
                  let s1 = sprintf "%swhen" (tab (pc.ind + 1)) in
                  let s2 =
                    expr {(pc) with ind = pc.ind + 3; bef = tab (pc.ind + 3)}
                      e
                  in
                  sprintf "%s\n%s" s1 s2)
           in
           sprintf "%s\n%s" s1 s2)
  | SpNtr _ p e ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s = %s%s" pc.bef
             (patt {(pc) with bef = ""; aft = ""} p)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 = patt {(pc) with aft = " ="} p in
           let s2 =
             expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
           in
           sprintf "%s\n%s" s1 s2)
  | SpLet _ p e ->
      horiz_vertic (fun () -> sprintf "\n")
        (fun () ->
           horiz_vertic
             (fun () ->
                sprintf "%slet %s = %s in%s" pc.bef
                  (patt {(pc) with bef = ""; aft = ""} p)
                  (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
             (fun () ->
                let s1 =
                  patt {(pc) with bef = sprintf "%slet " pc.bef; aft = " ="} p
                in
                let s2 =
                  expr
                    {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                     aft = ""} e
                in
                let s3 = sprintf "%sin%s" (tab pc.ind) pc.aft in
                sprintf "%s\n%s\n%s" s1 s2 s3))
  | SpStr _ p -> patt pc p
  | _ -> not_impl "stream_patt_comp" pc spc ]
;

value stream_patt_comp_err pc (spc, err) =
  match err with
  [ SpoNoth -> stream_patt_comp pc spc
  | SpoBang -> stream_patt_comp {(pc) with aft = sprintf " !%s" pc.aft} spc
  | SpoQues e ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s ? %s%s" pc.bef
             (stream_patt_comp {(pc) with bef = ""; aft = ""} spc)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 = stream_patt_comp {(pc) with aft = ""} spc in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 4;
                bef = sprintf "%s? " (tab (pc.ind + 2))}
               e
           in
           sprintf "%s\n%s" s1 s2) ]
;

value spc_kont =
  fun
  [ (SpLet _ _ _, _) -> ""
  | _ -> ";" ]
;

value stream_patt pc sp =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s" pc.bef
         (hlistl (semi_after stream_patt_comp_err) stream_patt_comp_err
            {(pc) with bef = ""; aft = ""} sp) pc.aft)
    (fun () ->
       let sp = List.map (fun spc -> (spc, spc_kont spc)) sp in
       plist stream_patt_comp_err 0 {(pc) with ind = pc.ind + 3} sp)
;

value parser_case pc (sp, po, e) =
  match sp with
  [ [] ->
      horiz_vertic
        (fun () ->
           sprintf "%s[: :]%s -> %s%s" pc.bef (ident_option po)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           match flatten_sequence e with
           [ Some el ->
               sequence_box
                 {(pc) with
                  bef k = sprintf "%s[: :]%s ->%s" pc.bef (ident_option po) k}
                 expr el
           | None ->
               let s1 = sprintf "%s[: :]%s ->" pc.bef (ident_option po) in
               let s2 =
                 expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
               in
               sprintf "%s\n%s" s1 s2 ])
  | _ ->
      horiz_vertic
        (fun () ->
           sprintf "%s[: %s :]%s -> %s%s" pc.bef
             (stream_patt {(pc) with bef = ""; aft = ""} sp)
             (ident_option po) (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           match flatten_sequence e with
           [ Some el ->
               sequence_box
                 {(pc) with
                  bef k =
                    stream_patt
                      {(pc) with bef = sprintf "%s[: " pc.bef;
                       aft = sprintf " :]%s ->%s" (ident_option po) k}
                      sp}
                 expr el
           | None ->
               let s1 =
                 stream_patt
                   {(pc) with bef = sprintf "%s[: " pc.bef;
                    aft = sprintf " :]%s ->" (ident_option po)}
                   sp
               in
               let s2 =
                 expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
               in
               sprintf "%s\n%s" s1 s2 ]) ]
;

value parser_case_sh pc spe = parser_case {(pc) with ind = pc.ind + 2} spe;

value parser_body pc (po, spel) =
  let s1 = ident_option po in
  let s2o =
    match spel with
    [ [spe] ->
        horiz_vertic
          (fun () ->
             let s =
               sprintf "%s%s %s%s" pc.bef s1
                 (parser_case {(pc) with bef = ""; aft = ""} spe) pc.aft
             in
             Some s)
          (fun () -> None)
    | _ -> None ]
  in
  match s2o with
  [ Some s -> s
  | None ->
      match spel with
      [ [] -> sprintf "%s []%s" pc.bef pc.aft
      | [spe] ->
          let s2 =
            parser_case {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
              spe
          in
          sprintf "%s%s\n%s" pc.bef s1 s2
      | _ ->
          let s2 =
            vlist2 parser_case_sh (bar_before parser_case_sh)
              {(pc) with bef = sprintf "%s[ " (tab pc.ind);
               aft = ("", sprintf " ]%s" pc.aft)}
              spel
          in
          sprintf "%s%s\n%s" pc.bef s1 s2 ] ]
;

value print_parser pc e =
  match e with
  [ <:expr< fun (strm__ : Stream.t _) -> $e$ >> ->
      let pa = unparser_body e in
      parser_body {(pc) with bef = sprintf "%sparser" pc.bef} pa
  | e -> expr pc e ]
;

value print_match_with_parser pc e =
  match e with
  [ <:expr< let (strm__ : Stream.t _) = $e1$ in $e2$ >> ->
      let pa = unparser_body e2 in
      let b =
        sprintf "%smatch %s with parser" pc.bef
          (expr {(pc) with bef = ""; aft = ""} e1)
      in
      parser_body {(pc) with bef = b} pa
  | e -> expr pc e ]
;

(* Printers extensions *)

pr_expr_fun_args.val :=
  extfun pr_expr_fun_args.val with
  [ <:expr< fun (strm__ : $_$) -> $_$ >> as e -> ([], e) ];

let lev = find_pr_level "top" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< fun (strm__ : Stream.t _) -> $_$ >> as e ->
      fun curr next pc -> print_parser pc e
  | <:expr< let (strm__ : Stream.t _) = $_$ in $_$ >> as e ->
      fun curr next pc -> print_match_with_parser pc e ];

let lev = find_pr_level "dot" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< Stream.sempty >> ->
      fun curr next pc -> sprintf "%s[: :]%s" pc.bef pc.aft ];
