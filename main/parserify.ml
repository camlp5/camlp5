(* camlp5r *)
(* parserify.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "q_MLast.cmo";

(* Heuristic to rebuild parsers and streams from the AST *)

open Pretty;
open Prtools;
open Versdep;

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and MLast.v (option MLast.expr)
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

(* Rebuilding syntax tree *)

value loc = Ploc.dummy;

value rec handle_failure e =
  match e with
  [ <:expr< match $e$ with [ $list:pel$ ] >> ->
      handle_failure e &&
      List.for_all
        (fun
         [ (p, <:vala< None >>, e) -> handle_failure e
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
  | <:expr< let $flag:_$ $list:pel$ in $e$ >> -> contains_strm__ e
  | <:expr< try $e$ with [ $list:pel$ ] >> -> contains_strm__ e
  | <:expr< match $e$ with [ $list:pel$ ] >> -> contains_strm__ e
  | _ -> False ]
;

value err =
  fun
  [ <:expr< "" >> -> SpoNoth
  | e -> SpoQues e ]
;

value rec simpl =
  fun
  [ <:expr<
      match try Some $f$ with [ Stream.Failure -> None ] with
      [ Some $lid:s1$ -> $lid:s2$
      | _ -> raise Stream.Failure ]
    >> as e ->
      if s1 = s2 then f else e
  | <:expr< match $e$ with [ Some $p1$ → $e1$ | _ → $e2$ ] >> →
      <:expr< match $e$ with [ Some $p1$ → $e1$ | _ → $simpl e2$ ] >>
  | e →
      e ]
;

value rec unstream_pattern_kont =
  fun
  [ <:expr<
      let $p$ =
        try $f$ with [ Stream.Failure -> raise (Stream.Error $e2$) ]
      in
      $e$
    >> |
    <:expr<
      match try Some $f$ with [ Stream.Failure -> None ] with
      [ Some $p$ -> $e$
      | _ -> raise (Stream.Error $e2$) ]
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
  | <:expr<
      match try Some ($f$ strm__) with [ Stream.Failure → None ] with
      [ Some $lid:s1$ → $lid:s2$
      | _ → raise Stream.Failure ]
    >> as e →
      if s1 = s2 then
        ([(SpNtr loc <:patt< a >> f, SpoBang)], None, <:expr< a >>)
      else
        ([], None, e)
  | <:expr<
      match try Some $e1$ with [ Stream.Failure → None ] with
      [ Some $lid:s$ → $e2$
      | _ → raise Stream.Failure ]
    >> →
      let e = <:expr< let $lid:s$ = $e1$ in $e2$ >> in
      unstream_pattern_kont e
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
      let sp = [(SpTrm loc p <:vala< None >>, err e2) :: sp] in
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
  | <:expr< let $lid:p$ = Stream.count strm__ in $e$ >> ->
      [([], Some p, e)]
  | <:expr< let $p$ = $f$ strm__ in $e$ >> ->
      let (sp, epo, e) = unstream_pattern_kont e in
      [([(SpNtr loc p f, SpoNoth) :: sp], epo, e)]
  | <:expr< let $p$ = strm__ in $e$ >> ->
      let (sp, epo, e) = unstream_pattern_kont e in
      [([(SpStr loc p, SpoNoth) :: sp], epo, e)]
  | <:expr< match Stream.peek strm__ with [ $list:pel$ ] >> as ge ->
      loop [] pel where rec loop rev_spel =
        fun
        [ [(<:patt< _ >>, <:vala< None >>, e)] ->
            list_rev_append rev_spel (unparser_cases_list e)
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
  | <:expr<
      match try Some $f$ with [ Stream.Failure -> None ] with
      [ Some $p1$ -> $e1$
      | _ -> $e2$ ]
    >> ->
      let e =
        <:expr<
          match try Some $simpl f$ with [ Stream.Failure -> None ] with
          [ Some $p1$ -> $simpl e1$
          | _ -> $simpl e2$ ]
        >>
      in
      [([], None, e)]
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
