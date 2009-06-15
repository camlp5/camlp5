(* camlp5r pa_extend.cmo q_MLast.cmo *)
(* $Id: pa_fstream.ml,v 1.3 2007/11/22 20:21:08 deraugla Exp $ *)

open Pcaml;

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and option MLast.expr
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpStr of MLast.loc and MLast.patt ]
;
type sexp_comp =
  [ SeTrm of MLast.loc and MLast.expr
  | SeNtr of MLast.loc and MLast.expr ]
;

(* parsers *)

value strm_n = "strm__";
value next_fun loc = <:expr< Fstream.next >>;

value rec pattern_eq_expression p e =
  match (p, e) with
  [ (<:patt< $lid:a$ >>, <:expr< $lid:b$ >>) -> a = b
  | (<:patt< $uid:a$ >>, <:expr< $uid:b$ >>) -> a = b
  | (<:patt< $p1$ $p2$ >>, <:expr< $e1$ $e2$ >>) ->
      pattern_eq_expression p1 e1 && pattern_eq_expression p2 e2
  | (<:patt< ($list:pl$) >>, <:expr< ($list:el$) >>) ->
      loop pl el where rec loop pl el =
        match (pl, el) with
        [ ([p :: pl], [e :: el]) -> pattern_eq_expression p e && loop pl el
        | ([], []) -> True
        | _ -> False ]
  | _ -> False ]
;

value stream_pattern_component skont =
  fun
  [ SpTrm loc p wo ->
      let p = <:patt< Some ($p$, $lid:strm_n$) >> in
      if wo = None && pattern_eq_expression p skont then
        <:expr< $next_fun loc$ $lid:strm_n$ >>
      else
        <:expr< match $next_fun loc$ $lid:strm_n$ with
                [ $p$ $opt:wo$ -> $skont$
                | _ -> None ] >>
  | SpNtr loc p e ->
      let p = <:patt< Some ($p$, $lid:strm_n$) >> in
      if pattern_eq_expression p skont then <:expr< $e$ $lid:strm_n$ >>
      else
        <:expr< match $e$ $lid:strm_n$ with
                [ $p$ -> $skont$
                | _ -> None ] >>
  | SpStr loc p ->
      <:expr< let $p$ = $lid:strm_n$ in $skont$ >> ]
;

value rec stream_pattern loc epo e =
  fun
  [ [] ->
      let e =
        match epo with
        [ Some ep -> <:expr< let $ep$ = Fstream.count $lid:strm_n$ in $e$ >>
        | None -> e ]
      in
      <:expr< Some ($e$, $lid:strm_n$) >>
  | [spc :: spcl] ->
      let skont = stream_pattern loc epo e spcl in
      stream_pattern_component skont spc ]
;

value rec parser_cases loc =
  fun
  [ [] -> <:expr< None >>
  | [(spcl, epo, e) :: spel] ->
      match parser_cases loc spel with
      [ <:expr< None >> -> stream_pattern loc epo e spcl
      | pc ->
          <:expr< match $stream_pattern loc epo e spcl$ with
                  [ Some _ as x -> x
                  | None -> $pc$ ] >> ] ]
;

value cparser_match loc me bpo pc =
  let pc = parser_cases loc pc in
  let e =
    match bpo with
    [ Some bp -> <:expr< let $bp$ = Fstream.count $lid:strm_n$ in $pc$ >>
    | None -> pc ]
  in
  <:expr< let ($lid:strm_n$ : Fstream.t _) = $me$ in $e$ >>
;

value cparser loc bpo pc =
  let e = parser_cases loc pc in
  let e =
    match bpo with
    [ Some bp -> <:expr< let $bp$ = Fstream.count $lid:strm_n$ in $e$ >>
    | None -> e ]
  in
  let p = <:patt< ($lid:strm_n$ : Fstream.t _) >> in
  <:expr< fun $p$ -> $e$ >>
;

(* streams *)

value slazy loc x = <:expr< fun () -> $x$ >>;

value rec cstream loc =
  fun
  [ [] -> <:expr< Fstream.nil >>
  | [SeTrm loc e :: sel] ->
      let e2 = cstream loc sel in
      let x = <:expr< Fstream.cons $e$ $e2$ >> in
      <:expr< Fstream.flazy $slazy loc x$ >>
  | [SeNtr loc e] -> e
  | [SeNtr loc e :: sel] ->
      let e2 = cstream loc sel in
      let x = <:expr< Fstream.app $e$ $e2$ >> in
      <:expr< Fstream.flazy $slazy loc x$ >> ]
;

(* backtracking parsers *)

value patt_expr_of_patt p =
  let loc = MLast.loc_of_patt p in
  match p with
  [ <:patt< $lid:x$ >> -> (p, <:expr< $lid:x$ >>)
  | <:patt< $uid:_$ $lid:x$ >> -> (<:patt< $lid:x$ >>, <:expr< $lid:x$ >>)
  | _ -> (<:patt< () >>, <:expr< () >>) ]
;

value bstream_pattern_component =
  fun
  [ SpTrm loc p wo ->
      let (p1, e1) = patt_expr_of_patt p in
      (p1, <:expr< Fstream.b_term (fun [ $p$ -> Some $e1$ | _ -> None ]) >>)
  | SpNtr loc p e ->
      (p, e)
  | SpStr loc p ->
      Ploc.raise loc (Stream.Error "not impl: stream_pattern_component") ]
;

value rec bstream_pattern loc (spcl, epo, e) =
  let rpel = List.rev_map bstream_pattern_component spcl in
  let p =
    match rpel with
    [ [(p, _) :: rpel] ->
        List.fold_left (fun p (p1, _) -> <:patt< ($p1$, $p$) >>) p rpel
    | [] ->
        <:patt< () >> ]
  in
  let e1 =
    match rpel with
    [ [(_, e) :: rpel] ->
        List.fold_left (fun e (_, e1) -> <:expr< Fstream.b_seq $e1$ $e$ >>) e
          rpel
    | [] ->
        <:expr< Fstream.b_nop >> ]
  in
  match epo with
  [ Some p1 -> <:expr< Fstream.b_act_ep $e1$ (fun $p$ $p1$ -> $e$) >>
  | None ->
      match (p, e) with
      [ (<:patt< $lid:s1$ >>, <:expr< $lid:s2$ >>) when s1 = s2 ->
          (* optimization *)
          e1
      | _ ->
          (* normal case *)
          <:expr< Fstream.b_act $e1$ (fun $p$ -> $e$) >> ] ]
;

value bparser_cases loc spel =
  let rel = List.rev_map (bstream_pattern loc) spel in
  let e =
    match rel with
    [ [e :: rel] ->
        List.fold_left (fun e e1 -> <:expr< Fstream.b_or $e1$ $e$ >>) e rel
    | [] -> Ploc.raise loc (Stream.Error "not impl: bparser_cases") ]
  in
  <:expr< $e$ $lid:strm_n$ >>
;

value bparser_match loc me bpo pc =
  let pc = bparser_cases loc pc in
  let e =
    match bpo with
    [ Some bp -> <:expr< let $bp$ = Fstream.count $lid:strm_n$ in $pc$ >>
    | None -> pc ]
  in
  <:expr< let ($lid:strm_n$ : Fstream.t _) = $me$ in $e$ >>
;

value bparser loc bpo pc =
  let e = bparser_cases loc pc in
  let e =
    match bpo with
    [ Some bp -> <:expr< let $bp$ = Fstream.count $lid:strm_n$ in $e$ >>
    | None -> e ]
  in
  let p = <:patt< ($lid:strm_n$ : Fstream.t _) >> in
  <:expr< fun $p$ -> $e$ >>
;

EXTEND
  GLOBAL: expr;
  expr: LEVEL "top"
    [ [ "fparser"; po = OPT ipatt; "["; pcl = LIST0 parser_case SEP "|";
        "]" ->
          <:expr< $cparser loc po pcl$ >>
      | "fparser"; po = OPT ipatt; pc = parser_case ->
          <:expr< $cparser loc po [pc]$ >>
      | "match"; e = SELF; "with"; "fparser"; po = OPT ipatt; "[";
        pcl = LIST0 parser_case SEP "|"; "]" ->
          <:expr< $cparser_match loc e po pcl$ >>
      | "match"; e = SELF; "with"; "fparser"; po = OPT ipatt;
        pc = parser_case ->
          <:expr< $cparser_match loc e po [pc]$ >>
      | "bparser"; po = OPT ipatt; "["; pcl = LIST0 parser_case SEP "|";
        "]" ->
          <:expr< $bparser loc po pcl$ >>
      | "bparser"; po = OPT ipatt; pc = parser_case ->
          <:expr< $bparser loc po [pc]$ >>
      | "match"; e = SELF; "with"; "bparser"; po = OPT ipatt; "[";
        pcl = LIST0 parser_case SEP "|"; "]" ->
          <:expr< $bparser_match loc e po pcl$ >>
      | "match"; e = SELF; "with"; "bparser"; po = OPT ipatt;
        pc = parser_case ->
          <:expr< $bparser_match loc e po [pc]$ >> ] ]
  ;
  parser_case:
    [ [ "[:"; sp = stream_patt; ":]"; po = OPT ipatt; "->"; e = expr ->
          (sp, po, e) ] ]
  ;
  stream_patt:
    [ [ spc = stream_patt_comp -> [spc]
      | spc = stream_patt_comp; ";"; sp = LIST1 stream_patt_comp SEP ";" ->
          [spc :: sp]
      | -> [] ] ]
  ;
  stream_patt_comp:
    [ [ "`"; p = patt; eo = OPT [ "when"; e = expr -> e ] -> SpTrm loc p eo
      | p = patt; "="; e = expr -> SpNtr loc p e
      | p = patt -> SpStr loc p ] ]
  ;
  ipatt:
    [ [ i = LIDENT -> <:patt< $lid:i$ >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "fstream"; "[:"; se = LIST0 stream_expr_comp SEP ";"; ":]" ->
          <:expr< $cstream loc se$ >> ] ]
  ;
  stream_expr_comp:
    [ [ "`"; e = expr -> SeTrm loc e
      | e = expr -> SeNtr loc e ] ]
  ;
END;
