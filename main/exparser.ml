(* camlp5r *)
(* exparser.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "q_MLast.cmo";

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and MLast.v (option MLast.expr)
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpLet of MLast.loc and MLast.patt and MLast.expr
  | SpLhd of MLast.loc and list (list MLast.patt)
  | SpStr of MLast.loc and MLast.patt ]
;
type sexp_comp =
  [ SeTrm of MLast.loc and MLast.expr
  | SeNtr of MLast.loc and MLast.expr ]
;

type spat_comp_opt =
  [ SpoNoth
  | SpoBang
  | SpoQues of MLast.expr ]
;

value strm_n = "strm__";
value peek_fun loc = <:expr< Stream.peek >>;
value junk_fun loc = <:expr< Stream.junk >>;

(* Parsers *)

value rec pattern_eq_expression p e =
  match (p, e) with
  [ (<:patt< $lid:a$ >>, <:expr< $lid:b$ >>) -> a = b
  | (<:patt< $uid:a$ >>, <:expr< $uid:b$ >>) -> a = b
  | (<:patt< $p1$ $p2$ >>, <:expr< $e1$ $e2$ >>) ->
      pattern_eq_expression p1 e1 && pattern_eq_expression p2 e2
  | _ -> False ]
;

value is_raise e =
  match e with
  [ <:expr< raise $_$ >> -> True
  | _ -> False ]
;

value is_raise_failure e =
  match e with
  [ <:expr< raise Stream.Failure >> -> True
  | _ -> False ]
;

value rec handle_failure e =
  match e with
  [ <:expr< try $te$ with [ Stream.Failure -> $e$] >> -> handle_failure e
  | <:expr< match $me$ with [ $list:pel$ ] >> ->
      handle_failure me &&
      List.for_all
        (fun
         [ (_, <:vala< None >>, e) -> handle_failure e
         | _ -> False ])
        pel
  | <:expr< let $list:pel$ in $e$ >> ->
      List.for_all (fun (p, e) -> handle_failure e) pel && handle_failure e
  | <:expr< do { $list:el$ } >> -> List.for_all handle_failure el
  | <:expr< $uid:_$ . $_$ >> | <:expr< $lid:_$ >> | <:expr< $int:_$ >> |
    <:expr< $str:_$ >> | <:expr< $chr:_$ >> | <:expr< fun [ $list:_$ ] >> |
    <:expr< $uid:_$ >> ->
      True
  | <:expr< raise $e$ >> ->
      match e with
      [ <:expr< Stream.Failure >> -> False
      | _ -> True ]
  | <:expr< $f$ $x$ >> ->
      no_raising_failure_fun f && handle_failure f && handle_failure x
  | _ -> False ]
and no_raising_failure_fun =
  fun
  [ <:expr< $uid:_$ >> -> True
  | <:expr< $lid:_$ >> -> False
  | <:expr< Stream.peek >> | <:expr< Stream.junk >> -> True
  | <:expr< $x$ $y$ >> -> no_raising_failure_fun x && handle_failure y
  | _ -> False ]
;

value rec subst v e =
  match e with
  [ <:expr:< $lid:x$ >> ->
      let x = if x = v then strm_n else x in
      <:expr< $lid:x$ >>
  | <:expr< $uid:_$ >> -> e
  | <:expr< $int:_$ >> -> e
  | <:expr< $chr:_$ >> -> e
  | <:expr< $str:_$ >> -> e
  | <:expr< $_$ . $_$ >> -> e
  | <:expr:< let $flag:rf$ $list:pel$ in $e$ >> ->
      <:expr< let $flag:rf$ $list:List.map (subst_pe v) pel$ in $subst v e$ >>
  | <:expr:< $e1$ $e2$ >> -> <:expr< $subst v e1$ $subst v e2$ >>
  | <:expr:< ( $list:el$ ) >> -> <:expr< ( $list:List.map (subst v) el$ ) >>
  | _ -> raise Not_found ]
and subst_pe v (p, e) =
  match p with
  [ <:patt< $lid:v'$ >> when v <> v' -> (p, subst v e)
  | _ -> raise Not_found ]
;

value optim = ref True;
Pcaml.add_option "-no-pa-opt" (Arg.Clear optim) "No parsers optimization.";

value rec perhaps_bound s =
  fun
  [ <:expr< ($list:el$) >> -> List.exists (perhaps_bound s) el
  | <:expr< $uid:_$ >> | <:expr< $str:_$ >> -> False
  | _ -> True ]
;

value wildcard_if_not_bound p e =
  match p with
  [ <:patt:< $lid:s$ >> -> if perhaps_bound s e then p else <:patt< _ >>
  | _ -> p ]
;

value stream_pattern_component skont ckont =
  fun
  [ SpTrm loc p wo ->
      <:expr< match $peek_fun loc$ $lid:strm_n$ with
              [ Some $p$ $_opt:wo$ ->
                  do { $junk_fun loc$ $lid:strm_n$; $skont$ }
              | _ -> $ckont$ ] >>
  | SpNtr loc p e ->
      let e =
        match e with
        [ <:expr< fun [ ($lid:v$ : Stream.t _) -> $e$ ] >> when v = strm_n ->
            e
        | _ -> <:expr< $e$ $lid:strm_n$ >> ]
      in
      if optim.val then
        if pattern_eq_expression p skont then
          if is_raise_failure ckont then e
          else if handle_failure e then e
          else <:expr< try $e$ with [ Stream.Failure -> $ckont$ ] >>
        else if is_raise_failure ckont then
          let p = wildcard_if_not_bound p skont in
          <:expr< let $p$ = $e$ in $skont$ >>
        else if is_raise ckont then
          let tst =
            if handle_failure e then e
            else <:expr< try $e$ with [ Stream.Failure -> $ckont$ ] >>
          in
          let p = wildcard_if_not_bound p skont in
          <:expr< let $p$ = $tst$ in $skont$ >>
        else if pattern_eq_expression <:patt< Some $p$ >> skont then
          <:expr< try Some $e$ with [ Stream.Failure -> $ckont$ ] >>
        else
          <:expr< match try Some $e$ with [ Stream.Failure -> None ] with
                  [ Some $p$ -> $skont$
                  | _ -> $ckont$ ] >>
      else
        <:expr< match try Some $e$ with [ Stream.Failure -> None ] with
                [ Some $p$ -> $skont$
                | _ -> $ckont$ ] >>
  | SpLet _ _ _ -> assert False
  | SpLhd loc [pl :: pll] ->
      let mklistpat loc pl =
        List.fold_right (fun p1 p2 -> <:patt< [$p1$ :: $p2$] >>) pl
          <:patt< [] >>
      in
      let len = List.length pl in
      if List.exists (fun pl -> List.length pl <> len) pll then
        Ploc.raise loc
          (Stream.Error "lookahead patterns must be of the same lengths")
      else
        let p =
          let p = mklistpat loc pl in
          let pl = List.map (mklistpat loc) pll in
          List.fold_left (fun p1 p2 -> <:patt< $p1$ | $p2$ >>) p pl
        in
        <:expr< match Stream.npeek $int:string_of_int len$ strm__ with
                [ $p$ -> $skont$
                | _ -> $ckont$ ] >>
  | SpLhd loc [] -> ckont
  | SpStr loc p ->
      try
        match p with
        [ <:patt< $lid:v$ >> -> subst v skont
        | _ -> raise Not_found ]
      with
      [ Not_found -> <:expr< let $p$ = $lid:strm_n$ in $skont$ >> ] ]
;

value rec stream_pattern loc epo e ekont =
  fun
  [ [] ->
      match epo with
      [ Some ep -> <:expr< let $ep$ = Stream.count $lid:strm_n$ in $e$ >>
      | _ -> e ]
  | [(SpLet loc p1 e1, _) :: spcl] ->
      let skont = stream_pattern loc epo e ekont spcl in
      <:expr< let $p1$ = $e1$ in $skont$ >>
  | [(spc, err) :: spcl] ->
      let skont =
        let ekont =
          fun
          [ SpoQues estr -> <:expr< raise (Stream.Error $estr$) >>
          | SpoBang -> <:expr< raise Stream.Failure >>
          | SpoNoth -> <:expr< raise (Stream.Error "") >> ]
        in
        stream_pattern loc epo e ekont spcl
      in
      let ckont = ekont err in
      stream_pattern_component skont ckont spc ]
;

value stream_patterns_term loc ekont tspel =
  let pel =
    List.map
      (fun (p, w, loc, spcl, epo, e) ->
         let p = <:patt< Some $p$ >> in
         let e =
           let ekont =
             fun
             [ SpoQues estr -> <:expr< raise (Stream.Error $estr$) >>
             | SpoBang -> <:expr< raise Stream.Failure >>
             | SpoNoth -> <:expr< raise (Stream.Error "") >> ]
           in
           let skont = stream_pattern loc epo e ekont spcl in
           <:expr< do { $junk_fun loc$ $lid:strm_n$; $skont$ } >>
         in
         (p, w, e))
      tspel
  in
  let pel = pel @ [(<:patt< _ >>, <:vala< None >>, ekont ())] in
  <:expr< match $peek_fun loc$ $lid:strm_n$ with [ $list:pel$ ] >>
;

value rec group_terms =
  fun
  [ [([(SpTrm loc p w, SpoNoth) :: spcl], epo, e) :: spel] ->
      let (tspel, spel) = group_terms spel in
      ([(p, w, loc, spcl, epo, e) :: tspel], spel)
  | spel -> ([], spel) ]
;

value rec parser_cases loc =
  fun
  [ [] -> <:expr< raise Stream.Failure >>
  | spel ->
      if optim.val then
        match group_terms spel with
        [ ([], [(spcl, epo, e) :: spel]) ->
            stream_pattern loc epo e (fun _ -> parser_cases loc spel) spcl
        | (tspel, spel) ->
            stream_patterns_term loc (fun _ -> parser_cases loc spel) tspel ]
      else
        match spel with
        [ [(spcl, epo, e) :: spel] ->
            stream_pattern loc epo e (fun _ -> parser_cases loc spel) spcl
        | [] -> <:expr< raise Stream.Failure >> ] ]
;

(* optim: left factorization of consecutive rules *)

type tree_node 'a 'b =
  [ Node of 'a and list (tree_node 'a 'b)
  | Leaf of 'b ]
;

value rec map_tree_node f_node f_leaf =
  fun
  [ Node x tl -> f_node x (List.map (map_tree_node f_node f_leaf) tl)
  | Leaf b -> f_leaf b ]
;

value rec insert_in_tree eq (l, a) tl =
  match tl with
  [ [Node n tl1 :: tl2] ->
      match l with
      [ [x :: l] ->
          if eq x n then
            [Node n (insert_in_tree eq (l, a) tl1) :: tl2]
          else
            [List.fold_right (fun x n -> Node x [n]) [x :: l] (Leaf a) :: tl]
      | [] ->
          loop tl where rec loop =
            fun
            [ [Node n tl1 :: tl] -> [Node n tl1 :: loop tl]
            | tl -> [Leaf a :: tl] ] ]
  | _ -> [List.fold_right (fun x n -> Node x [n]) l (Leaf a) :: tl] ]
;

value tree_of_list eq ll = List.fold_right (insert_in_tree eq) ll [];

value rec list_of_tree mk_node mk_leaf tl =
  List.map (map_tree_node mk_node mk_leaf) tl
;

value eq_spat_comp spc1 spc2 =
  match (spc1, spc2) with
  [ (SpTrm _ p1 <:vala< None >>, SpTrm _ p2 <:vala< None >>) ->
      Reloc.eq_patt p1 p2
  | (SpNtr _ p1 e1, SpNtr _ p2 e2) ->
      Reloc.eq_patt p1 p2 && Reloc.eq_expr e1 e2
  | _ -> False ]
;

value eq_spo spco1 spco2 =
  match (spco1, spco2) with
  [ (SpoQues e1, SpoQues e2) -> Reloc.eq_expr e1 e2
  | _ -> spco1 = spco2 ]
;

value eq_spat_comp_opt (spc1, spco1) (spc2, spco2) =
  eq_spat_comp spc1 spc2 && eq_spo spco1 spco2
;

value mk_empty b = ([], b);

value mk_rule x =
  fun
  [ [] -> failwith "mk_rule"
  | [(rl, a)] -> ([x :: rl], a)
  | ll ->
      let loc = Ploc.dummy in
      let e =
        let rl = List.map (fun (rl, (eo, a)) -> (rl, eo, a)) ll in
        let e = parser_cases loc rl in
        let p = <:patt< ($lid:strm_n$ : Stream.t _) >> in
        <:expr< fun $p$ -> $e$ >>
      in
      let spo =
        if List.exists
             (fun (rl, _) ->
                match rl with
                [ [] -> True
                | [(_, SpoBang) :: _] -> True
                | _ -> False ])
             ll
        then
          SpoBang
        else SpoNoth
      in
      ([x; (SpNtr loc <:patt< a >> e, spo)], (None, <:expr< a >>)) ]
;

value left_factorize rl =
  let rl = List.map (fun (rl, eo, a) -> (rl, (eo, a))) rl in
  let t = tree_of_list eq_spat_comp_opt rl in
  let rl = list_of_tree mk_rule mk_empty t in
  List.map (fun (rl, (eo, a)) -> (rl, eo, a)) rl
;

(* Converting into AST *)

value cparser loc bpo pc =
  let pc = left_factorize pc in
  let e = parser_cases loc pc in
  let e =
    let loc = Ploc.with_comment loc "" in
    match bpo with
    [ Some bp -> <:expr< let $bp$ = Stream.count $lid:strm_n$ in $e$ >>
    | None -> e ]
  in
  let p =
    let loc = Ploc.with_comment loc "" in
    <:patt< ($lid:strm_n$ : Stream.t _) >>
  in
  <:expr< fun $p$ -> $e$ >>
;

value rec is_not_bound s =
  fun
  [ <:expr< $uid:_$ >> -> True
  | <:expr< raise Stream.Failure >> -> True
  | _ -> False ]
;

value cparser_match loc me bpo pc =
  let pc = left_factorize pc in
  let iloc = Ploc.with_comment loc "" in
  let pc = parser_cases iloc pc in
  let e =
    let loc = iloc in
    match bpo with
    [ Some bp -> <:expr< let $bp$ = Stream.count $lid:strm_n$ in $pc$ >>
    | None -> pc ]
  in
  match me with
  [ <:expr< $lid:x$ >> when x = strm_n -> e
  | _ ->
      let p =
        let loc = iloc in
        if is_not_bound strm_n e then <:patt< _ >>
        else <:patt< $lid:strm_n$ >>
      in
      <:expr< let ($p$ : Stream.t _) = $me$ in $e$ >> ]
;

(* Streams *)

value rec not_computing =
  fun
  [ <:expr< $lid:_$ >> | <:expr< $uid:_$ >> | <:expr< $int:_$ >> |
    <:expr< $flo:_$ >> | <:expr< $chr:_$ >> | <:expr< $str:_$ >> ->
      True
  | <:expr< $x$ $y$ >> -> is_cons_apply_not_computing x && not_computing y
  | _ -> False ]
and is_cons_apply_not_computing =
  fun
  [ <:expr< $uid:_$ >> -> True
  | <:expr< $lid:_$ >> -> False
  | <:expr< $x$ $y$ >> -> is_cons_apply_not_computing x && not_computing y
  | _ -> False ]
;

value slazy loc e =
  match e with
  [ <:expr< $f$ () >> ->
      match f with
      [ <:expr< $lid:_$ >> -> f
      | _ -> <:expr< fun _ -> $e$ >> ]
  | _ -> <:expr< fun _ -> $e$ >> ]
;

value rec cstream gloc =
  fun
  [ [] ->
      let loc = gloc in
      <:expr< Stream.sempty >>
  | [SeTrm loc e] ->
      if not_computing e then <:expr< Stream.ising $e$ >>
      else <:expr< Stream.lsing $slazy loc e$ >>
  | [SeTrm loc e :: secl] ->
      if not_computing e then <:expr< Stream.icons $e$ $cstream gloc secl$ >>
      else <:expr< Stream.lcons $slazy loc e$ $cstream gloc secl$ >>
  | [SeNtr loc e] ->
      if not_computing e then e else <:expr< Stream.slazy $slazy loc e$ >>
  | [SeNtr loc e :: secl] ->
      if not_computing e then <:expr< Stream.iapp $e$ $cstream gloc secl$ >>
      else <:expr< Stream.lapp $slazy loc e$ $cstream gloc secl$ >> ]
;
