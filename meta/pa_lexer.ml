(* camlp5r *)
(* pa_lexer.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

(* Simplified syntax of parsers of characters streams *)

open Pcaml;
open Exparser;

value var () = "buf";
value empty loc = <:expr< Plexing.Lexbuf.empty >>;
value add_char loc c cl = <:expr< Plexing.Lexbuf.add $c$ $cl$ >>;
value get_buf loc cl = <:expr< Plexing.Lexbuf.get $cl$ >>;

value fresh_c cl =
  let n =
    List.fold_left
      (fun n c ->
         match c with
         [ <:expr< $lid:_$ >> -> n + 1
         | _ -> n ])
      0 cl
  in
  if n = 0 then "c" else "c" ^ string_of_int n
;

value accum_chars loc cl =
  List.fold_right (add_char loc) cl <:expr< $lid:var ()$ >>
;

value conv_rules loc rl =
  List.map
    (fun (sl, cl, a) ->
       let a =
         let b = accum_chars loc cl in
         match a with
         [ Some e -> e
         | None -> b ]
       in
       (List.rev sl, None, a))
    rl
;

value mk_lexer loc rl =
  cparser loc None (conv_rules loc rl)
;

value mk_lexer_match loc e rl =
  cparser_match loc e None (conv_rules loc rl)
;

(* group together consecutive rules just containing one character *)
value isolate_char_patt_list =
  loop [] where rec loop pl =
    fun
    [ [([(SpTrm _ p <:vala< None >>, SpoNoth)], [_], None) :: rl] ->
        let p =
          match p with
          [ <:patt< $chr:_$ >> -> p
          | <:patt< ($p$ as $lid:_$) >> -> p
          | p -> p ]
        in
        loop [p :: pl] rl
    | rl -> (List.rev pl, rl) ]
;

value or_patt_of_patt_list loc =
  fun
  [ [p :: pl] -> List.fold_left (fun p1 p2 -> <:patt< $p1$ | $p2$ >>) p pl
  | [] -> invalid_arg "or_patt_of_patt_list" ]
;

value isolate_char_patt loc rl =
  match isolate_char_patt_list rl with
  [ ([] | [_], _) -> (None, rl)
  | (pl, rl) -> (Some (or_patt_of_patt_list loc pl), rl) ]
;

value make_rules loc rl sl cl errk =
  match isolate_char_patt loc rl with
  [ (Some p, []) ->
      let c = fresh_c cl in
      let s =
        let p = <:patt< ($p$ as $lid:c$) >> in
        (SpTrm loc p <:vala< None >>, errk)
      in
      ([s :: sl], [<:expr< $lid:c$ >> :: cl])
  | x ->
      let rl =
        match x with
        [ (Some p, rl) ->
            let r =
              let p = <:patt< ($p$ as c) >> in
              let e = <:expr< c >> in
              ([(SpTrm loc p <:vala< None >>, SpoNoth)], [e], None)
            in
            [r :: rl]
        | (None, rl) -> rl ]
      in
      let errk =
        match List.rev rl with
        [ [([], _, _) :: _] -> SpoBang
        | _ -> errk ]
      in
      let sl =
        if cl = [] then sl
        else
          let s =
            let b = accum_chars loc cl in
            let e = cparser loc None [([], None, b)] in
            (SpNtr loc <:patt< $lid:var ()$ >> e, SpoBang)
          in
          [s :: sl]
      in
      let s =
        let e = mk_lexer loc rl in
        (SpNtr loc <:patt< $lid:var ()$ >> e, errk)
      in
      ([s :: sl], []) ]
;

value make_any loc norec sl cl errk =
  let (p, cl) =
    if norec then (<:patt< _ >>, cl)
    else
      let c = fresh_c cl in
      (<:patt< $lid:c$ >>, [<:expr< $lid:c$ >> :: cl])
  in
  let s = (SpTrm loc p <:vala< None >>, errk) in
  ([s :: sl], cl)
;

value fold_string_chars f s a =
  loop 0 a where rec loop i a =
    if i = String.length s then a
    else
      let c = Char.escaped s.[i] in
      loop (i + 1) (f c a)
;

value make_char loc c norec sl cl errk =
  let s = (SpTrm loc <:patt< $chr:c$ >> <:vala< None >>, errk) in
  let cl = if norec then cl else [<:expr< $chr:c$ >> :: cl] in
  ([s :: sl], cl)
;

value make_chars loc s norec sl cl errk =
  let s = Plexing.eval_string loc s in
  loop 0 sl cl where rec loop i sl cl =
    if i = String.length s then (sl, cl)
    else
      let c = Versdep.char_escaped s.[i] in
      let (sl, cl) = make_char loc c norec sl cl errk in
      loop (i + 1) sl cl
;

value make_range loc c1 c2 norec sl cl errk =
  let p = <:patt< $chr:c1$ .. $chr:c2$ >> in
  let c = fresh_c cl in
  let s =
    let p = if norec then p else <:patt< ($p$ as $lid:c$) >> in
    (SpTrm loc p <:vala< None >>, errk)
  in
  let cl = if norec then cl else [<:expr< $lid:c$ >> :: cl] in
  ([s :: sl], cl)
;

value make_sub_lexer loc f sl cl errk =
  let s =
    let buf = accum_chars loc cl in
    let e = <:expr< $f$ $buf$ >> in
    let p = <:patt< $lid:var ()$ >> in
    (SpNtr loc p e, errk)
  in
  ([s :: sl], [])
;

value make_lookahd loc pll sl cl errk =
  let s = (SpLhd loc pll, errk) in
  ([s :: sl], cl)
;

value gcl = ref [];

EXTEND
  GLOBAL: expr;
  expr: LIKE "match"
    [ [ "lexer"; rl = rules ->
          let rl =
            match isolate_char_patt loc rl with
            [ (Some p, rl) ->
                let p = <:patt< ($p$ as c) >> in
                let e = <:expr< c >> in
                [([(SpTrm loc p <:vala< None >>, SpoNoth)], [e], None) ::
                 rl]
            | (None, rl) -> rl ]
          in
          <:expr< fun $lid:var ()$ -> $mk_lexer loc rl$ >>
      | "match"; e = SELF; "with"; "lexer"; rl = rules ->
          mk_lexer_match loc e rl ] ]
  ;
  expr: LEVEL "simple"
    [ [ "$"; LIDENT "add"; s = STRING ->
          let s = Plexing.eval_string loc s in
          loop (accum_chars loc gcl.val) 0 where rec loop v i =
            if i = String.length s then v
            else
              let c = Char.escaped s.[i] in
              loop (add_char loc <:expr< $chr:c$ >> v) (i + 1)
      | "$"; LIDENT "add"; e = simple_expr ->
          add_char loc e (accum_chars loc gcl.val)
      | "$"; LIDENT "buf" ->
          get_buf loc (accum_chars loc gcl.val)
      | "$"; LIDENT "empty" ->
          empty loc
      | "$"; LIDENT "pos" ->
          <:expr< Stream.count $lid:strm_n$ >> ] ]
  ;
  rules:
    [ [ "["; rl = LIST0 rule SEP "|"; "]" -> rl ] ]
  ;
  rule:
    [ [ (sl, cl) = symb_list; a = act -> do { gcl.val := []; (sl, cl, a) } ] ]
  ;
  symb_list:
    [ [ (sl, cl) = symbs -> do { gcl.val := cl; (sl, cl) } ] ]
  ;
  symbs:
    [ [ (sl, cl) = SELF; f = symb; kont = err_kont -> f sl cl kont
      | -> ([], []) ] ]
  ;
  symb:
    [ [ "_"; norec = no_rec -> make_any loc norec
      | s = STRING; norec = no_rec -> make_chars loc s norec
      | c = CHAR; norec = no_rec -> make_char loc c norec
      | c = CHAR; "-"; d = CHAR; norec = no_rec -> make_range loc c d norec
      | f = simple_expr -> make_sub_lexer loc f
      | "?="; "["; pll = LIST1 lookahead SEP "|"; "]" -> make_lookahd loc pll
      | rl = rules -> make_rules loc rl ] ]
  ;
  simple_expr:
    [ [ i = LIDENT -> <:expr< $lid:i$ >>
      | c = CHAR -> <:expr< $chr:c$ >>
      | "("; e = expr; ")" -> e ] ]
  ;
  lookahead:
    [ [ pl = LIST1 lookahead_char -> pl
      | s = STRING ->
          let s = Plexing.eval_string loc s in
          List.rev
            (fold_string_chars (fun c pl -> [<:patt< $chr:c$ >> :: pl]) s
               []) ] ]
  ;
  lookahead_char:
    [ [ c = CHAR -> <:patt< $chr:c$ >>
      | c = CHAR; "-"; d = CHAR -> <:patt< $chr:c$..$chr:d$ >>
      | "_" -> <:patt< _ >> ] ]
  ;
  no_rec:
    [ [ "/" -> True
      | -> False ] ]
  ;
  err_kont:
    [ [ "!" -> SpoBang
      | "?"; s = STRING -> SpoQues <:expr< $str:s$ >>
      | "?"; e = simple_expr -> SpoQues e
      | -> SpoNoth ] ]
  ;
  act:
    [ [ "->"; e = expr -> Some e
      | -> None ] ]
  ;
END;
