(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

(* Heuristic to rebuild parsers and streams from the AST *)

open Pretty;
open Pcaml.NewPrinters;
open Prtools;

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and option MLast.expr
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpLhd of MLast.loc and list (list MLast.patt)
  | SpStr of MLast.loc and MLast.patt ]
;

type alt 'a 'b =
  [ Left of 'a
  | Right of 'b ]
;

value not_impl name ctx b x k =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_rp, not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value bar_before elem ctx b x k = elem ctx (sprintf "%s| " b) x k;
value semi_after elem ctx b x k = elem ctx b x (sprintf ";%s" k);

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
  | <:expr< try $e$ with [ $list:pel$ ] >> -> contains_strm__ e
  | <:expr< match $e$ with [ $list:pel$ ] >> -> contains_strm__ e
  | _ -> False ]
;

value err =
  fun
  [ <:expr< "" >> -> None
  | e -> Some (Some e) ]
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
      ([(SpStr loc p, None) :: sp], epo, e)
  | <:expr< let $p$ = $e1$ in $e2$ >> as ge ->
      if contains_strm__ e1 then
        let (f, err) =
          match e1 with
          [ <:expr< $f$ strm__ >> -> (f, Some None)
          | _ ->
              let f = <:expr< fun (strm__ : Stream.t _) -> $e1$ >> in
              let err = if handle_failure e1 then None else Some None in
              (f, err) ]
        in
        let (sp, epo, e) = unstream_pattern_kont e2 in
        ([(SpNtr loc p f, err) :: sp], epo, e)
      else
        ([], None, ge)
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
      let err = if handle_failure ge then None else Some None in
      ([(SpNtr loc <:patt< a >> f, err)], None, <:expr< a >>)
  | <:expr<
      try $f$ strm__ with [ Stream.Failure -> raise (Stream.Error $e$) ]
    >> ->
      ([(SpNtr loc <:patt< a >> f, err e)], None, <:expr< a >>)
  | <:expr< try $f$ with [ Stream.Failure -> raise (Stream.Error $e$) ] >> ->
      let f = <:expr< fun (strm__ : Stream.t _) -> $f$ >> in
      ([(SpNtr loc <:patt< a >> f, err e)], None, <:expr< a >>)
  | <:expr< $f$ strm__ >> ->
      ([(SpNtr loc <:patt< a >> f, Some None)], None, <:expr< a >>)
  | e -> ([], None, e) ]
;

value rec unparser_cases_list =
  fun
  [ <:expr<
      let $p$ = try $f$ strm__ with [ Stream.Failure -> raise $e2$ ] in $e1$
    >> ->
      let spe1 =
        let (sp, epo, e) = unstream_pattern_kont e1 in
        ([(SpNtr loc p f, None) :: sp], epo, e)
      in
      let spe2 = ([], None, <:expr< raise $e2$ >>) in
      [spe1; spe2]
  | <:expr< let $p$ = $f$ strm__ in $e$ >> ->
      let (sp, epo, e) = unstream_pattern_kont e in
      [([(SpNtr loc p f, None) :: sp], epo, e)]
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
              let sp = [(SpTrm loc p eo, None) :: sp] in
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
        let sp = [(SpNtr loc p1 f, None) :: sp] in
        (sp, epo, e)
      in
      let spel = unparser_cases_list e2 in
      [spe :: spel]
  | <:expr< try $f$ strm__ with [ Stream.Failure -> $e$ ] >> ->
      let spe = ([(SpNtr loc <:patt< a >> f, None)], None, <:expr< a >>) in
      let spel = unparser_cases_list e in
      [spe :: spel]
  | <:expr< try Some ($f$ strm__) with [ Stream.Failure -> $e$ ] >> ->
      let spe =
        ([(SpNtr loc <:patt< a >> f, None)], None, <:expr< Some a >>)
      in
      let spel = unparser_cases_list e in
      [spe :: spel]
  | <:expr< try $f$ with [ Stream.Failure -> $e$ ] >> ->
      let f = <:expr< fun (strm__ : Stream.t _) -> $f$ >> in
      let spe = ([(SpNtr loc <:patt< a >> f, None)], None, <:expr< a >>) in
      let spel = unparser_cases_list e in
      [spe :: spel]
  | <:expr< $f$ strm__ >> ->
      let spe = ([(SpNtr loc <:patt< a >> f, None)], None, <:expr< a >>) in
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

value expr ctx b z k = pr_expr.pr_fun "top" ctx b z k;
value patt ctx b z k = pr_patt.pr_fun "top" ctx b z k;

value sequence_box ctx bfun expr el k =
  let s1 = bfun " do {" in
  let s2 =
    vlistl (semi_after expr) expr (shi ctx 2) (tab (shi ctx 2)) el ""
  in
  let s3 = sprintf "%s%s%s" (tab ctx) "}" k in
  sprintf "%s\n%s\n%s" s1 s2 s3
;

value ident_option =
  fun
  [ Some s -> sprintf " %s" s
  | None -> "" ]
;

value stream_patt_comp ctx b spc k =
  match spc with
  [ SpTrm _ p None -> patt (shi ctx 1) (sprintf "%s`" b) p k
  | SpTrm _ p (Some e) ->
      horiz_vertic
        (fun () ->
           sprintf "%s`%s when %s%s" b (patt (shi ctx 1) "" p "")
             (expr ctx "" e "") k)
        (fun () ->
           let s1 = patt ctx (sprintf "%s`" b) p "" in
           let s2 =
             horiz_vertic
               (fun () ->
                  sprintf "%swhen %s%s" (tab (shi ctx 1)) (expr ctx "" e "")
                    k)
               (fun () ->
                  let s1 = sprintf "%swhen" (tab (shi ctx 1)) in
                  let s2 = expr (shi ctx 3) (tab (shi ctx 3)) e k in
                  sprintf "%s\n%s" s1 s2)
           in
           sprintf "%s\n%s" s1 s2)
  | SpNtr _ p e ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s = %s%s" b (patt ctx "" p "") (expr ctx "" e "") k)
        (fun () ->
           let s1 = patt ctx b p " =" in
           let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
           sprintf "%s\n%s" s1 s2)
  | SpStr _ p -> patt ctx b p k
  | _ -> not_impl "stream_patt_comp" ctx b spc k ]
;

value stream_patt_comp_err ctx b (spc, err) k =
  match err with
  [ None -> stream_patt_comp ctx b spc k
  | Some None -> stream_patt_comp ctx b spc (sprintf " !%s" k)
  | Some (Some e) ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s ? %s%s" b (stream_patt_comp ctx "" spc "")
             (expr ctx "" e "") k)
        (fun () ->
           let s1 = stream_patt_comp ctx b spc "" in
           let s2 = expr (shi ctx 4) (sprintf "%s? " (tab (shi ctx 2))) e k in
           sprintf "%s\n%s" s1 s2) ]
;

value stream_patt ctx b sp k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s" b
         (hlistl (semi_after stream_patt_comp_err) stream_patt_comp_err
            ctx "" sp "") k)
    (fun () ->
       let sp = List.map (fun spc -> (spc, ";")) sp in
       plist stream_patt_comp_err 0 (shi ctx 3) b sp k)
;

value parser_case ctx b (sp, po, e) k =
  match sp with
  [ [] ->
      horiz_vertic
        (fun () ->
           sprintf "%s[: :]%s -> %s%s" b (ident_option po) (expr ctx "" e "")
             k)
        (fun () ->
           let s1 = sprintf "%s[: :]%s ->" b (ident_option po) in
           let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
           sprintf "%s\n%s" s1 s2)
  | _ ->
      horiz_vertic
        (fun () ->
           sprintf "%s[: %s :]%s -> %s%s" b (stream_patt ctx "" sp "")
             (ident_option po) (expr ctx "" e "") k)
        (fun () ->
           match flatten_sequence e with
           [ Some el ->
               sequence_box ctx
                 (fun k ->
                    stream_patt ctx (sprintf "%s[: " b) sp
                      (sprintf " :]%s ->%s" (ident_option po) k))
                 expr el k
           | None ->
               let s1 =
                 stream_patt ctx (sprintf "%s[: " b) sp
                   (sprintf " :]%s ->" (ident_option po))
               in
               let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
               sprintf "%s\n%s" s1 s2 ]) ]
;

value parser_case_sh ctx b spe k = parser_case (shi ctx 2) b spe k;

value parser_body ctx b (po, spel) k =
  let s1 = ident_option po in
  let s2o =
    match spel with
    [ [spe] ->
        horiz_vertic
          (fun () ->
             let s =
               sprintf "%s%s %s%s" b s1 (parser_case ctx "" spe "") k
             in
             Some s)
          (fun () -> None)
    | _ -> None ]
  in
  match s2o with
  [ Some s -> s
  | None ->
      match spel with
      [ [] -> sprintf "%s []%s" b k
      | [spe] ->
          let s2 = parser_case (shi ctx 2) (tab (shi ctx 2)) spe k in
          sprintf "%s%s\n%s" b s1 s2
      | _ ->
          let s2 =
            vlist2 parser_case_sh (bar_before parser_case_sh) ctx
              (sprintf "%s[ " (tab ctx)) spel ("", sprintf " ]%s" k)
          in
          sprintf "%s%s\n%s" b s1 s2 ] ]
;

value print_parser ctx b e k =
  match e with
  [ <:expr< fun (strm__ : Stream.t _) -> $e$ >> ->
      let pa = unparser_body e in
      parser_body ctx (sprintf "%sparser" b) pa k
  | e -> expr ctx b e k ]
;

value print_match_with_parser ctx b e k =
  match e with
  [ <:expr< let (strm__ : Stream.t _) = $e1$ in $e2$ >> ->
      let pa = unparser_body e2 in
      let b = sprintf "%smatch %s with parser" b (expr ctx "" e1 "") in
      parser_body ctx b pa k
  | e -> expr ctx b e k ]
;

(* Printers extensions *)

pr_expr_fun_args.val :=
  extfun pr_expr_fun_args.val with
  [ <:expr< fun (strm__ : $_$) -> $_$ >> as e -> ([], e) ];

let lev = find_pr_level "top" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< fun (strm__ : Stream.t _) -> $_$ >> as e ->
      fun curr next ctx b k -> print_parser ctx b e k
  | <:expr< let (strm__ : Stream.t _) = $_$ in $_$ >> as e ->
      fun curr next ctx b k -> print_match_with_parser ctx b e k ];

let lev = find_pr_level "dot" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< Stream.sempty >> ->
      fun curr next ctx b k -> sprintf "%s[: :]%s" b k ];
