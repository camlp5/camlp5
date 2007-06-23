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

value not_impl name ind b x k =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_rp, not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value bar_before elem ind b x k = elem ind (sprintf "%s| " b) x k;
value semi_after elem ind b x k = elem ind b x (sprintf ";%s" k);

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

value expr ind b z k = pr_expr.pr_fun "top" ind b z k;
value patt ind b z k = pr_patt.pr_fun "top" ind b z k;

value sequence_box ind bfun expr el k =
  let s1 = bfun " do {" in
  let s2 =
    vlistl (semi_after expr) expr (shi ind 2) (tab (shi ind 2)) el ""
  in
  let s3 = sprintf "%s%s%s" (tab ind) "}" k in
  sprintf "%s\n%s\n%s" s1 s2 s3
;

value ident_option =
  fun
  [ Some s -> sprintf " %s" s
  | None -> "" ]
;

value stream_patt_comp ind b spc k =
  match spc with
  [ SpTrm _ p None -> patt (shi ind 1) (sprintf "%s`" b) p k
  | SpTrm _ p (Some e) ->
      horiz_vertic
        (fun () ->
           sprintf "%s`%s when %s%s" b (patt (shi ind 1) "" p "")
             (expr ind "" e "") k)
        (fun () ->
           let s1 = patt ind (sprintf "%s`" b) p "" in
           let s2 =
             horiz_vertic
               (fun () ->
                  sprintf "%swhen %s%s" (tab (shi ind 1)) (expr ind "" e "")
                    k)
               (fun () ->
                  let s1 = sprintf "%swhen" (tab (shi ind 1)) in
                  let s2 = expr (shi ind 3) (tab (shi ind 3)) e k in
                  sprintf "%s\n%s" s1 s2)
           in
           sprintf "%s\n%s" s1 s2)
  | SpNtr _ p e ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s = %s%s" b (patt ind "" p "") (expr ind "" e "") k)
        (fun () ->
           let s1 = patt ind b p " =" in
           let s2 = expr (shi ind 2) (tab (shi ind 2)) e k in
           sprintf "%s\n%s" s1 s2)
  | SpLet _ p e ->
      horiz_vertic (fun () -> sprintf "\n")
        (fun () ->
           horiz_vertic
             (fun () ->
                sprintf "%slet %s = %s in%s" b (patt ind "" p "")
                  (expr ind "" e "") k)
             (fun () ->
                let s1 = patt ind (sprintf "%slet " b) p " =" in
                let s2 = expr (shi ind 2) (tab (shi ind 2)) e "" in
                let s3 = sprintf "%sin%s" (tab ind) k in
                sprintf "%s\n%s\n%s" s1 s2 s3))
  | SpStr _ p -> patt ind b p k
  | _ -> not_impl "stream_patt_comp" ind b spc k ]
;

value stream_patt_comp_err ind b (spc, err) k =
  match err with
  [ SpoNoth -> stream_patt_comp ind b spc k
  | SpoBang -> stream_patt_comp ind b spc (sprintf " !%s" k)
  | SpoQues e ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s ? %s%s" b (stream_patt_comp ind "" spc "")
             (expr ind "" e "") k)
        (fun () ->
           let s1 = stream_patt_comp ind b spc "" in
           let s2 = expr (shi ind 4) (sprintf "%s? " (tab (shi ind 2))) e k in
           sprintf "%s\n%s" s1 s2) ]
;

value spc_kont =
  fun
  [ (SpLet _ _ _, _) -> ""
  | _ -> ";" ]
;

value stream_patt ind b sp k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s" b
         (hlistl (semi_after stream_patt_comp_err) stream_patt_comp_err
            ind "" sp "") k)
    (fun () ->
       let sp = List.map (fun spc -> (spc, spc_kont spc)) sp in
       plist stream_patt_comp_err 0 (shi ind 3) b sp k)
;

value parser_case ind b (sp, po, e) k =
  match sp with
  [ [] ->
      horiz_vertic
        (fun () ->
           sprintf "%s[: :]%s -> %s%s" b (ident_option po) (expr ind "" e "")
             k)
        (fun () ->
           match flatten_sequence e with
           [ Some el ->
               sequence_box ind
                 (fun k -> sprintf "%s[: :]%s ->%s" b (ident_option po) k)
                 expr el k
           | None ->
               let s1 = sprintf "%s[: :]%s ->" b (ident_option po) in
               let s2 = expr (shi ind 2) (tab (shi ind 2)) e k in
               sprintf "%s\n%s" s1 s2 ])
  | _ ->
      horiz_vertic
        (fun () ->
           sprintf "%s[: %s :]%s -> %s%s" b (stream_patt ind "" sp "")
             (ident_option po) (expr ind "" e "") k)
        (fun () ->
           match flatten_sequence e with
           [ Some el ->
               sequence_box ind
                 (fun k ->
                    stream_patt ind (sprintf "%s[: " b) sp
                      (sprintf " :]%s ->%s" (ident_option po) k))
                 expr el k
           | None ->
               let s1 =
                 stream_patt ind (sprintf "%s[: " b) sp
                   (sprintf " :]%s ->" (ident_option po))
               in
               let s2 = expr (shi ind 2) (tab (shi ind 2)) e k in
               sprintf "%s\n%s" s1 s2 ]) ]
;

value parser_case_sh ind b spe k = parser_case (shi ind 2) b spe k;

value parser_body ind b (po, spel) k =
  let s1 = ident_option po in
  let s2o =
    match spel with
    [ [spe] ->
        horiz_vertic
          (fun () ->
             let s =
               sprintf "%s%s %s%s" b s1 (parser_case ind "" spe "") k
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
          let s2 = parser_case (shi ind 2) (tab (shi ind 2)) spe k in
          sprintf "%s%s\n%s" b s1 s2
      | _ ->
          let s2 =
            vlist2 parser_case_sh (bar_before parser_case_sh) ind
              (sprintf "%s[ " (tab ind)) spel ("", sprintf " ]%s" k)
          in
          sprintf "%s%s\n%s" b s1 s2 ] ]
;

value print_parser ind b e k =
  match e with
  [ <:expr< fun (strm__ : Stream.t _) -> $e$ >> ->
      let pa = unparser_body e in
      parser_body ind (sprintf "%sparser" b) pa k
  | e -> expr ind b e k ]
;

value print_match_with_parser ind b e k =
  match e with
  [ <:expr< let (strm__ : Stream.t _) = $e1$ in $e2$ >> ->
      let pa = unparser_body e2 in
      let b = sprintf "%smatch %s with parser" b (expr ind "" e1 "") in
      parser_body ind b pa k
  | e -> expr ind b e k ]
;

(* Printers extensions *)

pr_expr_fun_args.val :=
  extfun pr_expr_fun_args.val with
  [ <:expr< fun (strm__ : $_$) -> $_$ >> as e -> ([], e) ];

let lev = find_pr_level "top" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< fun (strm__ : Stream.t _) -> $_$ >> as e ->
      fun curr next ind b k -> print_parser ind b e k
  | <:expr< let (strm__ : Stream.t _) = $_$ in $_$ >> as e ->
      fun curr next ind b k -> print_match_with_parser ind b e k ];

let lev = find_pr_level "dot" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< Stream.sempty >> ->
      fun curr next ind b k -> sprintf "%s[: :]%s" b k ];
