(* camlp5r q_MLast.cmo ./pa_extfun.cmo ./pa_extprint.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

(* Heuristic to rebuild parsers and streams from the AST *)

open Pretty;
open Pcaml;
open Prtools;

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

(*
type alt 'a 'b =
  [ Left of 'a
  | Right of 'b ]
;
*)

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

(** Printing **)

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;

(* Streams *)

(*
value stream pc e =
  let rec get =
    fun
    [ <:expr< Stream.iapp $x$ $y$ >> -> [(False, x) :: get y]
    | <:expr< Stream.icons $x$ $y$ >> -> [(True, x) :: get y]
    | <:expr< Stream.ising $x$ >> -> [(True, x)]
    | <:expr< Stream.lapp (fun _ -> $x$) $y$ >> -> [(False, x) :: get y]
    | <:expr< Stream.lcons (fun _ -> $x$) $y$ >> -> [(True, x) :: get y]
    | <:expr< Stream.lsing (fun _ -> $x$) >> -> [(True, x)]
    | <:expr< Stream.sempty >> -> []
    | <:expr< Stream.slazy (fun _ -> $x$) >> -> [(False, x)]
    | <:expr< Stream.slazy $x$ >> -> [(False, <:expr< $x$ () >>)]
    | e -> [(False, e)] ]
  in
  let elem pc e =
    match e with
    [ (True, e) -> expr {(pc) with bef = sprintf "%s`" pc.bef} e
    | (False, e) -> expr pc e ]
  in
  let el = List.map (fun e -> (e, ";")) (get e) in
  if el = [] then sprintf "%s[: :]%s" pc.bef pc.aft
  else
    plist elem 0
      {(pc) with ind = pc.ind + 3; bef = sprintf "%s[: " pc.bef;
       aft = sprintf " :]%s" pc.aft}
      el
;
*)

(* Parsers *)

value ident_option =
  fun
  [ Some s -> sprintf " %s" s
  | None -> "" ]
;

value stream_patt_comp pc spc =
  match spc with
  [ SpTrm _ p <:vala< None >> ->
      patt
        {(pc) with ind = pc.ind + 1; bef = sprintf "%s(` " pc.bef;
         aft = sprintf ")%s" pc.aft}
        p
  | SpTrm _ p <:vala< Some e >> ->
      horiz_vertic
        (fun () ->
           sprintf "%s(` %s %s)%s" pc.bef
             (patt {(pc) with ind = pc.ind + 1; bef = ""; aft = ""} p)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 =
             patt {(pc) with bef = sprintf "%s(` " pc.bef; aft = ""} p
           in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               e
           in
           sprintf "%s\n%s" s1 s2)
  | SpNtr _ p e ->
      horiz_vertic
        (fun () ->
           sprintf "%s(%s %s)%s" pc.bef
             (patt {(pc) with bef = ""; aft = ""} p)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 = patt {(pc) with bef = sprintf "%s(" pc.bef; aft = ""} p in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               e
           in
           sprintf "%s\n%s" s1 s2)
  | SpLet _ p e ->
      horiz_vertic
        (fun () ->
           sprintf "%s(let %s %s)%s" pc.bef
             (patt {(pc) with bef = ""; aft = ""} p)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 =
             patt {(pc) with bef = sprintf "%s(let " pc.bef; aft = ""} p
           in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               e
           in
           sprintf "%s\n%s" s1 s2)
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

value stream_patt pc sp =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s" pc.bef
         (hlist stream_patt_comp_err {(pc) with bef = ""; aft = ""} sp)
         pc.aft)
    (fun () ->
       let sp = List.map (fun spc -> (spc, "")) sp in
       plist stream_patt_comp_err 0 pc sp)
;

value parser_case force_vertic pc (sp, po, e) =
  match sp with
  [ [] ->
      horiz_vertic
        (fun () ->
           if force_vertic then sprintf "\n"
           else
             sprintf "%s(()%s %s)%s" pc.bef (ident_option po)
               (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 = sprintf "%s(()%s" pc.bef (ident_option po) in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               e
           in
           sprintf "%s\n%s" s1 s2)
  | _ ->
      horiz_vertic
        (fun () ->
           if force_vertic then sprintf "\n"
           else
             sprintf "%s((%s)%s %s)%s" pc.bef
               (stream_patt {(pc) with bef = ""; aft = ""} sp)
               (ident_option po) (expr {(pc) with bef = ""; aft = ""} e)
               pc.aft)
        (fun () ->
           let s1 =
             stream_patt
               {(pc) with ind = pc.ind + 2; bef = sprintf "%s((" pc.bef;
                aft = sprintf ")%s" (ident_option po)}
               sp
           in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               e
           in
           sprintf "%s\n%s" s1 s2) ]
;

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value parser_body pc spel =
  match spel with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [spe] -> parser_case False pc spe
  | _ ->
      let force_vertic =
        if flag_equilibrate_cases.val then
          let has_vertic =
            List.exists
              (fun spe ->
                 horiz_vertic
                   (fun () ->
                      let _ : string = parser_case False pc spe in
                      False)
                   (fun () -> True))
              spel
          in
          has_vertic
        else False
      in
      vlist (parser_case force_vertic) pc spel ]
;

value print_parser pc e =
  match e with
  [ <:expr< fun (strm__ : Stream.t _) -> $e$ >> ->
      let (po, spel) = unparser_body e in
      let pc =
        {(pc) with ind = pc.ind + 1;
         bef = sprintf "%s(parser" pc.bef;
         aft = sprintf ")%s" pc.aft}
      in
      match spel with
      [ [] -> sprintf "%s%s" pc.bef pc.aft
      | _ ->
          match po with
          [ Some s ->
              plistbf 0 pc
                [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
                 (fun pc -> parser_body pc spel, "")]
          | None ->
              plistbf 0 pc [(fun pc -> parser_body pc spel, "")] ] ]
  | e -> expr pc e ]
;

value print_match_with_parser pc e =
  match e with
  [ <:expr< let (strm__ : Stream.t _) = $e1$ in $e2$ >> ->
      let (po, spel) = unparser_body e2 in
      let fl =
        let fl = [(fun pc -> parser_body pc spel, "")] in
        match po with
        [ Some s -> [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "") :: fl]
        | None -> fl ]
      in
      plistbf 0
        {(pc) with ind = pc.ind + 1;
         bef = sprintf "%s(match_with_parser" pc.bef;
         aft = sprintf ")%s" pc.aft}
        [(fun pc -> expr pc e1, "") :: fl]
  | e -> expr pc e ]
;

(* Printers extensions *)

(*
pr_expr_fun_args.val :=
  extfun pr_expr_fun_args.val with
  [ <:expr< fun (strm__ : $_$) -> $_$ >> as e -> ([], e) ];
*)

EXTEND_PRINTER
  pr_expr: LEVEL "top"
    [ [ <:expr< fun (strm__ : Stream.t _) -> $_$ >> as e ->
          print_parser pc e
      | <:expr< let (strm__ : Stream.t _) = $_$ in $_$ >> as e ->
          print_match_with_parser pc e ] ]
  ;
END;
