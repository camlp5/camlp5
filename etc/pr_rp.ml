(* camlp5r *)
(* pr_rp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";
#load "pa_macro.cmo";

open Parserify;
open Pcaml;
open Pretty;
open Prtools;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      "\"" ^ Obj.magic x ^ "\""
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  pprintf pc "\"pr_rp, not impl: %s; %s\"" name (String.escaped desc)
;

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;

IFDEF OCAML_VERSION <= OCAML_1_07 THEN
  value with_ind = Pprintf.with_ind;
  value with_bef_aft = Pprintf.with_bef_aft;
END;

value bar_before elem pc x = pprintf pc "| %p" elem x;
value semi_after elem pc x = pprintf pc "%p;" elem x;

value loc = Ploc.dummy;

(* Streams *)

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
    [ (True, e) -> pprintf pc "`%p" expr e
    | (False, e) -> expr pc e ]
  in
  let el = List.map (fun e -> (e, ";")) (get e) in
  if el = [] then pprintf pc "[: :]"
  else pprintf pc "@[<3>[: %p :]@]" (plist elem 0) el
;

(* Parsers *)

value ident_option pc =
  fun
  [ Some s -> pprintf pc " %s" s
  | None -> pprintf pc "" ]
;

value stream_patt_comp pc spc =
  match spc with
  [ SpTrm _ p <:vala< None >> ->
      pprintf pc "@[<1>`%p@]" patt p
  | SpTrm _ p <:vala< Some e >> ->
      pprintf pc "`%p@;<1 1>@[when@;%p@]" patt p expr e
  | SpNtr _ p e ->
      pprintf pc "%p =@;%p" patt p expr e
  | SpLet _ p e ->
      horiz_vertic (fun () -> sprintf "\n")
        (fun () -> pprintf pc "@[<a>let %p =@;%p@ in@]" patt p expr e)
  | SpStr _ p ->
      patt pc p
  | _ ->
      not_impl "stream_patt_comp" pc spc ]
;

value stream_patt_comp_err pc (spc, err) =
  match err with
  [ SpoNoth -> stream_patt_comp pc spc
  | SpoBang -> pprintf pc "%p !" stream_patt_comp spc
  | SpoQues e -> pprintf pc "%p@;@[<2>? %p@]" stream_patt_comp spc expr e ]
;

value spc_kont =
  fun
  [ (SpLet _ _ _, _) -> ""
  | _ -> ";" ]
;

value stream_patt pc sp =
  let sp = List.map (fun spc -> (spc, spc_kont spc)) sp in
  pprintf pc "@[<3>%p@]" (plist stream_patt_comp_err 0) sp
;

value parser_case force_vertic pc (sp, po, e) =
  match sp with
  [ [] ->
      horiz_vertic
        (fun () ->
           if force_vertic then sprintf "\n"
           else pprintf pc "[: :]%p -> %p" ident_option po expr e)
        (fun () ->
           match Pr_r.flatten_sequence e with
           [ Some se ->
               Pr_r.sequence_box
                 (fun pc () -> pprintf pc "[: :]%p -> " ident_option po)
                 pc se
           | None ->
               pprintf pc "[: :]%p ->@;%p" ident_option po expr e ])
  | _ ->
      horiz_vertic
        (fun () ->
           if force_vertic then sprintf "\n"
           else
             pprintf pc "[: %p :]%p -> %p" stream_patt sp ident_option po
               expr e)
        (fun () ->
           match Pr_r.flatten_sequence e with
           [ Some se ->
               Pr_r.sequence_box
                 (fun pc () ->
                    pprintf pc "[: %p :]%p -> " stream_patt sp ident_option
                      po)
                    pc se
           | None ->
               pprintf pc "[: %p :]%s ->@;%p" stream_patt sp
                 (ident_option {(pc) with bef = ""; aft = ""} po)
                 expr e ]) ]
;

value parser_case_sh force_vertic pc spe =
  parser_case force_vertic {(pc) with ind = pc.ind + 2} spe
;

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value parser_body pc (po, spel) =
  match spel with
  [ [] -> pprintf pc "%p []" ident_option po
  | [spe] -> pprintf pc "%p@;%p" ident_option po (parser_case False) spe
  | _ ->
      let force_vertic =
        if flag_equilibrate_cases.val then
          let has_vertic =
            List.exists
              (fun spe ->
                 horiz_vertic
                   (fun () ->
                      let _ : string =
                        bar_before (parser_case_sh False) pc spe
                      in
                      False)
                   (fun () -> True))
              spel
          in
          has_vertic
        else False
      in
      pprintf pc "%p@ [ %p ]" ident_option po
        (vlist2 (parser_case_sh force_vertic)
           (bar_before (parser_case_sh force_vertic)))
        spel ]
;

(**)
value err =
  fun
  [ <:expr< "" >> -> SpoNoth
  | e -> SpoQues e ]
;

value rec unstream_pattern_kont ge =
  match ge with
  [ <:expr<
      match Stream.peek strm__ with
      [ Some $p1$ → do { Stream.junk strm__; $e1$ }
      | _ → raise (Stream.Error $e2$) ]
    >> →
      let (sp, epo, e) = unstream_pattern_kont e1 in
      let sp = [(SpTrm loc p1 <:vala< None >>, err e2) :: sp] in
      (sp, epo, e)
  | <:expr<
      match try Some $f$ with [ Stream.Failure -> None ] with
      [ Some $p1$ -> $e1$
      | _ -> raise (Stream.Error $e2$) ]
    >> ->
      let f =
        match f with
        [ <:expr< $f$ strm__ >> -> f
        | _ -> <:expr< fun (strm__ : Stream.t _) -> $f$ >> ]
      in
      let (sp, epo, e) = unstream_pattern_kont e1 in
      let sp =[(SpNtr loc p1 f, err e2) :: sp] in
      (sp, epo, e)
  | <:expr<
      match try Some ($f$ strm__) with [ Stream.Failure → None ] with
      [ Some $p1$ → $e1$
      | _ → raise Stream.Failure ]
    >> →
      let p1_eq_e1 =
        match (p1, e1) with
        [ (<:patt< $lid:s1$ >>, <:expr< $lid:s2$ >>) → s1 = s2
        | _ → False ]
      in
      if p1_eq_e1 then
        ([(SpNtr loc <:patt< a >> f, SpoBang)], None, <:expr< a >>)
      else
        let (sp, epo, e) = unstream_pattern_kont e1 in
        ([(SpNtr loc p1 f, SpoBang) :: sp], epo, e)
  | <:expr<
      match try Some $e1$ with [ Stream.Failure → None ] with
      [ Some $p1$ → $e2$
      | _ → raise Stream.Failure ]
    >> →
      let f = <:expr< fun (strm__ : Stream.t _) -> $e1$ >> in
      let (sp, epo, e) = unstream_pattern_kont e2 in
      ([(SpNtr loc p1 f, SpoBang) :: sp], epo, e)
  | e ->
      ([], None, e) ]
;

value rec unparser_cases_list ge =
  match ge with
  [ <:expr<
      match Stream.peek strm__ with
      [ Some $p1$ → do { Stream.junk strm__; $e1$ }
      | _ → $e2$ ]
    >> →
      let spe =
        let (sp, epo, e) = unstream_pattern_kont e1 in
        let sp = [(SpTrm loc p1 <:vala< None >>, SpoNoth) :: sp] in
        (sp, epo, e)
      in
      let spel = unparser_cases_list e2 in
      [spe :: spel]
  | <:expr<
      match try Some ($f$ strm__) with [ Stream.Failure → None ] with
      [ Some $p1$ → $e1$
      | _ → $e2$ ]
    >> →
      let spe =
        let (sp, epo, e) = unstream_pattern_kont e1 in
        let sp = [(SpNtr loc p1 f, SpoNoth) :: sp] in
        (sp, epo, e)
      in
      let spel = unparser_cases_list e2 in
      [spe :: spel]
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
    | _ ->
        (None, e) ]
  in
  let spel = unparser_cases_list e in
  (po, spel)
;
(**)

value print_parser pc e =
  match e with
  [ <:expr< fun (strm__ : Stream.t _) -> $e$ >> ->
      let pa = unparser_body e in
      pprintf pc "parser%p" parser_body pa
  | e -> expr pc e ]
;

value print_match_with_parser pc e =
  match e with
  [ <:expr< let ($_$ : Stream.t _) = $e1$ in $e2$ >> ->
      let pa = unparser_body e2 in
      pprintf pc "@[match %p with parser@]%p" expr e1 parser_body pa
  | <:expr<
      match Stream.peek strm__ with
      [ Some $_$ → do { Stream.junk strm__; $_$ }
      | _ → $_$ ]
    >> as e →
      let pa = unparser_body e in
      pprintf pc "@[match strm__ with parser@]%p" parser_body pa
  | e ->
      expr pc e ]
;

(* Printers extensions *)

pr_expr_fun_args.val :=
  extfun pr_expr_fun_args.val with
  [ <:expr< fun (strm__ : $_$) -> $_$ >> as e -> ([], e) ];

EXTEND_PRINTER
  pr_expr: LEVEL "top"
    [ [ <:expr< fun (strm__ : Stream.t _) -> $_$ >> as e ->
          print_parser pc e
      | <:expr< let ($_$ : Stream.t _) = $_$ in $_$ >> as e ->
          print_match_with_parser pc e
      | <:expr<
          match Stream.peek strm__ with
          [ Some $_$ → do { Stream.junk strm__; $_$ }
          | _ → $_$ ]
        >> as e →
          print_match_with_parser pc e ] ]
  ;
  pr_expr: LEVEL "apply"
    [ [ <:expr< Stream.iapp $_$ $_$ >> | <:expr< Stream.icons $_$ $_$ >> |
        <:expr< Stream.ising $_$ >> |
        <:expr< Stream.lapp (fun _ -> $_$) $_$ >> |
        <:expr< Stream.lcons (fun _ -> $_$) $_$ >> |
        <:expr< Stream.lsing (fun _ -> $_$) >> | <:expr< Stream.sempty >> |
        <:expr< Stream.slazy $_$ >> as e ->
          stream pc e ] ]
  ;
  pr_expr: LEVEL "dot"
    [ [ <:expr< Stream.sempty >> -> pprintf pc "[: :]" ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< Stream.iapp $_$ $_$ >> | <:expr< Stream.icons $_$ $_$ >> |
        <:expr< Stream.ising $_$ >> |
        <:expr< Stream.lapp (fun _ -> $_$) $_$ >> |
        <:expr< Stream.lcons (fun _ -> $_$) $_$ >> |
        <:expr< Stream.lsing (fun _ -> $_$) >> | <:expr< Stream.sempty >> |
        <:expr< Stream.slazy $_$ >> as e ->
          stream pc e ] ]
  ;
END;
