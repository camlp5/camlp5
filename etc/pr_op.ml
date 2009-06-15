(* camlp5r q_MLast.cmo ./pa_extfun.cmo ./pa_extprint.cmo *)
(* $Id: pr_op.ml,v 1.18 2007/12/14 20:27:26 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Parserify;
open Pcaml;
open Pretty;
open Prtools;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_op, not impl: %s; %s\"%s" pc.bef name (String.escaped desc)
    pc.aft
;

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;

value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;
value semi_after elem pc x = elem {(pc) with aft = sprintf ";%s" pc.aft} x;

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
    [ (True, e) -> expr {(pc) with bef = sprintf "%s'" pc.bef} e
    | (False, e) -> expr pc e ]
  in
  let el = List.map (fun e -> (e, ";")) (get e) in
  if el = [] then sprintf "%s[< >]%s" pc.bef pc.aft
  else
    plist elem 0
      {(pc) with ind = pc.ind + 3; bef = sprintf "%s[< " pc.bef;
       aft = sprintf " >]%s" pc.aft}
      el
;

(* Parsers *)

value ident_option =
  fun
  [ Some s -> sprintf " %s" s
  | None -> "" ]
;

value stream_patt_comp pc spc =
  match spc with
  [ SpTrm _ p <:vala< None >> ->
      patt {(pc) with ind = pc.ind + 1; bef = sprintf "%s'" pc.bef} p
  | SpTrm _ p <:vala< Some e >> ->
      horiz_vertic
        (fun () ->
           sprintf "%s'%s when %s%s" pc.bef
             (patt {(pc) with ind = pc.ind + 1; bef = ""; aft = ""} p)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 = patt {(pc) with bef = sprintf "%s'" pc.bef; aft = ""} p in
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
  | SpoBang -> stream_patt_comp {(pc) with aft = sprintf " ?!%s" pc.aft} spc
  | SpoQues e ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s ?? %s%s" pc.bef
             (stream_patt_comp {(pc) with bef = ""; aft = ""} spc)
             (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
        (fun () ->
           let s1 = stream_patt_comp {(pc) with aft = ""} spc in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 4;
                bef = sprintf "%s?? " (tab (pc.ind + 2))}
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

value parser_case force_vertic pc (sp, po, e) =
  match sp with
  [ [] ->
      horiz_vertic
        (fun () ->
           if force_vertic then sprintf "\n"
           else
             sprintf "%s[< >]%s -> %s%s" pc.bef (ident_option po)
               (expr {(pc) with bef = ""; aft = ""; dang = "|"} e) pc.aft)
        (fun () ->
           let s1 = sprintf "%s[< >]%s ->" pc.bef (ident_option po) in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                dang = "|"}
               e
           in
           sprintf "%s\n%s" s1 s2)
  | _ ->
      horiz_vertic
        (fun () ->
           sprintf "%s[< %s >]%s -> %s%s" pc.bef
             (stream_patt {(pc) with bef = ""; aft = ""} sp) (ident_option po)
             (expr {(pc) with bef = ""; aft = ""; dang = "|"} e) pc.aft)
        (fun () ->
           let s1 =
             stream_patt
               {(pc) with bef = sprintf "%s[< " pc.bef;
                aft = sprintf " >]%s ->" (ident_option po)}
               sp
           in
           let s2 =
             expr
               {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                dang = "|"}
               e
           in
           sprintf "%s\n%s" s1 s2) ]
;

value parser_case_sh force_vertic pc spe =
  parser_case force_vertic {(pc) with ind = pc.ind + 2} spe
;

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value parser_body pc (po, spel) =
  let s1 = ident_option po in
  let s2o =
    match spel with
    [ [spe] ->
        horiz_vertic
          (fun () ->
             let s =
               sprintf "%s%s %s%s" pc.bef s1
                 (parser_case False {(pc) with bef = ""; aft = ""} spe) pc.aft
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
            parser_case False
              {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} spe
          in
          sprintf "%s%s\n%s" pc.bef s1 s2
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
          let s2 =
            vlist2 (parser_case_sh force_vertic)
              (bar_before (parser_case_sh force_vertic))
              {(pc) with bef = sprintf "%s  " (tab pc.ind); aft = pc.aft}
              spel
          in
          sprintf "%s%s\n%s" pc.bef s1 s2 ] ]
;

value print_parser pc e =
  match e with
  [ <:expr< fun (strm__ : Stream.t _) -> $e$ >> ->
      let (po, spel) = unparser_body e in
      let (op_begin, op_end, sh, pc_dang) =
        if List.mem pc.dang ["|"; ";"] then ("(", ")", 1, "")
        else ("", "", 0, pc.dang)
      in
      let spel =
        if spel = [] then [([], None, <:expr< raise Stream.Failure >>)]
        else spel
      in
      parser_body
        {ind = pc.ind + sh; bef = sprintf "%s%sparser" pc.bef op_begin;
         aft = sprintf "%s%s" op_end pc.aft; dang = pc_dang}
        (po, spel)
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

EXTEND_PRINTER
  pr_expr: LEVEL "top"
    [ [ <:expr< fun (strm__ : Stream.t _) -> $_$ >> as e ->
          print_parser pc e
      | <:expr< let (strm__ : Stream.t _) = $_$ in $_$ >> as e ->
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
    [ [ <:expr< Stream.sempty >> -> sprintf "%s[< >]%s" pc.bef pc.aft ] ]
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
