(* camlp5r *)
(* pr_op.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";

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
  pprintf pc "\"pr_op, not impl: %s; %s\"" name (String.escaped desc)
;

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;

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
    [ (True, e) -> pprintf pc "'%p" expr e
    | (False, e) -> expr pc e ]
  in
  let el = List.map (fun e -> (e, ";")) (get e) in
  if el = [] then pprintf pc "[< >]"
  else pprintf pc "@[<3>[< %p >]@]" (plist elem 0) el
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
      pprintf pc "@[<1>'%p@]" patt p
  | SpTrm _ p <:vala< Some e >> ->
      pprintf pc "'%p@;<1 1>@[when@;%p@]" patt p expr e
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
  | SpoBang -> pprintf pc "%p ?!" stream_patt_comp spc
  | SpoQues e -> pprintf pc "%p@;@[<2>?? %p@]" stream_patt_comp spc expr e ]
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
           else pprintf pc "[< >]%p -> %q" ident_option po expr e "|")
        (fun () ->
           pprintf pc "[< >]%p ->@;%q" ident_option po expr e "|")
  | _ ->
      pprintf pc "[< %p@[ >]%p ->@]@;%q" stream_patt sp ident_option po
        expr e "|" ]
;

value parser_case_sh force_vertic pc spe =
  pprintf pc "@[<2>%p@]" (parser_case force_vertic) spe
;

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value parser_body pc (po, spel) =
  let s2o =
    match spel with
    [ [spe] ->
        horiz_vertic
          (fun () ->
             let s =
               pprintf pc "%p %p" ident_option po (parser_case False) spe
             in
             Some s)
          (fun () -> None)
    | _ -> None ]
  in
  match s2o with
  [ Some s -> s
  | None ->
      match spel with
      [ [] -> pprintf pc " []"
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
          pprintf pc "%p@   %p" ident_option po
            (vlist2 (parser_case_sh force_vertic)
               (bar_before (parser_case_sh force_vertic)))
            spel ] ]
;

value print_parser pc e =
  match e with
  [ <:expr< fun (strm__ : Stream.t _) -> $e$ >> ->
      let (po, spel) = unparser_body e in
      let spel =
        if spel = [] then [([], None, <:expr< raise Stream.Failure >>)]
        else spel
      in
      if List.mem pc.dang ["|"; ";"] then
        pprintf pc "@[<1>(parser%p)@]" parser_body (po, spel)
      else
        pprintf pc "parser%p" parser_body (po, spel)
  | e -> expr pc e ]
;

value print_match_with_parser pc e =
  match e with
  [ <:expr< let (strm__ : Stream.t _) = $e1$ in $e2$ >> ->
      let pa = unparser_body e2 in
      pprintf pc "match %p with parser%p" expr e1 parser_body pa
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
    [ [ <:expr< Stream.sempty >> -> pprintf pc "[< >]" ] ]
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
