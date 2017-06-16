(* camlp5r *)
(* pr_schemep.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_macro.cmo";

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
  sprintf "%s\"pr_schemep, not impl: %s; %s\"%s" pc.bef name
    (String.escaped desc) pc.aft
;

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

IFDEF OCAML_VERSION <= OCAML_1_07 THEN
  value with_ind_bef = Pprintf.with_ind_bef;
  value with_ind_bef_aft = Pprintf.with_ind_bef_aft;
  value with_bef_aft = Pprintf.with_bef_aft;
  value with_aft = Pprintf.with_aft;
END;

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

pr_expr_fun_args.val :=
  extfun pr_expr_fun_args.val with
  [ <:expr< fun (strm__ : $_$) -> $_$ >> as e -> ([], e) ];

EXTEND_PRINTER
  pr_expr: LEVEL "top"
    [ [ <:expr< fun (strm__ : Stream.t _) -> $_$ >> as e ->
          print_parser pc e
      | <:expr< let (strm__ : Stream.t _) = $_$ in $_$ >> as e ->
          print_match_with_parser pc e
      | x ->
          not_impl "expr" pc x ] ]
  ;
END;
