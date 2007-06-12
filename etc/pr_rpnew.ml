(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

(* Heuristic to rebuild parsers and streams from the AST *)

open Pcaml.NewPrinter;
open Sformat;

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and option MLast.expr
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpLhd of MLast.loc and list (list MLast.patt)
  | SpStr of MLast.loc and MLast.patt ]
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

(* General purpose printing functions *)

value zc = {ind = 0};
value shi ctx sh = {ind = ctx.ind + sh};
value tab ctx = String.make ctx.ind ' ';

(* horizontal list with different function for the last element *)
value rec hlistl elem eleml ctx b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> eleml ctx b x k
  | [x :: xl] ->
      sprintf "%s %s" (elem ctx b x "") (hlistl elem eleml ctx "" xl k) ]
;

(* vertical list with different function from 2nd element on *)
value rec vlist2 elem elem2 ctx b xl k0 k =
  match xl with
  [ [] -> invalid_arg "vlist2"
  | [x] -> elem ctx b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ctx b x k0)
        (vlist2 elem2 elem2 ctx (tab ctx) xl k0 k) ]
;

value rise_string ctx sh b s =
  (* hack for "plistl" (below): if s is a "string" (i.e. starting with
     double-quote) which contains newlines, attempt to concat its first
     line in the previous line, and, instead of displaying this:
              eprintf
                "\
           hello, world"
     displays that:
              eprintf "\
           hello, world"
     what "saves" one line.
   *)
  let ind = ctx.ind in
  if String.length s > ind + sh && s.[ind+sh] = '"' then
    match try Some (String.index s '\n') with [ Not_found -> None ] with
    [ Some i ->
        let t = String.sub s (ind + sh) (String.length s - ind - sh) in
        let i = i - ind - sh in
        match
          horiz_vertic (fun () -> Some (sprintf "%s %s" b (String.sub t 0 i)))
            (fun () -> None)
        with
        [ Some b -> (b, String.sub t (i + 1) (String.length t - i - 1))
        | None -> (b, s) ]
    | None -> (b, s) ]
  else (b, s)
;

(* paragraph list with a different function for the last element;
   the list elements are pairs where second elements are separators
   (the last separator is ignored) *)
value rec plistl elem eleml ctx sh b xl k =
  let (s1, s2o) = plistl_two_parts elem eleml ctx sh b xl k in
  match s2o with
  [ Some s2 -> sprintf "%s\n%s" s1 s2
  | None -> s1 ]
and plistl_two_parts elem eleml ctx sh b xl k =
  match xl with
  [ [] -> assert False
  | [(x, _)] -> (eleml ctx b x k, None)
  | [(x, sep) :: xl] ->
      let s =
        horiz_vertic (fun () -> Some (elem ctx b x sep)) (fun () -> None)
      in
      match s with
      [ Some b -> (plistl_kont_same_line elem eleml ctx sh b xl k, None)
      | None ->
          let s1 = elem ctx b x sep in
          let s2 = plistl elem eleml (shi ctx sh) 0 (tab (shi ctx sh)) xl k in
          (s1, Some s2) ] ]
and plistl_kont_same_line elem eleml ctx sh b xl k =
  match xl with
  [ [] -> assert False
  | [(x, _)] ->
      horiz_vertic (fun () -> eleml ctx (sprintf "%s " b) x k)
        (fun () ->
           let s = eleml (shi ctx sh) (tab (shi ctx sh)) x k in
           let (b, s) = rise_string ctx sh b s in
           sprintf "%s\n%s" b s)
  | [(x, sep) :: xl] ->
      let s =
        horiz_vertic (fun () -> Some (elem ctx (sprintf "%s " b) x sep))
          (fun () -> None)
      in
      match s with
      [ Some b -> plistl_kont_same_line elem eleml ctx sh b xl k
      | None ->
          let (s1, s2o) =
            plistl_two_parts elem eleml (shi ctx sh) 0 (tab (shi ctx sh))
              [(x, sep) :: xl] k
          in
          match s2o with
          [ Some s2 ->
              let (b, s1) = rise_string ctx sh b s1 in
              sprintf "%s\n%s\n%s" b s1 s2
          | None -> sprintf "%s\n%s" b s1 ] ] ]
;

(* paragraph list *)
value plist elem ctx sh b xl k = plistl elem elem ctx sh b xl k;

value bar_before elem ctx b x k = elem ctx (sprintf "%s| " b) x k;
value semi_after elem ctx b x k = elem ctx b x (sprintf ";%s" k);

(* Rebuilding syntax tree *)

value loc = Token.dummy_loc;

value handle_failure _ = False;

value rec handle_failure e =
  match e with
  [ <:expr< try $te$ with [ Stream.Failure -> $e$] >> -> handle_failure e
  | <:expr< raise $e$ >> ->
      match e with
      [ <:expr< Stream.Failure >> -> False
      | _ -> True ]
  | _ -> False ]
;

value rec unstream_pattern_kont =
  fun
  [ <:expr<
      let $p$ =
        try $f$ with [ Stream.Failure -> raise (Stream.Error $err$) ]
      in
      $e$
    >> ->
      let err =
        match err with
        [ <:expr< "" >> -> None
        | e -> Some (Some e) ]
      in
      let f =
        match f with
        [ <:expr< $f$ strm__ >> -> f
        | _ -> <:expr< fun (strm__ : Stream.t _) -> $f$ >> ]
      in
      let (sp, epo, e) = unstream_pattern_kont e in
      ([(SpNtr loc p f, err) :: sp], epo, e)
  | <:expr< let $lid:p$ = Stream.count strm__ in $e$ >> ->
      ([], Some p, e)
  | <:expr< let $p$ = $e1$ in $e2$ >> ->
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
  | <:expr< $f$ strm__ >> ->
      ([(SpNtr loc <:patt< a >> f, Some None)], None, <:expr< a >>)
  | e -> ([], None, e) ]
;

value rec unparser_cases_list =
  fun
  [ <:expr<
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
  | <:expr<
      match Stream.peek strm__ with
      [ Some $p$ -> do { Stream.junk strm__; $e1$ }
      | _ -> $e2$ ]
    >> ->
      let spe =
        let (sp, epo, e) = unstream_pattern_kont e1 in
        let sp = [(SpTrm loc p None, None) :: sp] in
        (sp, epo, e)
      in
      let spel = unparser_cases_list e2 in
      [spe :: spel]
  | <:expr<
      let $p$ = try $f$ strm__ with [ Stream.Failure -> raise $e2$ ] in $e1$
    >> ->
      let spe1 = ([(SpNtr loc p f, None)], None, e1) in
      let spe2 = ([], None, <:expr< raise $e2$ >>) in
      [spe1; spe2]
  | <:expr< let $p$ = $f$ strm__ in $e$ >> ->
      let (sp, epo, e) = unstream_pattern_kont e in
      [([(SpNtr loc p f, None) :: sp], epo, e)]
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

value ident_option =
  fun
  [ Some s -> sprintf " %s" s
  | None -> "" ]
;

value stream_patt_comp ctx b spc k =
  match spc with
  [ SpTrm _ p None -> patt (shi ctx 1) (sprintf "%s`" b) p k
  | SpNtr _ p e ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s = %s%s" b (patt zc "" p "") (expr zc "" e "") k)
        (fun () ->
           let s1 = patt ctx b p " =" in
           let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
           sprintf "%s\n%s" s1 s2)
  | _ -> not_impl "stream_patt_comp" ctx b spc k ]
;

value stream_patt_comp_err ctx b (spc, err) k =
  let k =
    match err with
    [ None -> k
    | Some None -> sprintf " !%s" k
    | Some (Some e) -> sprintf " ? %s%s" (expr zc "" e "") k ]
  in
  stream_patt_comp ctx b spc k
;

value stream_patt ctx b sp k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s" b
         (hlistl (semi_after stream_patt_comp_err) stream_patt_comp_err
            zc "" sp "") k)
    (fun () ->
       let sp = List.map (fun spc -> (spc, ";")) sp in
       plist stream_patt_comp_err (shi ctx 3) 0 b sp k)
;

value parser_case ctx b (sp, po, e) k =
  match sp with
  [ [] ->
      horiz_vertic
        (fun () ->
           sprintf "%s[: :]%s -> %s%s" b (ident_option po) (expr zc "" e "")
             k)
        (fun () ->
           let s1 = sprintf "%s[: :]%s ->" b (ident_option po) in
           let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
           sprintf "%s\n%s" s1 s2)
  | _ ->
      horiz_vertic
        (fun () ->
           sprintf "%s[: %s :]%s -> %s%s" b (stream_patt zc "" sp "")
             (ident_option po) (expr zc "" e "") k)
        (fun () ->
           let s1 =
             stream_patt ctx (sprintf "%s[: " b) sp
               (sprintf " :]%s ->" (ident_option po))
           in
           let s2 = expr (shi ctx 2) (tab (shi ctx 2)) e k in
           sprintf "%s\n%s" s1 s2) ]
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
               sprintf "%s%s %s%s" b s1 (parser_case zc "" spe "") k
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
              (sprintf "%s[ " (tab ctx)) spel "" (sprintf " ]%s" k)
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
      let b = sprintf "%smatch %s with parser" b (expr zc "" e1 "") in
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
      fun curr next ctx b k -> print_match_with_parser ctx b e k ]
;
