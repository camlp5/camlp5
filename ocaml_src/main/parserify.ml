(* camlp5r *)
(* parserify.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "q_MLast.cmo" *)

(* Heuristic to rebuild parsers and streams from the AST *)

open Pretty;;
open Prtools;;
open Versdep;;

type spat_comp =
    SpTrm of MLast.loc * MLast.patt * MLast.expr option MLast.v
  | SpNtr of MLast.loc * MLast.patt * MLast.expr
  | SpLet of MLast.loc * MLast.patt * MLast.expr
  | SpLhd of MLast.loc * MLast.patt list list
  | SpStr of MLast.loc * MLast.patt
;;

type spat_comp_opt =
    SpoNoth
  | SpoBang
  | SpoQues of MLast.expr
;;

(* Rebuilding syntax tree *)

let loc = Ploc.dummy;;

let rec handle_failure e =
  match e with
    MLast.ExMat (_, e, pel) ->
      handle_failure e &&
      List.for_all
        (function
           p, None, e -> handle_failure e
         | _ -> false)
        pel
  | MLast.ExApp (_, MLast.ExLid (_, "raise"), e) ->
      begin match e with
        MLast.ExAcc
          (_, MLast.ExUid (_, "Stream"), MLast.ExUid (_, "Failure")) ->
          false
      | _ -> true
      end
  | MLast.ExTry
      (_, te,
       [MLast.PaAcc
          (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
        None, e]) ->
      handle_failure e
  | MLast.ExApp (_, f, e) ->
      no_raising_failure_fun f && handle_failure f && handle_failure e
  | MLast.ExLid (_, _) | MLast.ExUid (_, _) -> true
  | _ -> false
and no_raising_failure_fun =
  function
    MLast.ExApp (_, x, y) -> no_raising_failure_fun x && handle_failure y
  | MLast.ExUid (_, _) -> true
  | _ -> false
;;

let rec contains_strm__ =
  function
    MLast.ExApp (_, e1, e2) -> contains_strm__ e1 || contains_strm__ e2
  | MLast.ExLid (_, "strm__") -> true
  | MLast.ExLet (_, _, pel, e) -> contains_strm__ e
  | MLast.ExTry (_, e, pel) -> contains_strm__ e
  | MLast.ExMat (_, e, pel) -> contains_strm__ e
  | _ -> false
;;

let err =
  function
    MLast.ExStr (_, "") -> SpoNoth
  | e -> SpoQues e
;;

let rec simpl =
  function
    MLast.ExMat
      (_,
       MLast.ExTry
         (_, MLast.ExApp (_, MLast.ExUid (_, "Some"), f),
          [MLast.PaAcc
             (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
           None, MLast.ExUid (_, "None")]),
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), MLast.PaLid (_, s1)), None,
        MLast.ExLid (_, s2);
        MLast.PaAny _, None,
        MLast.ExApp
          (_, MLast.ExLid (_, "raise"),
           MLast.ExAcc
             (_, MLast.ExUid (_, "Stream"),
              MLast.ExUid (_, "Failure")))]) as e ->
      if s1 = s2 then f else e
  | MLast.ExMat
      (_, e,
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), p1), None, e1;
        MLast.PaAny _, None, e2]) ->
      MLast.ExMat
        (loc, e,
         [MLast.PaApp (loc, MLast.PaUid (loc, "Some"), p1), None, e1;
          MLast.PaAny loc, None, simpl e2])
  | e -> e
;;

let rec unstream_pattern_kont =
  function
    MLast.ExLet
      (_, false,
       [p,
        MLast.ExTry
          (_, f,
           [MLast.PaAcc
              (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
            None,
            MLast.ExApp
              (_, MLast.ExLid (_, "raise"),
               MLast.ExApp
                 (_,
                  MLast.ExAcc
                    (_, MLast.ExUid (_, "Stream"), MLast.ExUid (_, "Error")),
                  e2))])],
       e) ->
      let f =
        match f with
          MLast.ExApp (_, f, MLast.ExLid (_, "strm__")) -> f
        | _ ->
            MLast.ExFun
              (loc,
               [MLast.PaTyc
                  (loc, MLast.PaLid (loc, "strm__"),
                   MLast.TyApp
                     (loc,
                      MLast.TyAcc
                        (loc, MLast.TyUid (loc, "Stream"),
                         MLast.TyLid (loc, "t")),
                      MLast.TyAny loc)),
                None, f])
      in
      let (sp, epo, e) = unstream_pattern_kont e in
      (SpNtr (loc, p, f), err e2) :: sp, epo, e
  | MLast.ExMat
      (_,
       MLast.ExTry
         (_, MLast.ExApp (_, MLast.ExUid (_, "Some"), f),
          [MLast.PaAcc
             (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
           None, MLast.ExUid (_, "None")]),
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), p), None, e;
        MLast.PaAny _, None,
        MLast.ExApp
          (_, MLast.ExLid (_, "raise"),
           MLast.ExApp
             (_,
              MLast.ExAcc
                (_, MLast.ExUid (_, "Stream"), MLast.ExUid (_, "Error")),
              e2))]) ->
      let f =
        match f with
          MLast.ExApp (_, f, MLast.ExLid (_, "strm__")) -> f
        | _ ->
            MLast.ExFun
              (loc,
               [MLast.PaTyc
                  (loc, MLast.PaLid (loc, "strm__"),
                   MLast.TyApp
                     (loc,
                      MLast.TyAcc
                        (loc, MLast.TyUid (loc, "Stream"),
                         MLast.TyLid (loc, "t")),
                      MLast.TyAny loc)),
                None, f])
      in
      let (sp, epo, e) = unstream_pattern_kont e in
      (SpNtr (loc, p, f), err e2) :: sp, epo, e
  | MLast.ExLet
      (_, false,
       [MLast.PaLid (_, p),
        MLast.ExApp
          (_,
           MLast.ExAcc
             (_, MLast.ExUid (_, "Stream"), MLast.ExLid (_, "count")),
           MLast.ExLid (_, "strm__"))],
       e) ->
      [], Some p, e
  | MLast.ExLet (_, false, [p, MLast.ExLid (_, "strm__")], e) ->
      let (sp, epo, e) = unstream_pattern_kont e in
      (SpStr (loc, p), SpoNoth) :: sp, epo, e
  | MLast.ExMat
      (_,
       MLast.ExTry
         (_,
          MLast.ExApp
            (_, MLast.ExUid (_, "Some"),
             MLast.ExApp (_, f, MLast.ExLid (_, "strm__"))),
          [MLast.PaAcc
             (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
           None, MLast.ExUid (_, "None")]),
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), MLast.PaLid (_, s1)), None,
        MLast.ExLid (_, s2);
        MLast.PaAny _, None,
        MLast.ExApp
          (_, MLast.ExLid (_, "raise"),
           MLast.ExAcc
             (_, MLast.ExUid (_, "Stream"),
              MLast.ExUid (_, "Failure")))]) as e ->
      if s1 = s2 then
        [SpNtr (loc, MLast.PaLid (loc, "a"), f), SpoBang], None,
        MLast.ExLid (loc, "a")
      else [], None, e
  | MLast.ExMat
      (_,
       MLast.ExTry
         (_, MLast.ExApp (_, MLast.ExUid (_, "Some"), e1),
          [MLast.PaAcc
             (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
           None, MLast.ExUid (_, "None")]),
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), MLast.PaLid (_, s)), None,
        e2;
        MLast.PaAny _, None,
        MLast.ExApp
          (_, MLast.ExLid (_, "raise"),
           MLast.ExAcc
             (_, MLast.ExUid (_, "Stream"), MLast.ExUid (_, "Failure")))]) ->
      let e = MLast.ExLet (loc, false, [MLast.PaLid (loc, s), e1], e2) in
      unstream_pattern_kont e
  | MLast.ExLet (_, false, [p, e1], e2) as ge ->
      if contains_strm__ e1 then
        let (f, err) =
          match e1 with
            MLast.ExApp (_, f, MLast.ExLid (_, "strm__")) -> f, SpoBang
          | _ ->
              let f =
                MLast.ExFun
                  (loc,
                   [MLast.PaTyc
                      (loc, MLast.PaLid (loc, "strm__"),
                       MLast.TyApp
                         (loc,
                          MLast.TyAcc
                            (loc, MLast.TyUid (loc, "Stream"),
                             MLast.TyLid (loc, "t")),
                          MLast.TyAny loc)),
                    None, e1])
              in
              let err = if handle_failure e1 then SpoNoth else SpoBang in
              f, err
        in
        let (sp, epo, e) = unstream_pattern_kont e2 in
        (SpNtr (loc, p, f), err) :: sp, epo, e
      else
        let (sp, epo, e) = unstream_pattern_kont e2 in
        if sp = [] then [], None, ge
        else (SpLet (loc, p, e1), SpoNoth) :: sp, epo, e
  | MLast.ExMat
      (_,
       MLast.ExApp
         (_,
          MLast.ExAcc (_, MLast.ExUid (_, "Stream"), MLast.ExLid (_, "peek")),
          MLast.ExLid (_, "strm__")),
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), p), None,
        MLast.ExSeq
          (_,
           [MLast.ExApp
              (_,
               MLast.ExAcc
                 (_, MLast.ExUid (_, "Stream"), MLast.ExLid (_, "junk")),
               MLast.ExLid (_, "strm__"));
            e]);
        MLast.PaAny _, None,
        MLast.ExApp
          (_, MLast.ExLid (_, "raise"),
           MLast.ExApp
             (_,
              MLast.ExAcc
                (_, MLast.ExUid (_, "Stream"), MLast.ExUid (_, "Error")),
              e2))]) ->
      let (sp, epo, e) = unstream_pattern_kont e in
      let sp = (SpTrm (loc, p, None), err e2) :: sp in sp, epo, e
  | MLast.ExMat
      (_,
       MLast.ExApp
         (_,
          MLast.ExAcc (_, MLast.ExUid (_, "Stream"), MLast.ExLid (_, "peek")),
          MLast.ExLid (_, "strm__")),
       _) |
    MLast.ExMat
      (_,
       MLast.ExTry
         (_,
          MLast.ExApp
            (_, MLast.ExUid (_, "Some"),
             MLast.ExApp (_, _, MLast.ExLid (_, "strm__"))),
          [MLast.PaAcc
             (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
           None, MLast.ExUid (_, "None")]),
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), _), None, _;
        MLast.PaAny _, None, _]) as ge ->
      let f =
        MLast.ExFun
          (loc,
           [MLast.PaTyc
              (loc, MLast.PaLid (loc, "strm__"),
               MLast.TyApp
                 (loc,
                  MLast.TyAcc
                    (loc, MLast.TyUid (loc, "Stream"),
                     MLast.TyLid (loc, "t")),
                  MLast.TyAny loc)),
            None, ge])
      in
      let err = if handle_failure ge then SpoNoth else SpoBang in
      [SpNtr (loc, MLast.PaLid (loc, "a"), f), err], None,
      MLast.ExLid (loc, "a")
  | MLast.ExTry
      (_, MLast.ExApp (_, f, MLast.ExLid (_, "strm__")),
       [MLast.PaAcc
          (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
        None,
        MLast.ExApp
          (_, MLast.ExLid (_, "raise"),
           MLast.ExApp
             (_,
              MLast.ExAcc
                (_, MLast.ExUid (_, "Stream"), MLast.ExUid (_, "Error")),
              e))]) ->
      [SpNtr (loc, MLast.PaLid (loc, "a"), f), err e], None,
      MLast.ExLid (loc, "a")
  | MLast.ExTry
      (_, f,
       [MLast.PaAcc
          (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
        None,
        MLast.ExApp
          (_, MLast.ExLid (_, "raise"),
           MLast.ExApp
             (_,
              MLast.ExAcc
                (_, MLast.ExUid (_, "Stream"), MLast.ExUid (_, "Error")),
              e))]) ->
      let f =
        MLast.ExFun
          (loc,
           [MLast.PaTyc
              (loc, MLast.PaLid (loc, "strm__"),
               MLast.TyApp
                 (loc,
                  MLast.TyAcc
                    (loc, MLast.TyUid (loc, "Stream"),
                     MLast.TyLid (loc, "t")),
                  MLast.TyAny loc)),
            None, f])
      in
      [SpNtr (loc, MLast.PaLid (loc, "a"), f), err e], None,
      MLast.ExLid (loc, "a")
  | MLast.ExApp (_, f, MLast.ExLid (_, "strm__")) ->
      [SpNtr (loc, MLast.PaLid (loc, "a"), f), SpoBang], None,
      MLast.ExLid (loc, "a")
  | e -> [], None, e
;;

let rec unparser_cases_list =
  function
    MLast.ExLet
      (_, false,
       [p,
        MLast.ExTry
          (_, MLast.ExApp (_, f, MLast.ExLid (_, "strm__")),
           [MLast.PaAcc
              (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
            None, MLast.ExApp (_, MLast.ExLid (_, "raise"), e2)])],
       e1) ->
      let spe1 =
        let (sp, epo, e) = unstream_pattern_kont e1 in
        (SpNtr (loc, p, f), SpoNoth) :: sp, epo, e
      in
      let spe2 =
        [], None, MLast.ExApp (loc, MLast.ExLid (loc, "raise"), e2)
      in
      [spe1; spe2]
  | MLast.ExLet
      (_, false,
       [MLast.PaLid (_, p),
        MLast.ExApp
          (_,
           MLast.ExAcc
             (_, MLast.ExUid (_, "Stream"), MLast.ExLid (_, "count")),
           MLast.ExLid (_, "strm__"))],
       e) ->
      [[], Some p, e]
  | MLast.ExLet
      (_, false, [p, MLast.ExApp (_, f, MLast.ExLid (_, "strm__"))], e) ->
      let (sp, epo, e) = unstream_pattern_kont e in
      [(SpNtr (loc, p, f), SpoNoth) :: sp, epo, e]
  | MLast.ExLet (_, false, [p, MLast.ExLid (_, "strm__")], e) ->
      let (sp, epo, e) = unstream_pattern_kont e in
      [(SpStr (loc, p), SpoNoth) :: sp, epo, e]
  | MLast.ExMat
      (_,
       MLast.ExApp
         (_,
          MLast.ExAcc (_, MLast.ExUid (_, "Stream"), MLast.ExLid (_, "peek")),
          MLast.ExLid (_, "strm__")),
       pel) as ge ->
      let rec loop rev_spel =
        function
          [MLast.PaAny _, None, e] ->
            list_rev_append rev_spel (unparser_cases_list e)
        | (MLast.PaApp (_, MLast.PaUid (_, "Some"), p), eo,
           MLast.ExSeq
             (_,
              [MLast.ExApp
                 (_,
                  MLast.ExAcc
                    (_, MLast.ExUid (_, "Stream"), MLast.ExLid (_, "junk")),
                  MLast.ExLid (_, "strm__"));
               e])) ::
          pel ->
            let spe =
              let (sp, epo, e) = unstream_pattern_kont e in
              let sp = (SpTrm (loc, p, eo), SpoNoth) :: sp in sp, epo, e
            in
            loop (spe :: rev_spel) pel
        | _ -> [[], None, ge]
      in
      loop [] pel
  | MLast.ExMat
      (_,
       MLast.ExTry
         (_,
          MLast.ExApp
            (_, MLast.ExUid (_, "Some"),
             MLast.ExApp (_, f, MLast.ExLid (_, "strm__"))),
          [MLast.PaAcc
             (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
           None, MLast.ExUid (_, "None")]),
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), p1), None, e1;
        MLast.PaAny _, None, e2]) ->
      let spe =
        let (sp, epo, e) = unstream_pattern_kont e1 in
        let sp = (SpNtr (loc, p1, f), SpoNoth) :: sp in sp, epo, e
      in
      let spel = unparser_cases_list e2 in spe :: spel
  | MLast.ExMat
      (_,
       MLast.ExTry
         (_, MLast.ExApp (_, MLast.ExUid (_, "Some"), f),
          [MLast.PaAcc
             (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
           None, MLast.ExUid (_, "None")]),
       [MLast.PaApp (_, MLast.PaUid (_, "Some"), p1), None, e1;
        MLast.PaAny _, None, e2]) ->
      let e =
        MLast.ExMat
          (loc,
           MLast.ExTry
             (loc, MLast.ExApp (loc, MLast.ExUid (loc, "Some"), simpl f),
              [MLast.PaAcc
                 (loc, MLast.PaUid (loc, "Stream"),
                  MLast.PaUid (loc, "Failure")),
               None, MLast.ExUid (loc, "None")]),
           [MLast.PaApp (loc, MLast.PaUid (loc, "Some"), p1), None, simpl e1;
            MLast.PaAny loc, None, simpl e2])
      in
      [[], None, e]
  | MLast.ExTry
      (_, MLast.ExApp (_, f, MLast.ExLid (_, "strm__")),
       [MLast.PaAcc
          (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
        None, e]) ->
      let spe =
        [SpNtr (loc, MLast.PaLid (loc, "a"), f), SpoNoth], None,
        MLast.ExLid (loc, "a")
      in
      let spel = unparser_cases_list e in spe :: spel
  | MLast.ExTry
      (_,
       MLast.ExApp
         (_, MLast.ExUid (_, "Some"),
          MLast.ExApp (_, f, MLast.ExLid (_, "strm__"))),
       [MLast.PaAcc
          (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
        None, e]) ->
      let spe =
        [SpNtr (loc, MLast.PaLid (loc, "a"), f), SpoNoth], None,
        MLast.ExApp (loc, MLast.ExUid (loc, "Some"), MLast.ExLid (loc, "a"))
      in
      let spel = unparser_cases_list e in spe :: spel
  | MLast.ExTry
      (_, f,
       [MLast.PaAcc
          (_, MLast.PaUid (_, "Stream"), MLast.PaUid (_, "Failure")),
        None, e]) ->
      let f =
        MLast.ExFun
          (loc,
           [MLast.PaTyc
              (loc, MLast.PaLid (loc, "strm__"),
               MLast.TyApp
                 (loc,
                  MLast.TyAcc
                    (loc, MLast.TyUid (loc, "Stream"),
                     MLast.TyLid (loc, "t")),
                  MLast.TyAny loc)),
            None, f])
      in
      let spe =
        [SpNtr (loc, MLast.PaLid (loc, "a"), f), SpoNoth], None,
        MLast.ExLid (loc, "a")
      in
      let spel = unparser_cases_list e in spe :: spel
  | MLast.ExApp (_, f, MLast.ExLid (_, "strm__")) ->
      let spe =
        [SpNtr (loc, MLast.PaLid (loc, "a"), f), SpoNoth], None,
        MLast.ExLid (loc, "a")
      in
      [spe]
  | MLast.ExApp
      (_, MLast.ExLid (_, "raise"),
       MLast.ExAcc
         (_, MLast.ExUid (_, "Stream"), MLast.ExUid (_, "Failure"))) ->
      []
  | e -> [[], None, e]
;;

let unparser_body e =
  let (po, e) =
    match e with
      MLast.ExLet
        (_, false,
         [MLast.PaLid (_, bp),
          MLast.ExApp
            (_,
             MLast.ExAcc
               (_, MLast.ExUid (_, "Stream"), MLast.ExLid (_, "count")),
             MLast.ExLid (_, strm_n))],
         e) ->
        Some bp, e
    | _ -> None, e
  in
  let spel = unparser_cases_list e in po, spel
;;
