(* camlp5r *)
(* q_regexp.ml,v *)

(* #load "q_MLast.cmo" *)

open Quotation;;
open Token_regexps;;

let export_dfa (init, initre, states) =
  let open PatternBaseToken in
  let loc = Ploc.dummy in
  let statename i = Printf.sprintf "q%04d" i in
  let token_pattern =
    function
      CLS s ->
        MLast.PaApp
          (loc, MLast.PaLong (loc, MLast.LiUid (loc, "Some"), []),
           MLast.PaApp
             (loc, MLast.PaLong (loc, MLast.LiUid (loc, "CLS"), []),
              MLast.PaStr (loc, s)))
    | SPCL s ->
        MLast.PaApp
          (loc, MLast.PaLong (loc, MLast.LiUid (loc, "Some"), []),
           MLast.PaApp
             (loc, MLast.PaLong (loc, MLast.LiUid (loc, "SPCL"), []),
              MLast.PaStr (loc, s)))
  in
  let export_state (i, rex, is_final, edges) =
    if is_final then
      MLast.PaLid (loc, statename i),
      MLast.ExFun
        (loc,
         [MLast.PaLid (loc, "ofs"), None,
          MLast.ExApp
            (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")),
             MLast.ExLid (loc, "ofs"))]),
      []
    else
      let branches =
        edges |>
          List.map
            (fun (tok, newst) ->
               token_pattern tok, None,
               MLast.ExApp
                 (loc, MLast.ExLid (loc, statename newst),
                  MLast.ExApp
                    (loc,
                     MLast.ExApp
                       (loc, MLast.ExLid (loc, "+"),
                        MLast.ExLid (loc, "ofs")),
                     MLast.ExInt (loc, "1", ""))))
      in
      let branches =
        branches @
        [MLast.PaAny loc, None, MLast.ExLong (loc, MLast.LiUid (loc, "None"))]
      in
      let rhs =
        MLast.ExFun
          (loc,
           [MLast.PaLid (loc, "ofs"), None,
            MLast.ExMat
              (loc,
               MLast.ExApp
                 (loc,
                  MLast.ExApp
                    (loc, MLast.ExLid (loc, "must_peek_nth"),
                     MLast.ExApp
                       (loc,
                        MLast.ExApp
                          (loc, MLast.ExLid (loc, "+"),
                           MLast.ExLid (loc, "ofs")),
                        MLast.ExInt (loc, "1", ""))),
                  MLast.ExLid (loc, "strm")),
               branches)])
      in
      MLast.PaLid (loc, statename i), rhs, []
  in
  let bindl = List.map export_state states in
  MLast.ExFun
    (loc,
     [MLast.PaLid (loc, "strm"), None,
      MLast.ExLop
        (loc, false, MLast.MeUid (loc, "Token_regexps"),
         MLast.ExLop
           (loc, false, MLast.MeUid (loc, "PatternBaseToken"),
            MLast.ExLet
              (loc, false,
               [MLast.PaLid (loc, "must_peek_nth"),
                MLast.ExFun
                  (loc,
                   [MLast.PaLid (loc, "n"), None,
                    MLast.ExFun
                      (loc,
                       [MLast.PaLid (loc, "strm"), None,
                        MLast.ExLet
                          (loc, false,
                           [MLast.PaLid (loc, "l"),
                            MLast.ExApp
                              (loc,
                               MLast.ExApp
                                 (loc,
                                  MLast.ExFle
                                    (loc,
                                     MLast.ExLong
                                       (loc, MLast.LiUid (loc, "Stream")),
                                     (None, "npeek")),
                                  MLast.ExLid (loc, "n")),
                               MLast.ExLid (loc, "strm")),
                            []],
                           MLast.ExIfe
                             (loc,
                              MLast.ExApp
                                (loc,
                                 MLast.ExApp
                                   (loc, MLast.ExLid (loc, "="),
                                    MLast.ExApp
                                      (loc,
                                       MLast.ExFle
                                         (loc,
                                          MLast.ExLong
                                            (loc, MLast.LiUid (loc, "List")),
                                          (None, "length")),
                                       MLast.ExLid (loc, "l"))),
                                 MLast.ExLid (loc, "n")),
                              MLast.ExApp
                                (loc, MLast.ExLid (loc, "convert_token"),
                                 MLast.ExApp
                                   (loc, MLast.ExLid (loc, "fst"),
                                    MLast.ExApp
                                      (loc, MLast.ExLid (loc, "sep_last"),
                                       MLast.ExLid (loc, "l")))),
                              MLast.ExLong
                                (loc, MLast.LiUid (loc, "None"))))])]),
                []],
               MLast.ExLet
                 (loc, true, bindl,
                  MLast.ExApp
                    (loc, MLast.ExLid (loc, statename init),
                     MLast.ExInt (loc, "0", ""))))))])
;;

let expand_expr txt =
  let rex = parse txt in
  let module C = Compile (struct let rex = rex;; let extra = [];; end) in
  let dfa = C.dfa in let export = C.BEval.export dfa in export_dfa export
;;

let expand_patt txt =
  failwith
    Fmt.
    (str "Q_regexp: cannot expand quotation in a pattern position: %a"
      Dump.string txt)
;;

Quotation.add "regexp" (ExAst (expand_expr, expand_patt));;
