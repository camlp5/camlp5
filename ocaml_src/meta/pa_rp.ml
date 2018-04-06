(* camlp5r *)
(* pa_rp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "q_MLast.cmo" *)

open Exparser;;
open Pcaml;;

(* Syntax extensions in Revised Syntax grammar *)

Grammar.safe_extend
  (let _ = (expr : 'expr Grammar.Entry.e)
   and _ = (ipatt : 'ipatt Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry expr) s
   in
   let parser_case : 'parser_case Grammar.Entry.e =
     grammar_entry_create "parser_case"
   and stream_patt : 'stream_patt Grammar.Entry.e =
     grammar_entry_create "stream_patt"
   and stream_patt_kont : 'stream_patt_kont Grammar.Entry.e =
     grammar_entry_create "stream_patt_kont"
   and stream_patt_comp_err : 'stream_patt_comp_err Grammar.Entry.e =
     grammar_entry_create "stream_patt_comp_err"
   and stream_patt_comp : 'stream_patt_comp Grammar.Entry.e =
     grammar_entry_create "stream_patt_comp"
   and stream_patt_let : 'stream_patt_let Grammar.Entry.e =
     grammar_entry_create "stream_patt_let"
   and lookahead : 'lookahead Grammar.Entry.e =
     grammar_entry_create "lookahead"
   and stream_expr_comp : 'stream_expr_comp Grammar.Entry.e =
     grammar_entry_create "stream_expr_comp"
   in
   [Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "top"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "match")))
                         Grammar.s_self)
                      (Grammar.s_token ("", "with")))
                   (Grammar.s_token ("", "parser")))
                (Grammar.s_opt
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))))
             (Grammar.s_nterm (parser_case : 'parser_case Grammar.Entry.e)),
           (fun (pc : 'parser_case) (po : 'ipatt option) _ _ (e : 'expr) _
                (loc : Ploc.t) ->
              (cparser_match loc e po [pc] : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "match")))
                               Grammar.s_self)
                            (Grammar.s_token ("", "with")))
                         (Grammar.s_token ("", "parser")))
                      (Grammar.s_opt
                         (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))))
                   (Grammar.s_token ("", "[")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm
                      (parser_case : 'parser_case Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           (fun _ (pcl : 'parser_case list) _ (po : 'ipatt option) _ _
                (e : 'expr) _ (loc : Ploc.t) ->
              (cparser_match loc e po pcl : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "parser")))
                (Grammar.s_opt
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))))
             (Grammar.s_nterm (parser_case : 'parser_case Grammar.Entry.e)),
           (fun (pc : 'parser_case) (po : 'ipatt option) _ (loc : Ploc.t) ->
              (cparser loc po [pc] : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "parser")))
                      (Grammar.s_opt
                         (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))))
                   (Grammar.s_token ("", "[")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm
                      (parser_case : 'parser_case Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           (fun _ (pcl : 'parser_case list) _ (po : 'ipatt option) _
                (loc : Ploc.t) ->
              (cparser loc po pcl : 'expr)))]];
    Grammar.extension (parser_case : 'parser_case Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "[:")))
                         (Grammar.s_nterm
                            (stream_patt : 'stream_patt Grammar.Entry.e)))
                      (Grammar.s_token ("", ":]")))
                   (Grammar.s_opt
                      (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))))
                (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (po : 'ipatt option) _ (sp : 'stream_patt) _
                (loc : Ploc.t) ->
              (sp, po, e : 'parser_case)))]];
    Grammar.extension (stream_patt : 'stream_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> ([] : 'stream_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (stream_patt_let : 'stream_patt_let Grammar.Entry.e)))
             Grammar.s_self,
           (fun (sp : 'stream_patt) (spc : 'stream_patt_let) (loc : Ploc.t) ->
              (spc :: sp : 'stream_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (stream_patt_comp : 'stream_patt_comp Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             (Grammar.s_nterm
                (stream_patt_kont : 'stream_patt_kont Grammar.Entry.e)),
           (fun (sp : 'stream_patt_kont) _ (spc : 'stream_patt_comp)
                (loc : Ploc.t) ->
              ((spc, SpoNoth) :: sp : 'stream_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (stream_patt_comp : 'stream_patt_comp Grammar.Entry.e)),
           (fun (spc : 'stream_patt_comp) (loc : Ploc.t) ->
              ([spc, SpoNoth] : 'stream_patt)))]];
    Grammar.extension (stream_patt_kont : 'stream_patt_kont Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (stream_patt_let : 'stream_patt_let Grammar.Entry.e)))
             Grammar.s_self,
           (fun (sp : 'stream_patt_kont) (spc : 'stream_patt_let)
                (loc : Ploc.t) ->
              (spc :: sp : 'stream_patt_kont)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (stream_patt_comp_err :
                       'stream_patt_comp_err Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             Grammar.s_self,
           (fun (sp : 'stream_patt_kont) _ (spc : 'stream_patt_comp_err)
                (loc : Ploc.t) ->
              (spc :: sp : 'stream_patt_kont)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (stream_patt_comp_err :
                 'stream_patt_comp_err Grammar.Entry.e)),
           (fun (spc : 'stream_patt_comp_err) (loc : Ploc.t) ->
              ([spc] : 'stream_patt_kont)))]];
    Grammar.extension
      (stream_patt_comp_err : 'stream_patt_comp_err Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (stream_patt_comp : 'stream_patt_comp Grammar.Entry.e)),
           (fun (spc : 'stream_patt_comp) (loc : Ploc.t) ->
              (spc, SpoNoth : 'stream_patt_comp_err)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (stream_patt_comp : 'stream_patt_comp Grammar.Entry.e)))
             (Grammar.s_token ("", "!")),
           (fun _ (spc : 'stream_patt_comp) (loc : Ploc.t) ->
              (spc, SpoBang : 'stream_patt_comp_err)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (stream_patt_comp : 'stream_patt_comp Grammar.Entry.e)))
                (Grammar.s_token ("", "?")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (spc : 'stream_patt_comp) (loc : Ploc.t) ->
              (spc, SpoQues e : 'stream_patt_comp_err)))]];
    Grammar.extension (stream_patt_comp : 'stream_patt_comp Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) (loc : Ploc.t) ->
              (SpStr (loc, p) : 'stream_patt_comp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (p : 'patt) (loc : Ploc.t) ->
              (SpNtr (loc, p, e) : 'stream_patt_comp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "?=")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (lookahead : 'lookahead Grammar.Entry.e))
                (Grammar.s_token ("", "|")) false),
           (fun (pll : 'lookahead list) _ (loc : Ploc.t) ->
              (SpLhd (loc, pll) : 'stream_patt_comp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "when")))
                         (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
                       (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'e__1)))])),
           (fun (eo : 'e__1 option) (p : 'patt) _ (loc : Ploc.t) ->
              (SpTrm (loc, p, eo) : 'stream_patt_comp)))]];
    Grammar.extension (stream_patt_let : 'stream_patt_let Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", "in")),
           (fun _ (e : 'expr) _ (p : 'ipatt) _ (loc : Ploc.t) ->
              (SpLet (loc, p, e), SpoNoth : 'stream_patt_let)))]];
    Grammar.extension (lookahead : 'lookahead Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "]")),
           (fun _ (pl : 'patt list) _ (loc : Ploc.t) -> (pl : 'lookahead)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[:")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm
                      (stream_expr_comp : 'stream_expr_comp Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", ":]")),
           (fun _ (se : 'stream_expr_comp list) _ (loc : Ploc.t) ->
              (cstream loc se : 'expr)))]];
    Grammar.extension (stream_expr_comp : 'stream_expr_comp Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) (loc : Ploc.t) ->
              (SeNtr (loc, e) : 'stream_expr_comp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (SeTrm (loc, e) : 'stream_expr_comp)))]]]);;
