(* camlp5r *)
(* pa_macro_gram.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)
(* #load "pa_extend.cmo" *)
(* #load "q_MLast.cmo" *)

open Pa_macro;;
open Pa_extend;;

Grammar.Unsafe.clear_entry rule_list;;

Grammar.safe_extend
  (let _ = (dexpr : 'dexpr Grammar.Entry.e)
   and _ = (rule : 'rule Grammar.Entry.e)
   and _ = (rule_list : 'rule_list Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry dexpr) s
   in
   let rule_or_ifdef0 : 'rule_or_ifdef0 Grammar.Entry.e =
     grammar_entry_create "rule_or_ifdef0"
   and rule_or_ifdef : 'rule_or_ifdef Grammar.Entry.e =
     grammar_entry_create "rule_or_ifdef"
   and rule_or_ifdef_list : 'rule_or_ifdef_list Grammar.Entry.e =
     grammar_entry_create "rule_or_ifdef_list"
   and else_rule_or_ifdef : 'else_rule_or_ifdef Grammar.Entry.e =
     grammar_entry_create "else_rule_or_ifdef"
   in
   [Grammar.extension (rule_list : 'rule_list Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (rule_or_ifdef0 : 'rule_or_ifdef0 Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           (fun _ (rules : 'rule_or_ifdef0 list) _ (loc : Ploc.t) ->
              ({au_loc = loc; au_rules = List.concat rules} : 'rule_list)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           (fun _ _ (loc : Ploc.t) ->
              ({au_loc = loc; au_rules = []} : 'rule_list)))]];
    Grammar.extension (rule_or_ifdef0 : 'rule_or_ifdef0 Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   (Grammar.s_nterm
                      (rule_or_ifdef_list :
                       'rule_or_ifdef_list Grammar.Entry.e)))
                (Grammar.s_nterm
                   (else_rule_or_ifdef :
                    'else_rule_or_ifdef Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (e2 : 'else_rule_or_ifdef) (e1 : 'rule_or_ifdef_list) _
                (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then e1 else e2 : 'rule_or_ifdef0)))];
       None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (rule : 'rule Grammar.Entry.e)),
           (fun (r : 'rule) (loc : Ploc.t) -> ([r] : 'rule_or_ifdef0)))]];
    Grammar.extension (rule_or_ifdef : 'rule_or_ifdef Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   (Grammar.s_nterm
                      (rule_or_ifdef_list :
                       'rule_or_ifdef_list Grammar.Entry.e)))
                (Grammar.s_nterm
                   (else_rule_or_ifdef :
                    'else_rule_or_ifdef Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (e2 : 'else_rule_or_ifdef) (e1 : 'rule_or_ifdef_list) _
                (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then e1 else e2 : 'rule_or_ifdef)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "|")))
             (Grammar.s_nterm (rule : 'rule Grammar.Entry.e)),
           (fun (r : 'rule) _ (loc : Ploc.t) -> ([r] : 'rule_or_ifdef)))]];
    Grammar.extension
      (rule_or_ifdef_list : 'rule_or_ifdef_list Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0
                (Grammar.s_nterm
                   (rule_or_ifdef : 'rule_or_ifdef Grammar.Entry.e))),
           (fun (l : 'rule_or_ifdef list) (loc : Ploc.t) ->
              (List.concat l : 'rule_or_ifdef_list)))]];
    Grammar.extension
      (else_rule_or_ifdef : 'else_rule_or_ifdef Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "ELSE")))
             (Grammar.s_nterm
                (rule_or_ifdef_list : 'rule_or_ifdef_list Grammar.Entry.e)),
           (fun (e : 'rule_or_ifdef_list) _ (loc : Ploc.t) ->
              (e : 'else_rule_or_ifdef)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm
                   (rule_or_ifdef_list :
                    'rule_or_ifdef_list Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'else_rule_or_ifdef) (e1 : 'rule_or_ifdef_list) _
                (e : 'dexpr) _ (loc : Ploc.t) ->
              (if not e then e1 else e2 : 'else_rule_or_ifdef)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm
                   (rule_or_ifdef_list :
                    'rule_or_ifdef_list Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'else_rule_or_ifdef) (e1 : 'rule_or_ifdef_list) _
                (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then e1 else e2 : 'else_rule_or_ifdef)))]]]);;
