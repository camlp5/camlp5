(* camlp5r *)
(* pa_extend_m.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "q_MLast.cmo" *)

open Pa_extend;;

Grammar.safe_extend
  (let _ = (symbol : 'symbol Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry symbol) s
   in
   let name : 'name Grammar.Entry.e = grammar_entry_create "name" in
   [Grammar.extension (symbol : 'symbol Grammar.Entry.e)
      (Some (Gramext.Level "top"))
      [None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("UIDENT", "SFLAG")))
             Grammar.s_self,
           (fun (s : 'symbol) _ (loc : Ploc.t) ->
              (ASquot (loc, ASflag (loc, s)) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("UIDENT", "SOPT")))
             Grammar.s_self,
           (fun (s : 'symbol) _ (loc : Ploc.t) ->
              (ASquot (loc, ASopt (loc, s)) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "SLIST1")))
                Grammar.s_self)
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("UIDENT", "SEP")))
                         (Grammar.s_nterm (symbol : 'symbol Grammar.Entry.e)),
                       (fun (t : 'symbol) _ (loc : Ploc.t) ->
                          (t, false : 'e__2)))])),
           (fun (sep : 'e__2 option) (s : 'symbol) _ (loc : Ploc.t) ->
              (ASquot (loc, ASlist (loc, LML_1, s, sep)) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "SLIST0")))
                Grammar.s_self)
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("UIDENT", "SEP")))
                         (Grammar.s_nterm (symbol : 'symbol Grammar.Entry.e)),
                       (fun (t : 'symbol) _ (loc : Ploc.t) ->
                          (t, false : 'e__1)))])),
           (fun (sep : 'e__1 option) (s : 'symbol) _ (loc : Ploc.t) ->
              (ASquot (loc, ASlist (loc, LML_0, s, sep)) : 'symbol)))]];
    Grammar.extension (symbol : 'symbol Grammar.Entry.e)
      (Some (Gramext.Level "vala"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("UIDENT", "SV")))
                   Grammar.s_next)
                (Grammar.s_list0 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_opt (Grammar.s_nterm (name : 'name Grammar.Entry.e))),
           (fun (oe : 'name option) (al : string list) (s : 'symbol) _
                (loc : Ploc.t) ->
              (ASvala2 (loc, s, al, oe) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("UIDENT", "SV")))
                   (Grammar.s_token ("UIDENT", "")))
                (Grammar.s_list0 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_opt (Grammar.s_nterm (name : 'name Grammar.Entry.e))),
           (fun (oe : 'name option) (al : string list) (x : string) _
                (loc : Ploc.t) ->
              (let s = AStok (loc, x, None) in ASvala2 (loc, s, al, oe) :
               'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("UIDENT", "SV")))
                   (Grammar.s_token ("UIDENT", "NEXT")))
                (Grammar.s_list0 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_opt (Grammar.s_nterm (name : 'name Grammar.Entry.e))),
           (fun (oe : 'name option) (al : string list) _ _ (loc : Ploc.t) ->
              (let s = ASnext loc in ASvala2 (loc, s, al, oe) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("UIDENT", "SV")))
                   (Grammar.s_token ("UIDENT", "SELF")))
                (Grammar.s_list0 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_opt (Grammar.s_nterm (name : 'name Grammar.Entry.e))),
           (fun (oe : 'name option) (al : string list) _ _ (loc : Ploc.t) ->
              (let s = ASself loc in ASvala2 (loc, s, al, oe) : 'symbol)))]];
    Grammar.extension (name : 'name Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (i, MLast.ExLid (loc, i) : 'name)))]]]);;
