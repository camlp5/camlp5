(* camlp5r *)
(* pa_macro_gram.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pa_macro;
open Pa_extend;

Grammar.Unsafe.clear_entry rule_list;
Grammar.Unsafe.clear_entry level_list;

value must_flatten_opts ll  =
List.fold_right (fun levs acc ->
    match levs with [
      None -> acc
    | Some v -> v @ acc
    ]
  ) ll []
;

EXTEND
  GLOBAL: dexpr rule rule_list level level_list;
  rule_list:
    [ [ "["; "]" -> {au_loc = loc; au_rules = []}
      | "["; rules = LIST1 rule_or_ifdef0 SEP "|"; "]" ->
          {au_loc = loc; au_rules = List.concat rules} ] ]
  ;
  rule_or_ifdef0:
    [ [ "IFDEF" ; e=dexpr ; "THEN" ; e1=rule_or_ifdef_list ; e2=else_rule_or_ifdef ; "END" ->
        if e then e1 else e2]
    | [ r=rule -> [r] ]
    ]
  ;
  rule_or_ifdef:
    [ [ "IFDEF" ; e=dexpr ; "THEN" ; e1=rule_or_ifdef_list ; e2=else_rule_or_ifdef ; "END" ->
        if e then e1 else e2]
    | [ "|" ; r=rule -> [r] ]
    ]
  ;
  rule_or_ifdef_list:
    [ [ l = LIST0 rule_or_ifdef -> List.concat l ]
    ]
  ;
  else_rule_or_ifdef:
    [ [ "ELSIFDEF"; e = dexpr; "THEN"; e1 = rule_or_ifdef_list ; e2 = else_rule_or_ifdef ->
          if e then e1 else e2
      | "ELSIFNDEF"; e = dexpr; "THEN"; e1 = rule_or_ifdef_list ; e2 = else_rule_or_ifdef ->
          if not e then e1 else e2
      | "ELSE"; e = rule_or_ifdef_list -> e ] ]
  ;
  level_list:
    [ [ "["; ll = LIST1 level_or_ifdef_opt SEP "|"; "]" -> must_flatten_opts ll ] ]
  ;
  level_or_ifdef_opt:
    [ [ "IFDEF" ; e=dexpr ; "THEN" ; e1=levels_or_ifdef_opt ; e2=else_levels_or_ifdef_opt ; "END" ->
        if e then e1 else e2]
    | [ l = level -> Some [l] ]
    | [ -> None ]
    ]
  ;
  levels_or_ifdef_opt:
    [ [ "IFDEF" ; e=dexpr ; "THEN" ; e1=levels_or_ifdef_opt ; e2=else_levels_or_ifdef_opt ; "END" ->
        if e then e1 else e2]
    | [ ll = LIST1 level SEP "|" -> Some ll ]
    | [ -> None ]
    ]
  ;
  else_levels_or_ifdef_opt:
    [ [ "ELSIFDEF"; e = dexpr; "THEN"; e1 = levels_or_ifdef_opt ; e2 = else_levels_or_ifdef_opt ->
          if e then e1 else e2
      | "ELSIFNDEF"; e = dexpr; "THEN"; e1 = levels_or_ifdef_opt ; e2 = else_levels_or_ifdef_opt ->
          if not e then e1 else e2
      | "ELSE"; e = levels_or_ifdef_opt -> e ] ]
  ;
END;
