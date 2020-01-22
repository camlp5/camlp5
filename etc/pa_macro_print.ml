(* camlp5r *)
(* pa_macro_gram.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pa_macro;
open Pa_extprint;

Grammar.Unsafe.clear_entry print_rule_list;

EXTEND
  GLOBAL: dexpr print_rule print_rule_list;
  print_rule_list:
    [ [ "["; "]" -> []
      | "["; rules = LIST1 print_rule_or_ifdef0 SEP "|"; "]" -> List.concat rules ] ]
  ;
  print_rule_or_ifdef0:
    [ [ "IFDEF" ; e=dexpr ; "THEN" ; e1=print_rule_or_ifdef_list ; e2=else_print_rule_or_ifdef ; "END" ->
        if e then e1 else e2]
    | [ r= print_rule -> [r] ]
    ]
  ;
  print_rule_or_ifdef:
    [ [ "IFDEF" ; e=dexpr ; "THEN" ; e1=print_rule_or_ifdef_list ; e2=else_print_rule_or_ifdef ; "END" ->
        if e then e1 else e2]
    | [ "|" ; r=print_rule -> [r] ]
    ]
  ;
  print_rule_or_ifdef_list:
    [ [ l = LIST0 print_rule_or_ifdef -> List.concat l ]
    ]
  ;
  else_print_rule_or_ifdef:
    [ [ "ELSIFDEF"; e = dexpr; "THEN"; e1 = print_rule_or_ifdef_list ; e2 = else_print_rule_or_ifdef ->
          if e then e1 else e2
      | "ELSIFNDEF"; e = dexpr; "THEN"; e1 = print_rule_or_ifdef_list ; e2 = else_print_rule_or_ifdef ->
          if not e then e1 else e2
      | "ELSE"; e = print_rule_or_ifdef_list -> e ] ]
  ;
END;
