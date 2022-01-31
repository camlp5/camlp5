(* camlp5r *)
(* calc.ml,v *)

open Brzozowski ;
open Token_regexps ;

value g = Grammar.gcreate (Plexer.gmake ());
value e = Grammar.Entry.create g "regexp";

value concatenation l =
  List.fold_left SBSyn.(fun e1 e2 -> e1 @@ e2) (List.hd l) (List.tl l)
;

EXTEND
  GLOBAL: e ;
  e: [ [ x = e5 -> x ] ] ;
  e5: [ [ l = LIST1 e4 SEP "|" -> SBSyn.disjunction l ] ] ;

  e4: [ [ l = LIST1 e3 SEP "&" -> SBSyn.conjunction l ] ] ;

  e3: [ [ l = LIST1 e2 -> concatenation l ] ] ;

  e2: [ [ "~"; x = e1 -> SBSyn.neg x | x = e1 -> x ] ] ;

  e1: [ [ x = e0; "*" -> SBSyn.star x | x = e0 -> x ] ] ;

  e0:
    [ [ x = STRING -> SBSyn.token (Scanf.unescaped x)
      | "("; x = e5; ")" -> x
      | "eps" -> SBSyn.epsilon
      ]
    ]
  ;
END;

value parse s =
  Grammar.Entry.parse e (Stream.of_string s)
;
