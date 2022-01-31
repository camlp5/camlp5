(* camlp5r *)
(* calc.ml,v *)

open Brzozowski ;


module CharToken = struct
  include Char ;
  value hash = Hashtbl.hash ;
  value foreach f = do {
    for i = Char.code 'a' to Char.code 'e' do { f (Char.chr i) };
    List.iter f [ '$' ]
  }
  ;
  value print c =
    Printf.sprintf "'%s'" (Char.escaped c) ;
end ;
module CharRegexp = Regexp(CharToken) ;

module BSyn = RESyntax(CharToken)(CharRegexp) ;
module BEval = Eval(CharToken)(CharRegexp) ;

value g = Grammar.gcreate (Plexer.gmake ());
value e = Grammar.Entry.create g "regexp";

value concatenation l =
  List.fold_left BSyn.(fun e1 e2 -> e1 @@ e2) (List.hd l) (List.tl l)
;

EXTEND
  GLOBAL: e ;
  e: [ [ x = e5 -> x ] ] ;
  e5: [ [ l = LIST1 e4 SEP "|" -> BSyn.disjunction l ] ] ;

  e4: [ [ l = LIST1 e3 SEP "&" -> BSyn.conjunction l ] ] ;

  e3: [ [ l = LIST1 e2 -> concatenation l ] ] ;

  e2: [ [ "~"; x = e1 -> BSyn.neg x | x = e1 -> x ] ] ;

  e1: [ [ x = e0; "*" -> BSyn.star x | x = e0 -> x ] ] ;

  e0:
    [ [ x = CHAR -> BSyn.token (String.get (Scanf.unescaped x) 0)
      | "("; x = e5; ")" -> x
      | "eps" -> BSyn.epsilon
      ]
    ]
  ;
END;

value parse s =
  Grammar.Entry.parse e (Stream.of_string s)
;
