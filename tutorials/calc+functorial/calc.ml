(* camlp5r *)
(* calc.ml,v *)

module Ocamllex_L = struct
type te = (string * string) ;
value lexer = Plexing.lexer_func_of_ocamllex Calclexer.token ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;
end ;

module Gram = Grammar.GMake(Ocamllex_L) ;

value e = Gram.Entry.create "expression";

GEXTEND Gram
  e:
    [ [ x = e; "+"; y = e -> x + y
      | x = e; "-"; y = e -> x - y ]
    | [ x = e; "*"; y = e -> x * y
      | x = e; "/"; y = e -> x / y ]
    | [ x = INT -> int_of_string x
      | "("; x = e; ")" -> x ] ]
  ;
END;

open Printf;

try
for i = 1 to Array.length Sys.argv - 1 do {
  let r = Gram.Entry.parse e (Gram.parsable (Stream.of_string Sys.argv.(i))) in
  printf "%s = %d\n" Sys.argv.(i) r;
  flush stdout;
}
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
;
