#load "pa_extend.cmo";

value lexer = Plexing.lexer_func_of_parser Calc_lexer.next_token_fun ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

value g = Grammar.gcreate lexer;
value e = Grammar.Entry.create g "expression";

EXTEND
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
  let r = Grammar.Entry.parse e (Stream.of_string Sys.argv.(i)) in
  printf "%s = %d\n" Sys.argv.(i) r;
  flush stdout;
}
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
;
