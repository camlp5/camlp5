#load "pa_extend.cmo";

value g = Grammar.gcreate (Plexer.gmake ());
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

for i = 1 to Array.length Sys.argv - 1 do {
  let r = Grammar.Entry.parse e (Stream.of_string Sys.argv.(i)) in
  printf "%s = %d\n" Sys.argv.(i) r;
  flush stdout;
};
