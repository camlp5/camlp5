(* camlp5o *)
(* streams.ml,v *)

open Genlex

let lexer = make_lexer ["+";"-";"*";"/"; "("; ")"]

let list_of_stream strm =
let rec listrec acc = parser
  [< 't ; strm >] -> listrec (t::acc) strm
| [< >] -> List.rev acc
in listrec [] strm

let pleft f sep =
let rec paux v1 = parser
  [< op = sep ; v2 = f ; rv = paux (op v1 v2) >] -> rv
| [< >] -> v1
in parser
  [< v = f ; rv = paux v >] -> rv


let additives = parser
  [< 'Kwd"+" >] -> (fun x y -> x + y)
| [< 'Kwd"-" >] -> (fun x y -> x - y)

let multiplicatives = parser
  [< 'Kwd"*" >] -> (fun x y -> x * y)
| [< 'Kwd"/" >] -> (fun x y -> x / y)


let rec expr strm = expr1 strm
and expr1 = parser
  [< rv = pleft expr2 additives >] -> rv

and expr2 = parser
  [< rv = pleft expr3 multiplicatives >] -> rv

and expr3 = parser
  [< 'Int n >] -> n
| [< 'Kwd"(" ; e = expr1 ; 'Kwd")" >] -> e


open Printf

if not !Sys.interactive then
try
for i = 1 to Array.length Sys.argv - 1 do
  let r = Sys.argv.(i) |> Stream.of_string |> lexer |> expr in
  printf "%s = %d\n" Sys.argv.(i) r;
  flush stdout;
done
with exc -> Fmt.(pf stderr "%a@.%!" exn exc)
