{

let locate ~comments lb v =
  let loc = Ploc.make_unlined (Lexing.lexeme_start lb, Lexing.lexeme_end lb) in
  let loc = Ploc.with_comment loc comments in
  (v, loc)

}

let ws = [' ' '\t' '\r' '\n']+
let decimal_digit = ['0'-'9']
let decimal = decimal_digit+
let comment = "//" [^ '\n']* '\n'
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule _token comments = parse
| comment { _token (comments^(Lexing.lexeme lexbuf)) lexbuf }
| ws     { _token (comments^(Lexing.lexeme lexbuf)) lexbuf }
| "(" { locate ~comments lexbuf ("","(") }
| ")" { locate ~comments lexbuf ("",")") }
| "+" { locate ~comments lexbuf ("","+") }
| "-" { locate ~comments lexbuf ("","-") }
| "*" { locate ~comments lexbuf ("","*") }
| "/" { locate ~comments lexbuf ("","/") }
| ":=" { locate ~comments lexbuf ("",":=") }
| ";" { locate ~comments lexbuf ("",";") }
| decimal as dec { locate ~comments lexbuf ("INT",dec) }
| ident as id { locate ~comments lexbuf ("IDENT",id) }
| eof { locate ~comments lexbuf ("EOI","") }

{

let token lb = _token "" lb

}
