{

}

let ws = [' ' '\t' '\r' '\n']+
let decimal_digit = ['0'-'9']
let decimal = decimal_digit+
let comment = "//" [^ '\n']* '\n'
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule token = parse
| comment { token lexbuf }
| ws     { token lexbuf }
| "(" { ("","(") }
| ")" { ("",")") }
| "+" { ("","+") }
| "-" { ("","-") }
| "*" { ("","*") }
| "/" { ("","/") }
| ":=" { ("",":=") }
| ";" { ("",";") }
| decimal as dec { ("INT",dec) }
| ident as id { ("IDENT",id) }
| eof { ("EOI","") }
