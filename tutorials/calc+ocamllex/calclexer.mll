{

}

let ws = [' ' '\t']
let decimal_digit = ['0'-'9']
let decimal = decimal_digit+

rule token = parse
| "(" { ("","(") }
| ")" { ("",")") }
| "+" { ("","+") }
| "-" { ("","-") }
| "*" { ("","*") }
| "/" { ("","/") }
| decimal as dec { ("INT",dec) }
| ws+     { token lexbuf }
| eof { ("EOI","") }
