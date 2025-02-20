(* camlp5r *)
(* calc.ml,v *)

let input_file = ref "" ;;
let nonws_re = Pcre2.regexp "\\S" ;;
let has_nonws s = Pcre2.pmatch ~rex:nonws_re s ;;

type ctxt = {
  line_nb : int ref ;
  bol_pos : int ref
} ;;

let rec number =
  lexer
  [ '0'-'9' number!
  | -> ("INT", $buf)
  ]
;;

let rec ident =
  lexer
  [ [ 'a'-'z' | 'A'-'Z' | '_' | '0'-'9'] ident!
  | -> ("IDENT",$buf)
  ]
;;

let next_token_must ctxt =
  lexer
  [ '0'-'9' number!
  | [ '+' | '-' | '*' | '/' | '(' | ')' ] -> ("",$buf)
  | ":=" -> ("",$buf)
  | ";" -> ("",$buf)
  | [ 'a'-'z' | 'A'-'Z' | '_' ] ident!
  ]
;;

let start_line ctxt ep =
    ctxt.line_nb := 1 + !(ctxt.line_nb) ;
    ctxt.bol_pos := ep
;;

let rec comment_rest ctxt buf = parser
  [< ''\n' >] ep ->
      start_line ctxt ep ;
      $add '\n'

| [< 'c ; strm >] -> comment_rest ctxt ($add c) strm
;;

let comment ctxt =
  lexer
  [ "//" (comment_rest ctxt)!
  ]
;;

let rec next_token ctxt buf = parser bp
    [< ?= [ '/' ; '/' ] ; buf = comment ctxt buf ; strm >] ->
      next_token ctxt buf strm
  | [< ' (' '|'\t'|'\r' as c) ; strm >] ->
      next_token ctxt ($add c) strm
  | [< ''\n' ; strm >] ep ->
      start_line ctxt ep ;
      next_token ctxt ($add '\n') strm

  | [< tok = next_token_must ctxt $empty >] ep ->
    let comm = $buf in
    let loc = Ploc.make_loc !input_file !(ctxt.line_nb) !(ctxt.bol_pos) (bp,ep) comm in
    (tok, loc)
  | [< _ = Stream.empty >] ep ->
    let comm = $buf in
    let loc = Ploc.make_loc !input_file !(ctxt.line_nb) !(ctxt.bol_pos) (bp,ep) comm in
    (("EOI",""), loc)
;;

let next_token_fun (cstrm, s_line_nb, s_bol_pos) =
  let ctxt = { line_nb = s_line_nb ; bol_pos = s_bol_pos } in
  next_token ctxt $empty cstrm
;;

type binop = ADD | SUB | DIV | MUL ;;
type unop = PLUS | MINUS ;;
type expr =
  BINOP of Ploc.t * binop * expr * expr
| UNOP of Ploc.t * unop * expr
| INT of Ploc.t * int
| VAR of Ploc.t * string
and stmt =
  ASSIGN of Ploc.t * string * expr
| EXPR of Ploc.t * expr
;;

let loc_of_expr = function
  BINOP(loc, _, _, _) -> loc
| UNOP(loc, _, _) -> loc
| INT(loc, _) -> loc
| VAR(loc, _) -> loc
;;

let loc_of_stmt = function
  ASSIGN(loc, _, _) -> loc
| EXPR(loc, _) -> loc
;;

let lexer_ = Plexing.lexer_func_of_parser next_token_fun ;;
let lexer_ = {Plexing.tok_func = lexer_ ;
 Plexing.tok_using = (fun _ -> ()); Plexing.tok_removing = (fun _ -> ());
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None ; Plexing.kwds = Hashtbl.create 23 } ;;

let g = Grammar.gcreate lexer_ ;;
let expr = Grammar.Entry.create g "expression";;
let stmt = Grammar.Entry.create g "statement";;
let stmts = Grammar.Entry.create g "statements";;
let stmts_eoi = Grammar.Entry.create g "statements_eoi";;

let loc_strip_comment loc = Ploc.with_comment loc "" ;;


let check_id_coloneq =
  Grammar.Entry.of_parser g "check_id_coloneq"
    (fun strm ->
       match Stream.npeek 2 strm with
         [("IDENT", _); ("", ":=")] -> ()
       | _ -> raise Stream.Failure )
;;

EXTEND
  GLOBAL: expr stmt stmts stmts_eoi check_id_coloneq ;
  expr:
    [ [ x = expr; "+"; y = expr -> BINOP (loc_strip_comment loc, ADD, x, y)
      | x = expr; "-"; y = expr -> BINOP (loc_strip_comment loc, SUB, x, y) ]
    | [ x = expr; "*"; y = expr -> BINOP (loc_strip_comment loc, MUL, x, y)
      | x = expr; "/"; y = expr -> BINOP (loc_strip_comment loc, DIV, x,  y) ]
    | [ "-" ; x = expr -> UNOP (loc, MINUS, x)
      | "+" ; x = expr -> UNOP (loc, PLUS, x) ]
    | [ x = INT -> INT (loc, int_of_string x)
      | x = IDENT -> VAR (loc, x)
      | "("; x = expr; ")" -> x
      ]
    ]
  ;
  stmt:
    [ [ check_id_coloneq ; id = IDENT ; ":=" ; x = expr -> ASSIGN (loc, id, x)
      | x = expr -> EXPR (loc, x) ]
    ]
  ;
  stmts : [ [ l = LIST1 stmt SEP ";" -> l ] ] ;
  stmts_eoi : [ [ l = stmts ; EOI -> l ] ] ;
END;;

let parse_expr = Grammar.Entry.parse expr ;;
let parse_stmt = Grammar.Entry.parse stmt ;;
let parse_stmts = Grammar.Entry.parse stmts ;;
let parse_stmts_eoi = Grammar.Entry.parse stmts_eoi ;;

let pr_expr = Eprinter.make "expr";;
let pr_stmt = Eprinter.make "stmt";;
let pr_stmts = Eprinter.make "stmts";;

let print_expr = Eprinter.apply pr_expr;;
let print_stmt = Eprinter.apply pr_stmt;;
let print_commented_stmt pc stmt =
  let loc = loc_of_stmt stmt in
  let comment = Ploc.comment loc in
  let comment = if has_nonws comment then comment else "" in
  let pp = (fun () -> pprintf pc "%s%p" comment print_stmt stmt) in
    Pretty.horiz_vertic pp pp
;;

let print_stmts = Eprinter.apply pr_stmts;;

let plist_semi f sh pc l =
  let l = List.map (fun s -> (s, ";")) l in
  pprintf pc "%p" (Prtools.plist f sh) l
;;

EXTEND_PRINTER
  pr_expr:
    [ "add"
      [ BINOP (_, ADD, x, y) -> pprintf pc "%p + %p" curr x next y
      | BINOP (_, SUB, x, y) -> pprintf pc "%p - %p" curr x next y ]
    | "mul"
      [ BINOP (_, MUL, x, y) -> pprintf pc "%p * %p" curr x next y
      | BINOP (_, DIV, x, y) -> pprintf pc "%p / %p" curr x next y ]
    | "uminus"
      [ UNOP (_, PLUS, x) -> pprintf pc "+ %p" curr x
      | UNOP (_, MINUS, x) -> pprintf pc "- %p" curr x ]
    | "simple"
      [ INT (_, x) -> pprintf pc "%d" x
      | VAR (_, s) -> pprintf pc "%s" s
      | x -> pprintf pc "(%p)" print_expr x ]
    ] ;
  pr_stmt:
    [ [ ASSIGN (_, id, e) -> pprintf pc "@[%s := %p@]" id print_expr e
      | EXPR (_, e) -> pprintf pc "@[%p@]" print_expr e ]
    ]
  ;
  pr_stmts:
    [ [ l -> pprintf pc "{@;%p@;}" (plist_semi print_commented_stmt 0) l ]
    ]
  ;
END;

module Eval = struct
let expr env e =
  let rec erec = function
    BINOP (_, ADD, x, y) -> (erec x)+(erec y)
  | BINOP (_, SUB, x, y) -> (erec x)-(erec y)
  | BINOP (_, DIV, x, y) -> (erec x)/(erec y)
  | BINOP (_, MUL, x, y) -> (erec x)*(erec y)
  | UNOP (_, MINUS, x) -> -(erec x)
  | UNOP (_, PLUS, x) -> erec x
  | INT (_, x) -> x
  | VAR (loc, s) -> match List.assoc s env with
      x -> x
    | exception Not_found -> Ploc.raise loc (Failure (Printf.sprintf "variable %s not found in environment" s))
  in erec e

let stmt env = function
  ASSIGN (_, s, e) ->
    let v = expr env e in ((s, v) :: env, v)
| EXPR (_, e) -> (env, expr env e)

let stmts env l =
  List.fold_left (fun (env, acc) s -> let (env, v) = stmt env s in (env, v :: acc)) (env, []) l
end

open Printf

Pretty.line_length := 100 ;;

if not !Sys.interactive then
try
    let l = parse_stmts_eoi (Stream.of_channel stdin) in
      let print_int pc n = pprintf pc "%d" n in
      printf "%s" (pprintf Pprintf.empty_pc "%p =@;@[[%p]@]\n"
                     print_stmts l
                     (plist_semi print_int 2) (List.rev(snd(Eval.stmts [] l))))
with Ploc.Exc (loc, exc) ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
else ()
;;
