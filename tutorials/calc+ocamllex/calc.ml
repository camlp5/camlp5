(* camlp5r *)
(* calc.ml,v *)

value input_file = ref "" ;
value nonws_re = Pcre.regexp "\\S" ;
value has_nonws s = Pcre.pmatch ~{rex=nonws_re} s;

value lexer = Plexing.lexer_func_of_ocamllex_located Calclexer.token ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

type binop = [ ADD | SUB | DIV | MUL ] ;
type unop = [ PLUS | MINUS ] ;
type expr = [
  BINOP of Ploc.t and binop and expr and expr
| UNOP of Ploc.t and unop and expr
| INT of Ploc.t and int
| VAR of Ploc.t and string ]
and stmt = [
  ASSIGN of Ploc.t and string and expr
| EXPR of Ploc.t and expr
]
;

value loc_of_expr = fun [
  BINOP loc _ _ _ -> loc
| UNOP loc _ _ -> loc
| INT loc _ -> loc
| VAR loc _ -> loc
]
;
value loc_of_stmt = fun [
  ASSIGN loc _ _ -> loc
| EXPR loc _ -> loc
]
;

value g = Grammar.gcreate lexer;
value expr = Grammar.Entry.create g "expression";
value stmt = Grammar.Entry.create g "statement";
value stmts = Grammar.Entry.create g "statements";
value stmts_eoi = Grammar.Entry.create g "statements_eoi";

value loc_strip_comment loc = Ploc.with_comment loc "" ;


value check_id_coloneq =
  Grammar.Entry.of_parser g "check_id_coloneq"
    (fun strm ->
       match Stream.npeek 2 strm with
       [ [("IDENT", _); ("", ":=")] -> ()
       | _ -> raise Stream.Failure ])
;

EXTEND
  GLOBAL: expr stmt stmts stmts_eoi check_id_coloneq ;
  expr:
    [ [ x = expr; "+"; y = expr -> BINOP (loc_strip_comment loc) ADD x y
      | x = expr; "-"; y = expr -> BINOP (loc_strip_comment loc) SUB x y ]
    | [ x = expr; "*"; y = expr -> BINOP (loc_strip_comment loc) MUL x y
      | x = expr; "/"; y = expr -> BINOP (loc_strip_comment loc) DIV x  y ]
    | [ "-" ; x = expr -> UNOP loc MINUS x
      | "+" ; x = expr -> UNOP loc PLUS x ]
    | [ x = INT -> INT loc (int_of_string x)
      | x = IDENT -> VAR loc x
      | "("; x = expr; ")" -> x
      ]
    ]
  ;
  stmt:
    [ [ check_id_coloneq ; id = IDENT ; ":=" ; x = expr -> ASSIGN loc id x
      | x = expr -> EXPR loc x ]
    ]
  ;
  stmts : [ [ l = LIST1 stmt SEP ";" -> l ] ] ;
  stmts_eoi : [ [ l = stmts ; EOI -> l ] ] ;
END;

value parse_expr = Grammar.Entry.parse expr ;
value parse_stmt = Grammar.Entry.parse stmt ;
value parse_stmts = Grammar.Entry.parse stmts ;
value parse_stmts_eoi = Grammar.Entry.parse stmts_eoi ;

value pr_expr = Eprinter.make "expr";
value pr_stmt = Eprinter.make "stmt";
value pr_stmts = Eprinter.make "stmts";

value print_expr = Eprinter.apply pr_expr;
value print_stmt = Eprinter.apply pr_stmt;
value print_commented_stmt pc stmt =
  let loc = loc_of_stmt stmt in
  let comment = Ploc.comment loc in
  let comment = if has_nonws comment then comment else "" in
  let pp = (fun () -> pprintf pc "%s%p" comment print_stmt stmt) in
    Pretty.horiz_vertic pp pp
;

value print_stmts = Eprinter.apply pr_stmts;

value plist_semi f sh pc l =
  let l = List.map (fun s -> (s, ";")) l in
  pprintf pc "%p" (Prtools.plist f sh) l
;

EXTEND_PRINTER
  pr_expr:
    [ "add"
      [ BINOP _ ADD x y -> pprintf pc "%p + %p" curr x next y
      | BINOP _ SUB x y -> pprintf pc "%p - %p" curr x next y ]
    | "mul"
      [ BINOP _ MUL x y -> pprintf pc "%p * %p" curr x next y
      | BINOP _ DIV x y -> pprintf pc "%p / %p" curr x next y ]
    | "uminus"
      [ UNOP _ PLUS x -> pprintf pc "+ %p" curr x
      | UNOP _ MINUS x -> pprintf pc "- %p" curr x ]
    | "simple"
      [ INT _ x -> pprintf pc "%d" x
      | x -> pprintf pc "(%p)" print_expr x ]
    ] ;
  pr_stmt:
    [ [ ASSIGN _ id e -> pprintf pc "@[%s := %p@]" id print_expr e
      | EXPR _ e -> pprintf pc "@[%p@]" print_expr e ]
    ]
  ;
  pr_stmts:
    [ [ l -> pprintf pc "{@;%p@;}" (plist_semi print_commented_stmt 0) l ]
    ]
  ;
END;

module Eval = struct
value expr env e =
  let rec erec = fun [
    BINOP _ ADD x y -> (erec x)+(erec y)
  | BINOP _ SUB x y -> (erec x)-(erec y)
  | BINOP _ DIV x y -> (erec x)/(erec y)
  | BINOP _ MUL x y -> (erec x)*(erec y)
  | UNOP _ MINUS x -> -(erec x)
  | UNOP _ PLUS x -> erec x
  | INT _ x -> x
  | VAR loc s -> match List.assoc s env with [
      x -> x
    | exception Not_found -> Ploc.raise loc (Failure (Printf.sprintf "variable %s not found in environment" s)) ]
  ]
  in erec e
;
value stmt env = fun [
  ASSIGN _ s e ->
    let v = expr env e in ([ (s, v) :: env ], v)
| EXPR _ e -> (env, expr env e)
]
;

value stmts env l =
  List.fold_left (fun (env, acc) s -> let (env, v) = stmt env s in (env, [v :: acc])) (env, []) l ;
end
;

open Printf;

Pretty.line_length.val := 100 ;

if not Sys.interactive.val then
try
    let l = parse_stmts_eoi (Stream.of_channel stdin) in do {
      let print_int pc n = pprintf pc "%d" n in
      printf "%s" (pprintf Pprintf.empty_pc "%p =@;@[[%p]@]\n"
                     print_stmts l
                     (plist_semi print_int 2) (snd(Eval.stmts [] l)))
    }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
