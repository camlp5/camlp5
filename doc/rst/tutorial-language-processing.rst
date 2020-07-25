=================================================
Tutorial: Writing Language Processors with Camlp5
=================================================

In this tutorial, we'll start with the simplest program that uses
Camlp5 features, and progressively move to more and more complicated
programs, until we arrive at a parser/pretty-printer for Google
Protocol Buffers IDL.

For users who only wish to *use* Camlp5 packages (and packages built
on Camlp5), it suffices to work thru the "streams-original" and "streams"
examples: after that, all the examples are really for users who wish
to actually write programs with grammars, extensible printers, and
other Camlp5 features.

Camlp5's syntax-extensions were meant to work with revised syntax, but
typically they work just as well with original syntax.  To demonstrate
that, the most-complicated example (using lexer, grammar, and printer
syntax-extensions) is available in both revised and original syntax
(though only the revised-syntax version is described herein).  A quick
diff of the two versions will show that the differences are entirely
superficial.

.. contents::
  :local:

Here is a list of all the calculator examples with their locations.
In each case, you'll find a buildable tree (with Makefile), and simple
tests.

1. Stream parser (original syntax): ``tutorials/streams-original``
2. Stream parser (revised syntax): ``tutorials/streams``
3. Extensible grammars (built-in Camlp5 lexer): ``tutorials/calc``
4. AST, Extensible grammars, extensible printers, evaluator (ocamllex lexer): ``tutorials/calc+ocamllex``
5. Extensible grammars (functorial interface) and ocamllex lexer: ``tutorials/calc+functorial``
6. like #4, but with ``pa_lexer``-implementation of a lexer:  ``tutorials/calc+pa_lexer``
7. a translation of #6 into original syntax.

Stream parsers in original syntax: the simplest program using Camlp5 features
=============================================================================

The code for this example is in ``tutorials/streams-original``.

A very simple program that uses Camlp5 features is one that uses
:ref:`stream_parsers` .  In this example you'll find a parser for
integer expressions (addition, subtraction, multiplication, division).
It is written using the "original syntax stream parsers" syntax: the
code is in ``tutorials/streams-original/streams.ml``, and the critical bit, the
parser is as follows:

1. First a left-associative parser-combinator:
::

  let pleft f sep =
  let rec paux v1 = parser
    [< op = sep ; v2 = f ; rv = paux (op v1 v2) >] -> rv
  | [< >] -> v1
  in parser
    [< v = f ; rv = paux v >] -> rv

2. Then parser combinators for the operators:
::

  let additives = parser
    [< 'Kwd"+" >] -> (fun x y -> x + y)
  | [< 'Kwd"-" >] -> (fun x y -> x - y)

  let multiplicatives = parser
    [< 'Kwd"*" >] -> (fun x y -> x * y)
  | [< 'Kwd"/" >] -> (fun x y -> x / y)

3. And finally, the main parser, which is written in typical
   operator-precedence style:
::

  let rec expr strm = expr1 strm
  and expr1 = parser
    [< rv = pleft expr2 additives >] -> rv

  and expr2 = parser
    [< rv = pleft expr3 multiplicatives >] -> rv

  and expr3 = parser
    [< 'Int n >] -> n
  | [< 'Kwd"(" ; e = expr1 ; 'Kwd")" >] -> e

The documentation section
:ref:`stream_parsers` explains the syntax and semantics of stream parsers.  To
compile this file, we invoke::

  ocamlfind ocamlc -package camlp5,fmt -linkpkg \
      -syntax camlp5o streams.ml -o streams

The ``camlp5`` package has built-in support for stream-parsers.

To run this example::

  ./streams '1+1' '1 - 1' '1 + (2*6)'

Loading and testing in the toplevel
-----------------------------------

To load and test this example in the toplevel:

::

   $ ocaml
        OCaml version 4.10.0

   #use "topfind.camlp5";;
   #camlp5o ;;
   #require "fmt";;
   #use "streams.ml";;

   val lexer : char Stream.t -> Genlex.token Stream.t = <fun>
   val list_of_stream : 'a Stream.t -> 'a list = <fun>
   val pleft :
     ('a Stream.t -> 'b) -> ('a Stream.t -> 'b -> 'b -> 'b) -> 'a Stream.t -> 'b =
     <fun>
   val additives : Genlex.token Stream.t -> int -> int -> int = <fun>
   val multiplicatives : Genlex.token Stream.t -> int -> int -> int = <fun>
   val expr : Genlex.token Stream.t -> int = <fun>
   val expr1 : Genlex.token Stream.t -> int = <fun>
   val expr2 : Genlex.token Stream.t -> int = <fun>
   val expr3 : Genlex.token Stream.t -> int = <fun>
   - : unit = ()

And to calculate:

::

   # {| 1 + 1 |} |> Stream.of_string |> lexer |> expr ;;
- : int = 2

etc.

Stream parsers in revised syntax: the simplest program using Camlp5 features
============================================================================

The code for this example is in ``tutorials/streams``.

Since the rest of the tutorial will be written in
:ref:`revised_syntax` , we have transliterated (it's not very hard)
from original to revised syntax.  Most of the changes are
straightforward: I'll include only the left-associative parser
combinator here:

::

  value pleft f sep =
  let rec paux v1 = parser [
    [: op = sep ; v2 = f ; rv = paux (op v1 v2) :] -> rv
  | [: :] -> v1
  ]
  in parser [
    [: v = f ; rv = paux v :] -> rv
  ]
  ;

To compile this file::

  ocamlfind ocamlc -package camlp5,fmt -linkpkg -syntax camlp5r \
      streams.ml -o streams

Note that the only change in the compile line is to replace ``-syntax
camlp5o`` with ``-syntax camlp5r``.  Of course, there are changes in
``streams.ml`` from original to revised syntax.

This example runs precisely as the previous one.

A Calculator using Extensible Grammars
======================================

The code for this example is in ``tutorials/calc``.

Next, we can replace the stream-parser (and ``Genlex`` lexer) with a
grammar written using Camlp5's extensible-grammar support, and
Camlp5's built-in lexer.  You can find thie example in
``tutorials/calc/calc.ml``.  The grammar is very compact::

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

The syntax and semanatics of extensible grammars are explained in
:ref:`extensible_grammars` .  The compactness of the code comes from
two things:

1. implicit and explicit support for associativity (left-associativity
   is the default)
2. explicit support for precedence via "levels" in the grammar-rules.

To compile this example::

  ocamlfind ocamlc -package camlp5,fmt,camlp5.extend -linkpkg \
      -syntax camlp5r calc.ml -o calc

and the only difference is that we have to add the Camlp5 package
``camlp5.extend`` which provides extensible-grammar syntax support
(for the new syntax we used above, that is most definitely not normal
Ocaml!)

A Calculator using Extensible Grammars & Printers (Ocamllex-based Lexer)
========================================================================

The code for this example is found in ``tutorials/calc+ocamllex``.

The previous example used the built-in Camlp5 lexer, which supports
Ocaml-style comments.  That is, in the text which is parsed by the
calculator, ocanl-style comments would be treated as comments and
ignored.  In this example, we'll use an ocamllex-generated lexer,
which handles C++-ctyle comments instead.  To refresh, C++-style
comments are thus::

  int x = 1 ; // any text to end of line

and we'll augment the language we parse with variables and
assignment-statements, in addition to expressions.  We'll also add a
real parse-tree and evaluator.  And finally, when pretty-printing,
let's print out comments that appear immediately before statements.

Because this example will be pretty involved, we'll go thru it
step-by-step, explaining each block of code and what it does, with
pointers to the relevant bits of documentation.

The Lexer
---------

The lexer is a standard ocamllex lexer.  We define regular expressions:
::

   let ws = [' ' '\t' '\r' '\n']+
   let decimal_digit = ['0'-'9']
   let decimal = decimal_digit+
   let comment = "//" [^ '\n']* '\n'
   let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

and a tokenizer that accumulates comments (notice they're C++-style)
before a token:

::

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

At end-of-input, we return the special token ``("EOI","")``, so that
the grammar can explicitly require that parsing consume all the input.
Notice the way we're wrapping each return with a ``locate``
function-call.  This function takes the current lexbuf and
comments/whitespace so far accumulated before the token, and builds a
Camlp5 location (``Ploc.t``) to return along with the token:

::

   let locate ~comments lb v =
     let loc = Ploc.make_unlined (Lexing.lexeme_start lb, Lexing.lexeme_end lb) in
     let loc = Ploc.with_comment loc comments in
    (v, loc)

Also, as you can see a token (for Camlp5's grammar engine) is always a
pair of its class (a string) and the text of the token.

To make an ocamllex lexer available to Camlp5's grammar-interpreter,
there is a little bit of special sauce:

::

   value lexer = Plexing.lexer_func_of_ocamllex_located Calclexer.token ;
   value lexer = {Plexing.tok_func = lexer;
    Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
    Plexing.tok_match = Plexing.default_match;
    Plexing.tok_text = Plexing.lexer_text;
    Plexing.tok_comm = None} ;

The AST
-------

The AST is straightforward.  There are expressions with unary and
binary operators, integer constants, and variable-names.  There are
statements of two kinds: expression-statements and
assignment-statements.  We will see later an "environment" mapping
identifiers to integers, to support these variables and assignments.
Notice that most AST nodes also have a ``Ploc.t``.  In a real
language-processor, this would allow to print locations in
error-messages (as we'll do in the evaluator).

::

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

The Grammar
-----------

The grammar is what we'd expect: there are nonterminals for
statements, expressions, and a list of statements that consume all the
input.  For nodes other than toplevel statements, we strip comments
from the location.  Also, Camlp5's grammar-interpreter is a classic
LL(1) engine, but there is one ambiguity which would require work to
resolve: when we see an input like "x", we don't know if it will
continue as an expression-statement, or an assignment-statement.
There are standard ways (in LL(1) grammars) of resolving this, but
here I'm just going to do a little bit of lookahead (one token) to
check whether the next token is a ":=" (in the function
`check_id_coloneq`).  This is something pretty common in writing LL(1)
parsers: instead of working hard to make the grammar LL(1), go ahead
and use some lookahead.

::

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


The Pretty-Printer
------------------

We could write the pretty-printer as a recursive function over the
types ``expr`` and ``stmt``.  But instead, we'll write it using
Ocaml's :ref:`extensible_printers` support.  This allows to extend a
printer with new rules after it's been defined (though we won't do
that here).  Please consult the documentation on the ``Pretty`` module
and ``pprintf`` to understand how the pretty-printing actually works.

NOTE: this actually really ugly pretty-printing.  I haven't completely
figured out how to use ``pprintf`` to get nice indentation; when I do,
this tutorial will be updated.

First, some setup (defining the printers, and convenience
functions that call them:

::

   value parse_expr = Grammar.Entry.parse expr ;
   value parse_stmt = Grammar.Entry.parse stmt ;
   value parse_stmts = Grammar.Entry.parse stmts ;
   value parse_stmts_eoi = Grammar.Entry.parse stmts_eoi ;

   value pr_expr = Eprinter.make "expr";
   value pr_stmt = Eprinter.make "stmt";
   value pr_stmts = Eprinter.make "stmts";

   value print_expr = Eprinter.apply pr_expr;
   value print_stmt = Eprinter.apply pr_stmt;

Here's a function that prints out statement, and the comment prior to
it, if that comment string is nonempty:

::

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

And finally the printers themselves.  Just as with the grammar, it's
defined in precedence levels.  Each level has pattern-matching, and
the default is to proceed to the next level.

:::

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

The Evaluator
-------------

The evaluator is bog-standard, but with the one nuance that when it
cannot locate a variable in the environment, it raises an exception
wrapped with a ``Ploc.t``.

::

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

The Results
-----------

On the input:

::

   // foo
   1+2 ;
   // bar
   x := 3

the output is:

::

   {
     // foo
   1 + 2;

   // bar
   x := 3
     } =
     [3; 3]

As I noted above, I haven't completely figured-out the way ``pprintf``
is supposed to be used.  Now how about an erroneous input?

::

   echo "1+2+y" | ./calc
   File "", line 1, characters 5-6:
   Failure("variable y not found in environment")

When we pretty-print the exception, we can pretty-print the location:

::

   try
       let l = parse_stmts_eoi (Stream.of_channel stdin) in do {
         let print_int pc n = pprintf pc "%d" n in
         printf "%s" (pprintf Pprintf.empty_pc "%p =@;@[[%p]@]\n"
                        print_stmts l
                        (plist_semi print_int 2) (List.rev(snd(Eval.stmts [] l))))
       }
   with [ Ploc.Exc loc exc ->
       Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
     | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
   ]

A Calculator using Extensible Grammars (the Functorial Interface)
=================================================================

The code for this example is in ``tutorials/calc+functorial``.  This
example is in the style of "A Calculator using Extensible Grammars"_,
but with the functorial interface to grammars.  It also uses an
ocamllex-based lexer.  Here's the code for the functorial bits:

::

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

The rest is pretty straightforward and just like the
``tutorials/calc`` example.

A Calculator using Extensible Grammars & Printers (``pa_lexer``-based Lexer)
============================================================================

The code for this example is in ``tutorials/calc+pa_lexer``.

This example replaces the ocamllex-based lexer with one using Camlp5's
builtin ``pa_lexer`` syntax extension.

TODO: finish this sub-section.

.. container:: trailer
