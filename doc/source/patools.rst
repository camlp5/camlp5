#############
Parsing tools
#############

.. _stream-parsers:

**************
Stream parsers
**************

We describe here the syntax and the semantics of the parsers of
streams of Camlp5. Streams are kinds of lazy lists. The parsers of
these streams use recursive descendent method without backtracking,
which is the most natural one in functional languages. In particular,
parsers are normal functions.

Notice that the parsers have existed in OCaml since many years (the
beginning of the 90ies), but some new features have been added in 2007
(lookahead, "no error" optimization, let..in statement and left
factorization) in Camlp5 distribution. This chapter describes them
also.

Introduction
============

Parsers apply to values of type ``Stream.t`` defined in the module
``Stream`` of the standard library of OCaml. Like the type ``list``, the
type ``Stream.t`` has a type parameter, indicating the type of its
elements. They differ from the lists that they are lazy (the elements
are evaluated as long as the parser need them for its actions), and
imperative (parsers deletes their first elements when they take their
parsing decisions): notice that purely functional parsers exist in
Camlp5, where the corresponding streams are lazy and functional, the
analyzed elements remaining in the initial stream and the semantic
action returning the resulting stream together with the normal result,
which allow natural limited backtrack but have the drawback that it is
not easy to find the position of parsing errors when they happen.

Parsers of lazy+imperative streams, which are described here, use a
method named "recursive descendent": they look at the first element,
they decide what to do in function of its value, and continue the
parsing with the remaining elements. Parsers can call other parsers,
and can be recursive, like normal functions.

Actually, parsers are just pure syntactic sugar. When writing a parser
in the syntax of the parser, Camlp5 transforms them into normal call
to functions, use of patterns matchings and try..with statements.  The
pretty printer of Camlp5, by default, displays this expanded result,
without syntax of parsers. A pretty printing kit, when added, can
rebuild the parsers in their initial syntax and display it.

Syntax
======

The syntax of the parsers, when loading "pa_rp.cmo" (or already
  included in the command "camlp5r"), is the following:

::

            expression ::= parser
                         | match-with-parser
                parser ::= "parser" pos-opt "[" parser-cases "]"
                         | "parser" pos-opt parser-case
     match-with-parser ::= "match" expression "with" parser
          parser-cases ::= parser-cases parser-case
                         | <nothing>
           parser-case ::= "[:" stream-pattern ":]" pos-opt "->" expression
        stream-pattern ::= stream-patt-comp
                         | stream-patt-comp ";" stream-patt-cont
                         | "let" LIDENT "=" expression "in" stream-pattern
                         | <nothing>
      stream-patt-cont ::= stream-patt-comp-err
                         | stream-patt-comp-err ";" stream-patt-cont
                         | "let" LIDENT "=" expression "in" stream-patt-cont
  stream-patt-comp-err ::= stream-patt-comp
                         | stream-patt-comp "?" expression
                         | stream-patt-comp "!"
      stream-patt-comp ::= "`" pattern
                         | "`" pattern "when" expression
                         | "?=" lookaheads
                         | pattern "=" expression
                         | pattern
            lookaheads ::= lookaheads "|" lookahead
                         | lookahead
             lookahead ::= "[" patterns "]"
              patterns ::= patterns pattern
                         | pattern
               pos-opt ::= pattern
                         | <nothing>

Streams
=======

The parsers are functions taking streams as parameter. Streams are are
values of type ``Stream.t a`` for some type ``a<``. It is possible to
build streams using the functions defined in the module
``Stream``:

Stream.from
-----------

``Stream.from f`` returns a stream built from the function ``f``. To
create a new stream element, the function ``f`` is called with the
current stream count, starting with zero. The user function ``f`` must
return either ``Some <value>`` for a value or ``None`` to specify the
end of the stream.

Stream.of_list
--------------

Return a stream built from the list in the same order.

Stream.of_string
----------------

Return a stream of the characters of the string parameter.

Stream.of_channel
-----------------

Return a stream of the characters read from the input channel
parameter.

Semantics of parsers
====================

Parser
------

A parser, defined with the syntax "parser" above, is of type
``Stream.t a -> b`` where ``a`` is the type of the elements
of the streams and ``b`` the type of the result. The parser cases are
tested in the order they are defined until one of them applies. The
result is the semantic action of the parser case which applies. If no
parser case applies, the exception ``Stream.Failure`` is
raised.

When testing a parser case, if the first stream pattern component
matches, all remaining stream pattern components of the stream pattern
must match also. If one does not match, the parser raises the
exception ``Stream.Error`` which has a parameter of type
string: by default, this string is the empty string, but if the stream
pattern component which does not match is followed by a question mark
and an expression, this expression is evaluated and given as parameter
to ``Stream.Error``.

In short, a parser can return with three ways:

- A normal result, of type ``b`` for a parser of type ``Stream.t a -> b``.
- Raising the exception ``Stream.Failure``.
- Raising the exception ``Stream.Error``.

Fundamentally, the exception ``Stream.Failure`` means "this
parser does not apply and no element have been removed from the
initial stream". This is a normal case when parsing: the parser
locally fails, but the parsing can continue.

Conversely, the exception ``Stream.Error`` means that "this
parser encountered a syntax error and elements have probably been
removed from the stream". In this case, there is no way to recover the
parsing, and it definitively fails.

Left factorization
------------------

In parsers, *consecutive* rules starting with the same components are
left factorized. It means that they are transformed into one only rule
starting with the common path, and continuing with a call to a parser
separating the two cases. The order is kept, except that the possible
empty rule is inserted at the end.

For example, the parser:::

  parser
  [ [: `If; e1 = expr; `Then; e2 = expr; `Else; e3 = expr :] -> f e1 e2 e3
  | [: `If; e1 = expr; `Then; e2 = expr :] -> g e1 e2 ]

is transformed into:::

  parser
    [: `If; e1 = expr; `Then; e2 = expr;
       a =
         parser
         [ [: `Else; e3 = expr :] -> f e1 e2 e3
         | [: :] -> g e1 e2 ] :] -> a

The version where rules are inverted:::

  parser
  [ [: `If; e1 = expr; `Then; e2 = expr :] -> g e1 e2
  | [: `If; e1 = expr; `Then; e2 = expr; `Else; e3 = expr :] -> f e1 e2 e3 ]

is transformed into the same parser.

Notice that:

- Only *consecutive* rules are left factorized. In the following parser:

::

  parser
  [ [: `If; e1 = expr; `Then; e2 = expr; `Else; e3 = expr :] -> ...
  | [: a = b :] -> a
  | [: `If; e1 = expr; `Then; e2 = expr :] -> ... ]

the two rules starting with ```If`` are not left factorized,
and the second ```If`` rule will never work.

- The components which are not *identical* are not factorized. In the following parser:

::

  parser
  [ [: `If; e1 = expr; `Then; e2 = expr; `Else; e3 = expr :] -> ...
  | [: `If; e4 = expr; `Then; e2 = expr :] -> ... ]

only the first component, ```If`` is factorized, the second one being
different because of different patterns (``e1`` and ``e4``).


Match with parser
-----------------

The syntax ``match expression with parser`` allows to match a stream
against a parser. It is, for ``parser``, the equivalent of ``match
expression with`` for ``fun``. The same way we could say:::

  match expression with ...

could be considered as an equivalent to:::

  (fun ...) expression

we could consider that:::

  match expression with parser ...

is an equivalent to:::

  (parser ...) expression

Error messages
--------------

A ``Stream.Error`` exception is raised when a stream pattern component
does not match and that it is not the first one of the parser
case. This exception has a parameter of type ``string``, useful to specify
the error message. By default, this is the empty string. To specify an
error message, add a question mark and an expression after the stream
pattern component. A typical error message is "that stream pattern
component expected".  Example with the parser of ``if..then..else..``
above:::


  parser
    [: `If; e1 = expr ? "expression expected after 'if'";
       `Then ? "'then' expected";
       e2 = expr ? "expression expected after 'then'";
       a =
         parser
         [ [: `Else; e3 = expr ? "expression expected" :] -> f e1 e2 e3
         | [: :] -> g e1 e2 ] :] -> a


Notice that the expression after the question mark is evaluated only
in case of syntax error. Therefore, it can be a complicated call to a
complicated function without slowing down the normal parsing.


Stream pattern component
------------------------

In a stream pattern (starting with ``[:`` and ending with
``:]``), the stream pattern components are separated with
the semicolon character. There are three cases of stream pattern
components with some sub-cases for some of them, and an extra syntax
can be used with a ``let..in`` construction. The three cases are:

- A direct test of one or several stream elements (called **terminal**
  symbol), in three ways:

  - The character "backquote" followed by a pattern, meaning: if the
    stream starts with an element which is matched by this pattern,
    the stream pattern component matches, and the stream element is
    removed from the stream.

  - The character "backquote" followed by a pattern, the keyword
    ``when`` and an expression of type ``bool``, meaning: if
    the stream starts with an element which is matched by this pattern
    and if the evaluation of the expression is ``True``,
    the stream pattern component matches, and the first element of the
    stream is removed.

  - The character "question mark" followed by the character "equal"
    and a lookahead expression (see further), meaning: if the
    lookahead applies, the stream pattern component matches. The
    lookahead may unfreeze one or several elements on the stream, but
    does not remove them.

- A pattern followed by the "equal" sign and an expression of type
  ``Stream.t x -> y`` for some types ``x`` and
  ``y``. This expression is called a **non terminal**
  symbol. It means: call the expression (which is a parser) with the
  current stream. If this sub-parser:

  - Returns an element, the pattern is bound to this result and the
    next stream pattern component is tested.

  - Raises the exception ``Stream.Failure``, there are two cases:

    - if the stream pattern component is the first one of the stream
      case, the current parser also fails with the exception
      ``Stream.Failure``.

    - if the stream pattern component is not the first one of the
      stream case, the current parser fails with the exception
      ``Stream.Error``.


    In this second case:

    - If the stream pattern component is followed by a "question mark"
      and an expression (which must be of type ``string``),
      the expression is evaluated and given as parameter of the
      exception ``Stream.Error``.

    - If the expression is followed by an "exclamation mark", the test
      and conversion from ``Stream.Failure`` to
      ``Stream.Error`` is not done, and the parser just
      raises ``Stream.Failure`` again. This is an
      optimization which must be assumed by the programmer, in general
      when he knows that the sub-parser called never raises
      ``Stream.Failure`` (for example if the called parser
      ends with a parser case containing an empty stream pattern). See
      "no error optionization" below.

    - Otherwise the exception parameter is the empty string.

- A pattern, which is bound to the current stream.


Notice that patterns are bound immediately and can be used in the next
stream pattern component.

Let statement
-------------

Between stream pattern components, it is possible to use the ``let..in``
construction. This is not considered as a real stream pattern
component, in the fact that is is not tested against the exception
``Stream.Failure`` it may raise. It can be useful for
intermediate computation. In particular, it is used internally by the
lexers (see chapter about  :ref:`lexers` as character stream parsers).

Example of use, when an expression have to be used several times (in
the example, ``d a``, which is bound to the variable
``c``):::

  parser
    [: a = b;
       let c = d a in
       e =
         parser
         [ [: f = g :] -> h c
         | [: :] -> c ] :] -> e


Lookahead
---------

The lookahead feature allows to look at several terminals in the
stream without removing them, in order to take decisions when more
than one terminal is necessary.

For example, when parsing the normal syntax of the OCaml language,
there is a problem, in recursing descendent parsing, for the cases
where to treat and differentiate the following inputs:::

  (-x+1)
  (-)

The first case is treated in a rule, telling: "a left parenthesis,
followed by an expression, and a right parenthesis". The second one is
"a left parenthesis, an operator, a right parenthesis". Programming it
like this (left factorizing the first parenthesis):::

  parser
    [: `Lparen;
       e =
         parser
         [ [: e = expr; `Rparen :] -> e
         | [: `Minus; `Rparen :] -> minus_op ] :] -> e

does not work if the input is ``(-)`` because the rule ``e = expr``
accepts the minus sign as expression start, removing it from the input
stream and fails as parsing error, while encountering the right
parenthesis.

Conversely, writing it this way:::

  parser
    [: `Lparen;
       e =
         parser
         [ [: `Minus; `Rparen :] -> minus_op
         | [: e = expr; `Rparen :] -> e ] :] -> e

does not help, because if the input is ``(-x+1)`` the rule
above starting with `` `Minus`` is accepted and the
exception ``Stream.Error`` is raised while encountering the
variable ``x`` since a right parenthesis is expected.

In general, this kind of situation is best resolved by a left
factorization of the parser cases (see the section "Semantics" above),
but that is not possible in this case. The solution is to test whether
the character after the minus sign is a right parenthesis:::

  parser
    [: `Lparen;
       e =
         parser
         [ [: ?= [ _ Rparen ]; `Minus; `Rparen :] -> minus_op
         | [: e = expr; `Rparen :] -> e ] :] -> e

It is possible to put several lists of patterns separated by a
vertical bar in the lookahead construction, but with a limitation (due
to the implementation): all lists of patterns must have the same
number of elements.

No error optimization
---------------------

The "no error optimization" is the fact to end a stream pattern
component of kind "non-terminal" ("pattern" "equal" "expression") by
the character "exclamation mark". Like said above, this inhibits the
transformation of the exception ``Stream.Failure``,
possibly raised by the called parser, into the exception
``Stream.Error``.

The code:::

  parser [: a = b; c = d ! :] -> e

is equivalent to:::

  parser [: a = b; s :] -> let c = d s in e

One interest of the first syntax is that it shows to readers that
``d`` is indeed a syntactic sub-parser. In the second syntax, it is
called in the semantic action, which makes the parser case not so
clear, as far as readability is concerned.

If the stream pattern component is at end of the stream pattern, this
allow possible tail recursion by the OCaml compiler, in the following
case:::

  parser [: a = b; c = d ! :] -> c

since it is equivalent (with the fact that ``c`` is at the
same time the pattern of the last case and the expression of the
parser case semantic action) to:::

  parser [: a = b; s :] -> d s

The call to ``d s`` can be a tail recursive call. Without the use of
the "exclamation mark" in the rule, the equivalent code is:::

  parser [: a = b; s :] ->
    try d s with [ Stream.Failure -> raise (Stream.Error "") ]

which is not tail recursive (due to the ``try..with`` construction
pushes a context), preventing the compiler to optimize its code. This
can be important when many recursive calls happen, since it can
overflow the OCaml stack.

Position
--------

The optional "pattern" before and after a stream pattern is bound to
the current stream count. Indeed, streams internally contain a count
of their elements. At the beginning the count is zero. When an element
is removed, the count is incremented. The example:::

  parser [: a = b :] ep -> c

is equivalent to:::

  parser [: a = b; s :] -> let ep = Stream.count s in c

There is no direct syntax equivalent to the optional pattern at
beginning of the stream pattern:::

  parser bp [: a = b :] -> c

These optional patterns allow disposal of the stream count at the
beginning and at the end of the parser case, allowing to compute
locations of the rule in the source. In particular, if the stream is a
stream of characters, these counts are the source location in number
of characters.

Semantic action
---------------

In a parser case, after the stream pattern, there is an "arrow" and an
expression, called the "semantic action". If the parser case is
matched the parser returns with the evaluated expression whose
environment contains all values bound in the stream pattern.

Remarks
=======

Simplicity vs Associativity
---------------------------

This parsing technology has the advantage of simplicity of use and
understanding, but it does not treat the associativity of
operators. For example, if you write a parser like this (to compute
arithmetic expressions):::

  value rec expr =
    parser
    [ [: e1 = expr; `'+'; e2 = expr :] -> e1 + e2
    | [: `('0'..'9' as c) :] -> Char.code c - Char.code '0' ]

this would loop endlessly, exactly as if you wrote code starting with:::

  value rec expr e =
    let e1 = expr e in
    ...

One solution is to treat the associativity "by hand": by reading a
sub-expression, then looping with a parser which parses the operator
and another sub-expression, and so on.

An alternative solution is to write parsing "combinators". Indeed,
parsers being normal functions, it is possible to make a function
which takes a parser as parameter and returning a parser using it. For
example, left and right associativity parsing combinators:::

  value rec left_assoc op elem =
    let rec op_elem x =
      parser
      [ [: t = op; y = elem; r = op_elem (t x y) :] -> r
      | [: :] -> x ]
    in
    parser [: x = elem; r = op_elem x :] -> r
  ;

  value rec right_assoc op elem =
    let rec op_elem x =
      parser
      [ [: t = op; y = elem; r = op_elem y :] -> t x r
      | [: :] -> x ]
    in
    parser [: x = elem; r = op_elem x :] -> r
  ;

which can be used, e.g. like this:::

  value expr =
    List.fold_right (fun op elem -> op elem)
      [left_assoc (parser [: `'+' :] -> fun x y -> x +. y);
       left_assoc (parser [: `'*' :] -> fun x y -> x *. y);
       right_assoc (parser [: `'^' :] -> fun x y -> x ** y)]
      (parser [: `('0'..'9' as c) :] -> float (Char.code c - Char.code '0'))
  ;

and tested, e.g. in the toplevel, like that:::

  expr (Stream.of_string "2^3^2+1");

The same way, it is possible to parse non-context free grammars, by
programming parsers returning other parsers.

A third solution, to resolve the problem of associativity, is to use
the grammars of Camlp5, which have the other advantage that they are
extensible.

Lexing vs Parsing
-----------------

In general, while analyzing a language, there are two levels:

- The level where the input, considered as a stream of characters, is
  read to make a stream of tokens (for example "words", if it is a
  human language, or punctuation). This level is generally called
  "lexing".

- The level where the input is a stream of tokens where grammar rules
  are parsed. This level is generally called "parsing".

The "parser" construction described here can be used for both, thanks
to the polymorphism of OCaml:

- The lexing level is a "parser" of streams of characters returning
  tokens.
- The parsing level is a "parser" of streams of tokens returning
  syntax trees.

By comparison, the programs "lex" and "yacc" use two different
technologies. With "parser"s, it is possible to use the same one for
both.

Lexer syntax vs Parser syntax
-----------------------------

For "lexers", i.e. for the specific case of parsers when the input is
a stream of characters, it is possible to use a shorter syntax. See
the chapter on  :ref:`lexers`. They have another
syntax, shorter and adapted for the specific type
``char``. But they still are internally parsers of streams
with the same semantics.

Purely functional parsers
-------------------------

This system of parsers is imperative: while parsing, the stream
advances and the already parsed terminals disappear from the stream
structure. This is useful because it is not necessary to return the
remaining stream together with the normal result. This is the reason
there is this ``Stream.Error`` exception: when it is raised, it
means that some terminals have been consumed from the stream, which
are definitively lost, and therefore that are no more possible parser
cases to try.

An alternative is to use :ref:`functional-parsers` which use a new
stream type, lazy but not destructive. Their advantage is that they
use a limited backtrack: the case of ``if..then..else..`` and the
shorter ``if..then..`` work without having to left factorize the parser
cases, and there is no need to lookahead. They have no equivalent to
the exception ``Stream.Error``: when all cases are tested,
and have failed, the parsers return the value ``None``. The
drawback is that, when a parsing error happens, it is not easily
possible to know the location of the error in the input, as the
initial stream has not been modified: the system would indicate a
failure at the first character of the first line: this is a general
drawback of backtracking parsers. See the solutions found to this
problem in the chapter about :ref:`functional-parsers`.

A second alternative is to use the :ref:`backtracking-parsers`. They
use the same stream type as the functional parsers, but they test more
cases than them. They have the same advantages and drawbacks than the
functional parsers.

.. _lexers:

*************
Stream lexers
*************

The file ``pa_lexer.cmo`` is a Camlp5 syntax extension kit for parsers
of streams of the type ``char``. This syntax is shorter and more
readable than its equivalent version written with
:ref:`stream-parsers`. Like classical parsers, they use recursive
descendant parsing. They are also pure syntax sugar, and each lexer
written with this syntax can be written using normal parsers syntax.

(An old version, named ``pa_lex.cmo`` was provided before with a
different syntax. It is no longer distributed, its proposed syntax
being confusing.)

Introduction
============

Classical parsers in OCaml apply to streams of any type of values. For
the specific type ``char``, it has been possible to shorten the encoding
in several ways, in particular by using strings to group several
characters together, and by hiding the management of a "lexing
buffer", a data structure recording the matched characters.

Let us take an example. The following function parses a left bracket
followed by a less, a colon or nothing, and record the result in a
buffer. In classical parsers syntax, this could be written like this:

::

  fun buf ->
    parser
    [ [: `'['; `'<' :] ->
        Plexing.Lexbuf.add '<' (Plexing.Lexbuf.add '[' buf)
    | [: `'['; `':' :] ->
        Plexing.Lexbuf.add ':' (Plexing.Lexbuf.add '[' buf)
    | [: `'[' :] ->
        Plexing.Lexbuf '[' buf ]


With the new syntax, it is possible to write it as:

::

  lexer [ "[<" | "[:" | "[" ]


The two codes are strictly equivalent, but the lexer version is easier
to write and understand, and is much shorter.

Syntax
======

When loading the syntax extension ``pa_lexer.cmo``, the OCaml syntax
is extended as follows:

::
   
          expression ::= lexer
               lexer ::= "lexer" "[" rules "]"
               rules ::= ne-rules rule
                       | <nothing>
            ne-rules ::= ne-rules "|" rule
                       | rule
                rule ::= symbols [ "->" action ]
             symbols ::= symbols symbol err
                       | <nothing>
              symbol ::= "_" no-record-opt
                       | CHAR no-record-opt
                       | CHAR "-" CHAR no-record-opt
                       | STRING no-record-opt
                       | simple-expression
                       | "?=" "[" lookaheads "]"
                       | "[" rules "]"
       no-record-opt ::= "/"
                       | <nothing>
   simple-expression ::= LIDENT
                       | "(" <expression> ")"
          lookaheads ::= lookaheads "|" lookahead-sequence
                       | lookahead-sequence
  lookahead-sequence ::= lookahead-symbols
                       | STRING
   lookahead-symbols ::= lookahead-symbols lookahead-symbol
                       | lookahead-symbol
    lookahead-symbol ::= CHAR
                       | CHAR "-" CHAR
                       | "_"
                 err ::= "?" simple-expression
                       | "!"
                       | <nothing>
              action ::= expression


The identifiers ``STRING``, ``CHAR`` and ``LIDENT`` above represent
the OCaml tokens corresponding to string, character and lowercase
identifier (identifier starting with a lowercase character).

Moreover, together with that syntax extension, another extension is
added the entry ``expression``, typically for the semantics
actions of the ``lexer`` statement above, but not only. It is:

::

  expression ::= "$" "add" STRING
               | "$" "buf"
               | "$" "empty"
               | "$" "pos"

Remark: the identifiers ``add``, ``buf``, ``empty`` and ``pos`` are
not keywords (they are not reserved words) but just identifiers. On
the contrary, the identifier ``lexer``, which introduces the syntax,
is a new keyword and cannot be used as variable identifier any more.

Semantics
=========

A lexer defined in the syntax above is a shortcut version of a parser
applied to the specific case of streams of characters. It could be
written with a normal parser. The proposed syntax is much shorter,
easier to use and to understand, and silently takes care of the lexing
buffer for the programmer. The lexing buffers are data structures,
which are passed as parameters to called lexers and returned by them.

Our lexers are of the type:

::

  Plexing.Lexbuf.t -> Stream.t char -> u

where ``u`` is a type which depends on what the lexer returns. If
there is no semantic action (since it it optional), this type is
automatically ``Plexing.Lexbuf.t`` also.

A lexer is, actually, a function with two implicit parameters: the
first one is the lexing buffer itself, and the second one the
stream. When called, it tries to match the stream against its first
rule. If it fails, it tries its second rule, and so on, up to its last
rule. If the last rule fails, the lexer fails by raising the exception
``Stream.Failure``. All of this is the usual behaviour of
:ref:`stream-parsers`.

In a rule, when a character is matched, it is inserted into the lexing
buffer, except if the "no record" feature is used (see further).

Rules which have no semantic action return the lexing buffer itself.

Symbols
-------

The different kinds or symbols in a rule are:

- The token "underscore", which represents any character. Fails only
  if the stream is empty.
- A character which represents a matching of this character.
- A character followed by the minus sign and by another character
  which represent all characters in the range between the two
  characters in question.
- A string with represents a matching of all its characters, one after
  the other.
- An expression corresponding to a call to another lexer, which takes
  the buffer as first parameter and returns another lexing buffer with
  all characters found in the stream added to the initial lexing
  buffer.
- The sequence ``?=`` introducing lookahead characters.
- A rule, recursively, between brackets, inlining a lexer.

In the cases matching characters (namely underscore, character,
characters range and string), the symbol can be optionally followed by
the "no record" character "slash" specifying that the found
character(s) are not added into the lexing buffer. By default, they
are. This feature is useful, for example, writing a lexer which parses
strings, when the initial double quote and final double quote should
not be part of the string itself.

Moreover, a symbol can be followed by an optional error indicator,
which can be:

- The character ``?`` (question mark) followed by a string expression,
  telling that, if there is a syntax error at this point (i.e. the
  symbol is not matched although the beginning of the rule was), the
  exception ``Stream.Error`` is raised with that string as
  parameter. Without this indicator, it is raised with the empty
  string. This is the same behaviour than with classical
  :ref:`stream-parsers`.
- The character ``!`` (exclamation mark), which is just an indicator
  to let the syntax expander optimize the code. If the programmer is
  sure that the symbol never fails (i.e. never raises
  ``Stream.Failure``), in particular if this symbol recognizes the
  empty rule, he can add this exclamation mark. If it is used
  correctly (the compiler cannot check it), the behaviour is identical
  as without the ``!``, except that the code is shorter and faster,
  and can sometimes be tail recursive. If the indication is not
  correct, the behaviour of the lexer is undefined.


Specific expressions
--------------------

When loading this syntax extension, the entry
``<expression>``, at level labelled ``"simple"`` of the OCaml
language is extended with the following rules:

- ``$add`` followed by a string, specifing that the programmer wants
  to add all characters of the string in the lexing buffer. It returns
  the new lexing buffer. It corresponds to an iteration of calls to
  ``Plexing.Lexbuf.add`` with all characters of the string with the
  current lexing buffer as initial parameter.
- ``$buf`` which returns the lexing buffer converted into string.
- ``$empty`` which returns an empty lexing buffer.
- ``$pos`` which returns the current position of the stream in number
  of characters (starting at zero).


Lookahead
---------

Lookahead is useful in some cases, when factorization of rules is
impossible. To understand how it is useful, a first remark must be
done, about the usual behaviour of Camlp5 stream parsers.

Stream parsers (including these lexers) use a limited parsing
algorithm, in a way that when the first symbol of a rule is matched,
all the following symbols of the same rule must apply, otherwise it is
a syntax error. There is no backtrack. In most of the cases, left
factorization of rules resolve conflicting problems. For example, in
parsers of tokens (which is not our case here, since we parse only
characters), when one writes a parser to recognize both typical
grammar rules ``if..then..else`` and the shorter ``if..then..``, the
system transforms them into a single rule starting with ``if..then..``
followed by a call to a parser recognizing ``else..`` *or* nothing.

Sometimes, however, this left factorization is not possible. A
lookahead of the stream to check the presence of some elements (these
elements being characters, if we are using this "lexer" syntax) might
be necessary to decide if is a good idea to start the rule. This
lookahead feature may unfreeze several characters from the input
stream but without removing them.

Syntactically, a lookahead starts with ``?=`` and is followed by
one or several lookahead sequences separated by the vertical bar
``|``, the whole list being enclosed by braces.

If there are several lookaheads, they must all be of the same size
(contain the same number of characters).

If the lookahead sequence is just a string, it corresponds to all
characters of this string in the order (which is different for strings
outside lookahead sequences, representing a choice of all characters).

Examples of lookaheads:

::

  ?= [ _ ''' | '\\' _ ]
  ?= [ "<<" | "<:" ]

The first line above matches a stream whose second character is a
quote or a stream whose first character is a backslash (real example
in the lexer of OCaml, in the library of Camlp5, named
"plexer.ml"). The second line matches a stream starting with the two
characters ``<`` and ``<`` or starting with the two characters ``<``
and ``:`` (this is another example in the same file).

Semantic actions of rules
-------------------------

By default, the result of a "lexer" is the current lexing buffer,
which is of type ``Plexing.Lexbuf.t``. But it is possible to return
other values, by adding ``->`` at end of rules followed by the
expression you want to return, as in usual pattern matching in OCaml.

An interesting result, for example, could be the string corresponding
to the characters of the lexing buffer. This can be obtained by
returning the value ``$buf``.

A complete example
------------------

A complete example can be seen in the sources of Camlp5,
file ``lib/plexer.ml``. This is the lexer of OCaml, either "normal"
or"revised" syntax.

Compiling
---------

To compile a file containing lexers, just load ``pa_lexer.cmo`` using
one of the following methods:

- Either by adding ``pa_lexer.cmo`` among the Camlp5 options. See the
  Camlp5 manual page or documentation.
- Or by adding ``#load "pa_lexer.cmo";`` anywhere in the file, before
  the usages of this "lexer" syntax.

How to display the generated code
---------------------------------

You can see the generated code, for a file ``bar.ml`` containing
lexers, by typing in a command line:

::

  camlp5r pa_lexer.cmo pr_r.cmo bar.ml

To see the equivalent code with stream parsers, use:

::

  camlp5r pa_lexer.cmo pr_r.cmo pr_rp.cmo bar.ml

.. _functional-parsers:

******************
Functional parsers
******************

Purely functional parsers are an alternative of :ref:`stream-parsers`
where the used stream type is a lazy non-destructive type. These
streams are lazy values, as in classical stream parsers, but the
values are not removed as long as the parsing advances.

To make them work, the parsers of purely functional streams return,
not the simple values, but a value of type option :
``None`` meaning "no match" (the equivalent of the
exception ``Parse.Failure`` of normal streams) and
``Some (r, s)`` meaning "the result is r and the remaining
stream is s".

Syntax
======

The syntax of purely functional parsers, when loading
``pa_fstream.cmo``, is the following:

::

          expression ::= fparser
                       | match-with-fparser
             fparser ::= "fparser" pos-opt "[" parser-cases "]"
                       | "fparser" pos-opt parser-case
  match-with-fparser ::= "match" expression "with" fparser
        parser-cases ::= parser-cases parser-case
                       | <nothing>
         parser-case ::= "[:" stream-pattern ":]" pos-opt "->" expression
                       | "[:" ":]" pos-opt "->" expression
      stream-pattern ::= stream-patt-comp
                       | stream-patt-comp ";" stream-pattern
    stream-patt-comp ::= "`" pattern
                       | "`" pattern "when" expression
                       | pattern "=" expression
                       | pattern
                       | "when" expression
             pos-opt ::= pattern
                       | <nothing>


Notice that, unlike classical parsers, there is no difference, in a
stream pattern, between the first stream pattern component and the
other ones. In particular, there is no "question mark" syntax and
expression optionnally ending those components. Moreover, the
"lookahead" case is not necessary, we see further why. The syntaxes
"pattern when" and "let..in" inside stream patterns we see in
classical parsers are not implemented.

Streams
=======

The functional parsers are functions taking as parameters functional
streams, which are values of type ``Fstream.t a`` for some type
``a``. It is possible to build functional streams using the functions
defined in the module ``Fstream``:

Fstream.from
------------

``Fstream.from f`` returns a stream built from the function ``f``. To
create a new stream element, the function ``f`` is called with the
current stream count, starting with zero. The user function ``f`` must
return either ``Some <value>`` for a value or ``None`` to specify the
end of the stream.

Fstream.of_list
---------------

Return a stream built from the list in the same order.

Fstream.of_string
-----------------

Return a stream of the characters of the string parameter.

Fstream.of_channel
------------------

Return a stream of the characters read from the input channel
parameter.

Semantics of parsers
====================

Fparser
-------

The purely functional parsers act like classical parsers, with a
recursive descent algorithm, except that:

- If the first stream pattern component matches the beginning of the
  stream, there is no error if the following stream patterns
  components do not match: the control simply passes to the next
  parser case with the initial stream.
- If the semantic actions are of type ``t``, the result of the parser
  is of type ``option (t * Fstream.t)``, not just ``t`` like in
  classical parsers. If a stream pattern matches, the semantic action
  is evaluated, giving some result ``e`` and the result of the parser
  is ``Some (e, strm)`` where ``strm`` is the remaining stream.
- If no parser case matches, the result of the parser is ``None``.


Error position
--------------

A difficulty, with purely functional parsers, is how to find the
position of the syntax error, when the input is wrong. Since the
system tries all parsers cases before returning ``None``, and that the
initial stream is not affected, it is not possible to directly find
where the error happened. This is a problem for parsing using
backtracking (here, it is limited backtracking, but the problem is the
same).

The solution is to use the function ``Fstream.count_unfrozen``
applied to the initial stream. Like its name says, it returns the
number of unfrozen elements of the stream, which is exactly the
longest match found. If the input is a stream of characters, the
return of this function is exactly the position in number of
characters from the beginning of the stream.

However, it is not possible to know directly which rule failed and
therefore it is not possible, as in classical parsers, to specify and
get clear error messages. Future versions of purely functional parsers
may propose solutions to resolve this problem.

Notice that, if using the ``count_unfrozen`` method, it is not
possible to reuse that same stream to call another parser, and hope to
get the right position of the error, if another error happens, since
it may test less terminals than the first parser. Use a fresh stream
in this case, if possible.

.. _backtracking-parsers:

********************
Backtracking parsers
********************

Backtracking parsers are a second alternative of
:ref:`stream-parsers` and :ref:`functional-parsers`.

Backtracking parsers are close to functional parsers: they use the
same stream type, ``Fstream.t``, and their syntax is almost
identical, its introducing keyword being ``bparser`` instead of
``fparser``.

The difference is that they are implemented with *full
backtracking* and that they return values of the type ``option``
of the triplet: 1/ value, 2/ remaining stream and 3/ continuation.

Syntax
======

The syntax of backtracking parsers is added together with the syntax
of functional parsers, when the kit ``pa_fstream.cmo`` is loaded. It is:

::

          expression ::= bparser
                       | match-with-bparser
             bparser ::= "bparser" pos-opt "[" parser-cases "]"
                       | "bparser" pos-opt parser-case
  match-with-bparser ::= "match" expression "with" bparser
        parser-cases ::= parser-cases parser-case
                       | <nothing>
         parser-case ::= "[:" stream-pattern ":]" pos-opt "->" expression
                       | "[:" ":]" pos-opt "->" expression
      stream-pattern ::= stream-patt-comp
                       | stream-patt-comp ";" stream-pattern
    stream-patt-comp ::= "`" pattern
                       | "`" pattern "when" expression
                       | pattern "=" expression
                       | pattern
                       | "when" expression
             pos-opt ::= pattern
                       | <nothing>


Semantics
=========

Algorithm
---------

The backtracking parsers, like classical parsers and functional
parsers, use a recursive descent algorithm. But:

- If a stream pattern component does not match the current position of
  the input stream, the control is given to the next case of the
  stream pattern component before it. If it is the first stream
  pattern component, the rule (the stream pattern) is left and the
  next rule is tested.


For example, the following grammar:

::

   E -> X Y
   X -> a b | a
   Y -> b

works, with the backtracking algorithm, for the input ``a  b``.

Parsing with the non-terminal ``E``, the non-terminal ``X`` first
accepts the input ``a b`` with its first rule. Then when ``Y`` is
called, the parsing fails since nothing remains in the input stream.

In the rule ``X Y`` of the non-terminal ``E``, the non-terminal ``Y``
having failed, the control is given the the continuation of the
non-terminal ``X``. This continuation is its second rule containing
only ``a``. Then ``Y`` is called and accepted.

This case does not work with functional parsers since when the rule
``a b`` of the non-terminal ``X`` is accepted, it is definitive. If
the input starts with ``a b``, there is no way to apply its second
rule.

Backtracking parsers are strictly more powerful than functional
parsers.

Type
----

A backtracking parser whose stream elements are of type ``t1``, and
whose semantic actions are of some type ``t2``, is of type:

::

   Fstream.t t1 -> option (t * Fstream.t t1 * Fstream.kont t1 t2)


If the backtracking parsers fails, its returning value is ``None``.

If it succeeds, its returning value is ``Some (x, strm, k)`` where
``x`` is its result, ``strm`` the remaining stream, and ``k`` the
continuation.

The continuation is internally used in the backtracking algorithm, but
is can also be used in the main call to compute the next solution,
using the function ``Fstream.bcontinue``.

It is also possible to directly get the list of all solutions by
calling the function ``Fstream.bparse_all``.

Syntax errors
-------------

Like for :ref:`functional-parsers`, in case of syntax error, the error
position can be found by using the function
``Fstream.count_unfrozen``, the token in error being the last unfrozen
element of the stream.

A syntax error is not really an error: for the backtracking parsers,
like for functional parsers, it is viewed as a "non-working" case and
another solution is searched.

In the backtracking algorithm, depending on the grammar and the input,
the search of the next solution can be very long. A solution is
proposed for that in the :ref:`grammars` system when the parsing
algorithm is set to "backtracking".

Example
=======

Here is an example which just shows the backtracking algorithm but
without parsing, an empty stream being given as parameter and never
referred.

It creates a list of three strings, each of them being chosen between
``"A"``, ``"B"`` and ``"C"``.

The code is:

::

  #load "pa_fstream.cmo";
  value choice = bparser [ [: :] -> "A" | [: :] -> "B" | [: :] -> "C" ];
  value combine = bparser [: x = choice; y = choice; z = choice :] -> [x; y; z];

The function ``combine`` returns the first solution:

::

  # combine (fstream [: :]);
  - : option (list string * Fstream.t '_a * Fstream.kont '_a (list string)) =
  Some (["A"; "A"; "A"], <abstr>, Fstream.K <fun>)


The function ``Fstream.bparse_all`` returns the list of all solutions,
showing the interest of the backtracking:

::

  # Fstream.bparse_all combine (fstream [: :]);
  - : list (list string) =
  [["A"; "A"; "A"]; ["A"; "A"; "B"]; ["A"; "A"; "C"]; ["A"; "B"; "A"];
   ["A"; "B"; "B"]; ["A"; "B"; "C"]; ["A"; "C"; "A"]; ["A"; "C"; "B"];
   ["A"; "C"; "C"]; ["B"; "A"; "A"]; ["B"; "A"; "B"]; ["B"; "A"; "C"];
   ["B"; "B"; "A"]; ["B"; "B"; "B"]; ["B"; "B"; "C"]; ["B"; "C"; "A"];
   ["B"; "C"; "B"]; ["B"; "C"; "C"]; ["C"; "A"; "A"]; ["C"; "A"; "B"];
   ["C"; "A"; "C"]; ["C"; "B"; "A"]; ["C"; "B"; "B"]; ["C"; "B"; "C"];
   ["C"; "C"; "A"]; ["C"; "C"; "B"]; ["C"; "C"; "C"]]


.. _grammars:

*******************
Extensible grammars
*******************

This chapter describes the syntax and semantics of the extensible
grammars of Camlp5.

The extensible grammars are the most advanced parsing tool of
Camlp5. They apply to streams of characters using a lexer which has to
be previously defined by the programmer. In Camlp5, the syntax of the
OCaml language is defined with extensible grammars, which makes Camlp5
a bootstrapped system (it compiles its own features by itself).


Getting started
===============

The extensible grammars are a system to build *grammar entries*
which can be extended dynamically. A grammar entry is an abstract
value internally containing a stream parser. The type of a grammar
entry is ``Grammar.Entry.e t`` where ``t`` is the type
of the values returned by the grammar entry.

To start with extensible grammars, it is necessary to build a
*grammar*, a value of type ``Grammar.g``, using the function
``Grammar.gcreate``:

::

  value g = Grammar.gcreate lexer;

where ``lexer`` is a lexer previously defined. See the section
explaining the interface with lexers. In a first time, it is possible
to use a lexer of the module ``Plexer`` provided by Camlp5:

::

  value g = Grammar.gcreate (Plexer.gmake ());

Each grammar entry is associated with a grammar. Only grammar
entries of the same grammar can call each other. To create a grammar
entry, one has to use the function ``Grammar.Entry.create`` with
takes the grammar as first parameter and a name as second parameter. This
name is used in case of syntax errors. For example:

::

  value exp = Grammar.Entry.create g "expression";

To apply a grammar entry, the function ``Grammar.Entry.parse``
can be used. Its first parameter is the grammar entry, the second one
a stream of characters:

::

  Grammar.Entry.parse exp (Stream.of_string "hello");


But if you experiment this, since the entry was just created without
any rules, you receive an error message:

::

  Stream.Error "entry [expression] is empty"

To add grammar rules to the grammar entry, it is necessary to
*extend* it, using a specific syntactic statement:
``EXTEND``.

Syntax of the EXTEND statement
==============================

The ``EXTEND`` statement is added in the expressions of the OCaml
language when the syntax extension kit ``pa_extend.cmo`` is
loaded. Its syntax is:

::

    expression ::= extend
        extend ::= "EXTEND" extend-body "END"
   extend-body ::= global-opt entries
    global-opt ::= "GLOBAL" ":" entry-names ";"
                 | <nothing>
   entry-names ::= entry-name entry-names
                 | entry-name
         entry ::= entry-name ":" position-opt "[" levels "]"
  position-opt ::= "FIRST"
                 | "LAST"
                 | "BEFORE" label
                 | "AFTER" label
                 | "LIKE" string
                 | "LEVEL" label
                 | <nothing>
        levels ::= level "|" levels
                 | level
         level ::= label-opt assoc-opt "[" rules "]"
     label-opt ::= label
                 | <nothing>
     assoc-opt ::= "LEFTA"
                 | "RIGHTA"
                 | "NONA"
                 | <nothing>
         rules ::= rule "|" rules
                 | rule
          rule ::= psymbols-opt "->" expression
                 | psymbols-opt
  psymbols-opt ::= psymbols
                 | <nothing>
      psymbols ::= psymbol ";" psymbols
                 | psymbol
       psymbol ::= symbol
                 | pattern "=" symbol
        symbol ::= keyword
                 | token
                 | token string
                 | entry-name
                 | entry-name "LEVEL" label
                 | "SELF"
                 | "NEXT"
                 | "LIST0" symbol
                 | "LIST0" symbol "SEP" symbol opt-opt-sep
                 | "LIST1" symbol
                 | "LIST1" symbol "SEP" symbol opt-opt-sep
                 | "OPT" symbol
                 | "FLAG" symbol
                 | "V" symbol opt-strings
                 | "[" rules "]"
                 | "(" symbol ")"
   opt-opt-sep ::= "OPT_SEP"
                 | <nothing>
   opt-strings ::= string opt-strings
                 | <nothing>
       keyword ::= string
         token ::= uident
         label ::= string
    entry-name ::= qualid
        qualid ::= qualid "." qualid
                 | uident
                 | lident
        uident ::= 'A'-'Z' ident
        lident ::= ('a'-'z' | '_' | misc-letter) ident
         ident ::= ident-char*
    ident-char ::= ('a'-'a' | 'A'-'Z' | '0'-'9' | '_' | ''' | misc-letter)
   misc-letter ::= '\128'-'\255'


Other statements, ``GEXTEND``, ``DELETE_RULE``, ``GDELETE_RULE`` are
also defined by the same syntax extension kit. See further.

In the description above, only ``EXTEND`` and ``END`` are new keywords
(reserved words which cannot be used in variables, constructors or
module names). The other strings (e.g. ``GLOBAL``, ``LEVEL``,
``LIST0``, ``LEFTA``, etc.) are not reserved.

Semantics of the EXTEND statement
=================================

The EXTEND statement starts with the ``EXTEND`` keyword and ends with
the ``END`` keyword.

GLOBAL indicator
----------------

After the first keyword, it is possible to see the identifier
``GLOBAL`` followed by a colon, a list of entries names and a
semicolon. It says that these entries correspond to visible
(previously defined) entry variables, in the context of the EXTEND
statement, the other ones being locally and silently defined inside.

- If an entry, which is extended in the EXTEND statement, is in the
  GLOBAL list, but is not defined in the context of the EXTEND
  statement, the OCaml compiler will fail with the error "unbound
  value".
- If there is no GLOBAL indicator, and an entry, which is extended in
  the EXTEND statement, is not defined in the contex of the EXTEND
  statement, the OCaml compiler will also fail with the error "unbound
  value".

Example:

::

  value exp = Grammar.Entry.create g "exp";
  EXTEND
    GLOBAL: exp;
    exp: [ [ x = foo; y = bar ] ];
    foo: [ [ "foo" ] ];
    bar: [ [ "bar" ] ];
  END;


The entry ``exp`` is an existing variable (defined by ``value exp = ...``).
On the other hand, the entries ``foo`` and ``bar`` have not been
defined. Because of the ``GLOBAL`` indicator, the system define them
locally.

Without the GLOBAL indicator, the three entries would have been
considered as global variables, therefore the OCaml compiler would
say "unbound variable" under the first undefined entry, ``foo``.

Entries list
------------

Then the list of entries extensions follow. An entry extension
starts with the entry name followed by a colon. An entry may have
several levels corresponding to several stream parsers which call the
ones the others (see further).

Optional position
^^^^^^^^^^^^^^^^^

After the colon, it is possible to specify a where to insert the defined levels:

- The identifier ``FIRST`` (resp. ``LAST``) indicates that the level
    must be inserted before (resp. after) all possibly existing levels
    of the entry. They become their first (resp. last) levels.- The
    identifier ``BEFORE`` (resp. ``AFTER``) followed by a level label
    (a string) indicates that the levels must be inserted before
    (resp. after) that level, if it exists. If it does not exist, the
    extend statement fails at run time.
- The identifier ``LIKE`` followed by a string indicates that the
  first level defined in the extend statement must be inserted in the
  first already existing level with a rule containing this string as
  keyword or token name. For example, ``LIKE "match"`` is the first
  level having ``match`` as keyword. If there is no level with this
  string, the extend statement fails at run time.
- The identifier ``LEVEL`` followed by a level label indicates that
  the first level defined in the extend statement must be inserted at
  the given level, extending and modifying it. The other levels
  defined in the statement are inserted after this level, and before
  the possible levels following this level. If there is no level with
  this label, the extend statement fails at run time.
- By default, if the entry has no level, the levels defined in the
  statement are inserted in the entry. Otherwise the first defined
  level is inserted at the first level of the entry, extending or
  modifying it. The other levels are inserted afterwards (before the
  possible second level which may previously exist in the entry).

Levels
^^^^^^

After the optional *position*, the *level* list follow. The
levels are separated by vertical bars, the whole list being between
brackets.

A level starts with an optional label, which corresponds to its
name. This label is useful to specify this level in case of future
extensions, using the *position* (see previous section) or for
possible direct calls to this specific level.

The level continues with an optional associativity indicator, which
can be:

- LEFTA for left associativity (default),
- RIGHTA for right associativity,
- NONA for no associativity.

Rules
^^^^^

At last, the grammar *rule* list appear. The rules are
separated by vertical bars, the whole list being brackets.

A rule looks like a match case in the ``match`` statement or a parser
case in the ``parser`` statement: a list of psymbols (see next
paragraph) separated by semicolons, followed by a right arrow and an
expression, the semantic action. Actually, the right arrow and
expression are optional: in this case, it is equivalent to an
expression which would be the unit ``()`` constructor.

A psymbol is either a pattern, followed with the equal sign and a
symbol, or by a symbol alone. It corresponds to a test of this symbol,
whose value is bound to the pattern if any.

Symbols
-------

A symbol is an item in a grammar rule. It is either:

- a keyword (a string): the input must match this keyword,
- a token name (an identifier starting with an uppercase character),
  optionally followed by a string: the input must match this token
  (any value if no string, or that string if a string follows the
  token name), the list of the available tokens depending on the
  associated lexer (the list of tokens available with "Plexer.gmake
  ()" is: LIDENT, UIDENT, TILDEIDENT, TILDEIDENTCOLON, QUESTIONIDENT,
  INT, INT_l, INT_L, INT_n, FLOAT, CHAR, STRING, QUOTATION, ANTIQUOT
  and EOI; other lexers may propose other lists of tokens),

- an entry name, which correspond to a call to this entry,
- an entry name followed by the identifier ``LEVEL`` and a level
  label, which correspond to the call to this entry at that level,-
  the identifier ``SELF`` which is a recursive call to the present
  entry, according to the associativity (i.e. it may be a call at the
  current level, to the next level, or to the top level of the entry):
  ``SELF`` is equivalent to the name of the entry itself,
- the identifier ``NEXT``, which is a call to the next level of the
  current entry,
- a left brace, followed by a list of rules separated by vertical
  bars, and a right brace: equivalent to a call to an entry, with
  these rules, inlined,
- a meta symbol (see further),
- a symbol between parentheses.

The syntactic analysis follow the list of symbols. If it fails,
depending on the first items of the rule (see the section about the
kind of grammars recognized):

- the parsing may fail by raising the exception ``Stream.Error``
- the parsing may continue with the next rule.

Meta symbols
^^^^^^^^^^^^

Extra symbols exist, allowing to manipulate lists or optional
symbols. They are:

- LIST0 followed by a symbol: this is a list of this symbol, possibly
  empty,
- LIST0 followed by a symbol, SEP and another symbol, and optional
  OPT_SEP: this is a list, possibly empty, of the first symbol
  separated by the second one, possibly ended with the separator if
  OPT_SEP is present,
- LIST1 followed by a symbol: this is a list of this symbol, with at
  least one element,
- LIST1 followed by a symbol, SEP and another symbol, and optional
  OPT_SEP: this is a list, with at least one element, of the first
  symbol separated by the second one, possibly ended with the
  separator if OPT_SEP is present,
- OPT followed by a symbol: equivalent to "this symbol or nothing"
  returning a value of type ``option``.
- FLAG followed by a symbol: equivalent to "this symbol or nothing",
  returning a boolean.


The V meta symbol
^^^^^^^^^^^^^^^^^

The V meta symbol is destinated to allow antiquotations while using
the syntax tree quotation kit :ref:`q_ast` (``q_ast.cmo``). It works
only in strict mode. In transitional mode, it is just equivalent to
its symbol parameter.

Antiquotation kind
""""""""""""""""""

The antiquotation kind is the optional identifier between the starting
``$`` (dollar) and the ``:`` (colon) in a quotation of syntax tree
(see the chapter :ref:`ml_ast`).

The optional list of strings following the ``V`` meta symbol and its
symbol parameter gives the allowed antiquotations kinds.

By default, this string list, i.e. the available antiquotation kinds,
is:

- ``["flag"]`` for FLAG
- ``["list"]`` for LIST0 and LIST1
- ``["opt"]`` for OPT

For example, the symbol:

::

  V (FLAG "rec")

is like ``FLAG`` while normally parsing, allowing to parse the keyword
``rec``. While using it in quotations, also allows the parse the
keyword ``rec`` but, moreover, the antiquotation ``$flag:..$`` where
``..`` is an expression or a pattern depending on the position of the
quotation.

There are also default antiquotations kinds for the tokens used in the
OCaml language predefined parsers ``pa_r.cmo`` (revised syntax) and
``pa_o.cmo`` (normal syntax), actually all parsers using the provided
lexer ``Plexer`` (see the chapter :ref:`library`). They are:

- ``["chr"]`` for CHAR
- ``["flo"]`` for FLOAT
- ``["int"]`` for INT
- ``["int32"]`` for INT_l
- ``["int64"]`` for INT_L
- ``["nativeint"]`` for INT_n
- ``["lid"]`` for LIDENT
- ``["str"]`` for STRING
- ``["uid"]`` for UIDENT

It is also possible to use the "V" meta symbol over non-terminals
(grammars entries), but there is no default antiquotation kind. For
example, while parsing a quotation, the symbol:

::

  V foo "bar" "oops"

corresponds to either a call to the grammar entry ``foo``, or to the
antiquotations ``$bar:...$`` or ``$oops:...$``.

Type
^^^^

The type of the value returned by a V meta symbol is:

- in transitional mode, the type of its symbol parameter,
- in strict mode, ``Ploc.vala t``, where ``t`` is its symbol
  parameter.

In strict mode, if the symbol parameter is found, whose value is, say,
``x``, the result is ``Ploc.VaVal x``. If an antiquotation is found
the result is ``Ploc.VaAnt s`` where ``s`` is some string containing
the antiquotation text and some other internal information.

Rules insertion
---------------

Remember that ``EXTEND`` is a statement, not a declaration:
the rules are added in the entries at run time. Each rule is
internally inserted in a tree, allowing the left factorization of the
rule. For example, with this list of rules (borrowed from the Camlp5
sources):

::

  "method"; "private"; "virtual"; l = label; ":"; t = poly_type
  "method"; "virtual"; "private"; l = label; ":"; t = poly_type
  "method"; "virtual"; l = label; ":"; t = poly_type
  "method"; "private"; l = label; ":"; t = poly_type; "="; e = expr
  "method"; "private"; l = label; sb = fun_binding
  "method"; l = label; ":"; t = poly_type; "="; e = expr
  "method"; l = label; sb = fun_binding


the rules are inserted in a tree and the result looks like:

::

  "method"
     |-- "private"
     |       |-- "virtual"
     |       |       |-- label
     |       |             |-- ":"
     |       |                  |-- poly_type
     |       |-- label
     |             |-- ":"
     |             |    |-- poly_type
     |             |            |-- ":="
     |             |                 |-- expr
     |             |-- fun_binding
     |-- "virtual"
     |       |-- "private"
     |       |       |-- label
     |       |             |-- ":"
     |       |                  |-- poly_type
     |       |-- label
     |             |-- ":"
     |                  |-- poly_type
     |-- label
           |-- ":"
           |    |-- poly_type
           |            |-- "="
           |                 |-- expr
           |-- fun_binding


This tree is built as long as rules are inserted. When used, by
  applying the function ``Grammar.Entry.parse`` to the current
  entry, the input is matched with that tree, starting from the tree
  root, descending on it as long as the parsing advances.

There is a different tree by entry level.

Semantic action
---------------

The semantic action, i.e. the expression following the right arrow in
rules, contains in its environment:

- the variables bound by the patterns of the symbols found in the
  rules,
- the specific variable ``loc`` which contain the location of the
  whole rule in the source.

The location is an abstract type defined in the module ``Ploc`` of
Camlp5.

It is possible to change the name of this variable by using the
option``-loc`` of Camlp5. For example, compiling a file like this:

::

  camlp5r -loc foobar file.ml

the variable name, for the location will be ``foobar`` instead of
``loc``.

The DELETE_RULE statement
=========================

The ``DELETE_RULE`` statement is also added in the expressions of the
OCaml language when the syntax extension kit ``pa_extend.cmo`` is
loaded. Its syntax is:

::

        expression ::= delete-rule
       delete-rule ::= "DELETE_RULE" delete-rule-body "END"
  delete-rule-body ::= entry-name ":" symbols
           symbols ::= symbol symbols
                     | symbol


See the syntax of the EXTEND statement for the meaning of the syntax
entries not defined above.

The entry is scanned for a rule matching the giving symbol list. When
found, the rule is removed. If no rule is found, the exception
``Not_found`` is raised.

Extensions FOLD0 and FOLD1
==========================

When loading ``pa_extfold.cmo`` after ``pa_extend.cmo``, the entry
``symbol`` of the EXTEND statement is extended with what is named the
<em>fold iterators</em>, like this:

::

       symbol ::= "FOLD0" simple_expr simple_expr symbol
                | "FOLD1" simple_expr simple_expr symbol
                | "FOLD0" simple_expr simple_expr symbol "SEP" symbol
                | "FOLD1" simple_expr simple_expr symbol "SEP" symbol
  simple_expr ::= expr (level "simple")


Like their equivalent with the lists iterators: ``LIST0``, ``LIST1``,
``LIST0SEP``, ``LIST1SEP``, they read a sequence of symbols, possibly
with the separators, but instead of building the list of these
symbols, apply a fold function to each symbol, starting at the second
"expr" (which must be a expression node) and continuing with the first
"expr" (which must be a function taking two expressions and returing a
new expression).

The list iterators can be seen almost as a specific case of these fold
iterators where the initial "expr" would be:

::
  <:expr< [] >>


and the fold function would be:

::

  fun e1 e2 -> <:expr< [$e1$ :: $e2$ ] >>


except that, implemented like that, they would return the list in  reverse order.

Actually, a program using them can be written with the lists iterators
with the semantic action applying the function ``List.fold_left`` to
the returned list, except that with the fold iterators, this operation
is done as long as the symbols are read on the input, no intermediate
list being built.

Example, file ``sum.ml``:

::

  #load "pa_extend.cmo";
  #load "pa_extfold.cmo";
  #load "q_MLast.cmo";
  let loc = Ploc.dummy in
  EXTEND
    Pcaml.expr:
      [ [ "sum";
          e =
            FOLD0 (fun e1 e2 -> <:expr< $e2$ + $e1$ >>) <:expr< 0 >>
              Pcaml.expr SEP ";";
          "end" -> e ] ]
    ;
  END;


which can be compiled like this:

::

  ocamlc -pp camlp5r -I +camlp5 -c sum.ml

and tested:

::

  ocaml -I +camlp5 camlp5r.cma sum.cmo
          Objective Caml version ...

          Camlp5 Parsing version ...

  # sum 3;4;5 end;
  - : int = 12

Grammar machinery
=================

We explain here the detail of the mechanism of the parsing of an
entry.

Start and Continue
------------------

At each entry level, the rules are separated into two trees:

- The tree of the rules *not* starting with the current entry name nor
  by ``SELF``.
- The tree of the rules starting with the current entry name or by the
  identifier ``SELF``, this symbol not being included in the tree.


They determine two functions:

- The function named "start", analyzing the first tree.
- The function named "continue", taking, as parameter, a value
  previously parsed, and analyzing the second tree.

A call to an entry, using ``Grammar.Entry.parse`` correspond to a call
to the "start" function of the first level of the entry.

The "start" function tries its associated tree. If it works, it calls
the "continue" function of the same level, giving the result of
"start" as parameter. If this "continue" function fails, this
parameter is simply returned. If the "start" function fails, the
"start" function of the next level is tested. If there is no more
levels, the parsing fails.

The "continue" function first tries the "continue" function of the
next level. If it fails, or if it is the last level, it tries its
associated tree, then calls itself again, giving the result as
parameter. If its associated tree fails, it returns its extra
parameter.

Associativity
-------------

While testing the tree, there is a special case for rules ending with
SELF or with the current entry name. For this last symbol, there is a
call to the "start" function: of the current level if the level is
right associative, or of the next level otherwise.

There is no behaviour difference between left and non associative,
because, in case of syntax error, the system attempts to recover the
error by applying the "continue" function of the previous symbol (if
this symbol is a call to an entry).

When a SELF or the current entry name is encountered in the middle of
the rule (i.e. if it is not the last symbol), there is a call to the
"start" function of the first level of the current entry.

Example. Let us consider the following grammar:

::

  EXTEND
    expr:
      [ "minus" LEFTA
        [ x = SELF; "-"; y = SELF -> x -. y ]
      | "power" RIGHTA
        [ x = SELF; "**"; y = SELF -> x ** y ]
      | "simple"
        [ "("; x = SELF; ")" -> x
        | x = INT -> float_of_int x ] ]
    ;
  END

The left "SELF"s of the two levels "minus" and "power" correspond to a
call to the next level. In the level "minus", the right "SELF" also,
and the left associativity is treated by the fact that the "continue"
function is called (starting with the keyword "-" since the left
"SELF" is not part of the tree). On the other hand, for the level
"power", the right "SELF" corresponds to a call to the current level,
i.e. the level "power" again. At end, the "SELF" between parentheses
of the level "simple" correspond to a call to the first level, namely
"minus" in this grammar.

Parsing algorithm
-----------------

By default, the kind of grammar is predictive parsing grammar,
i.e. recursive descent parsing without backtrack. But with some
nuances, due to the improvements (error recovery and token starting
rules) indicated in the next sections.

However, it is possible to change the parsing algorithm, by calling
the function ``Grammar.set_algorithm``. The possible values are:

- ``Grammar.Predictive``: internally using :ref:`stream-parsers`, with
  a predictive (recursive descent without backtracking) algorithm.
- ``Grammar.Functional``: internally using :ref:`functional-parsers`,
  with a limited backtracking algorithm,
- ``Grammar.Backtracking``: internally using
  :ref:`backtracking-parsers`, with a full backtracking algorithm,
- ``Grammar.DefaultAlgorithm``: the parsing algorithm is determined by
  the environment variable ``CAMLP5PARAM``. If this environment variable
  exists and contains ``f``, the parsing algorithm is "functional"; if
  it it ``b``, the parsing algorithm is "backtracking". Otherwise it is
  "predictive".


An interesting function, when using then backtracking algorithm, is
``Grammar.Entry.parse_all`` which returns all solutions of a given
input.

See details in the chapter :ref:`library`, section "Grammar module".

Errors and recovery
-------------------

In extensible grammars, the exceptions are encapsulated with the
exception "Ploc.Exc" giving the location of the error together with
the exception itself.

If the parsing algorithm is ``Grammar.Predictive``, the system
internally uses :ref:`stream-parsers`. Two exceptions may happen:
``Stream.Failure`` or ``Stream.Error``. ``Stream.Failure`` indicates
that the parsing just could not start. ``Stream.Error`` indicates that
the parsing started but failed further.

With this algorithm, when the first symbol of a rule has been
accepted, all the symbols of the same rule must be accepted, otherwise
the exception ``Stream.Error`` is raised.

If the parsing algorithm is ``Grammar.Functional`` (resp.
``Grammar.Backtracking``), the system internally uses
:ref:`functional-parsers` (resp :ref:`backtracking-parsers`). If no
solution is found, the exception ``Stream.Error`` is raised and the
location of the error is the location of the last unfrozen token,
i.e. where the stream advanced the farthest.

In extensible grammars, unlike stream parsers, before the
``Stream.Error`` exception, the system attempts to recover the error
by the following trick: if the previous symbol of the rule was a call
to another entry, the system calls the "continue" function of that
entry, which may resolve the problem.

Tokens starting rules
---------------------

Another improvement (other than error recovery) is that when a rule
starts with several tokens and/or keywords, all these tokens and
keywords are tested in one time, and the possible ``Stream.Error`` may
happen, only from the symbol following them on, if any.

The Grammar module
==================

See :ref:`library_grammar_module`.

Interface with the lexer
========================

To create a grammar, the function ``Grammar.gcreate`` must be called,
with a lexer as parameter.

A simple solution, as possible lexer, is the predefined lexer built by
``Plexer.gmake ()``, lexer used for the OCaml grammar of Camlp5. In
this case, you can just put it as parameter of ``Grammar.gcreate`` and
it is not necessary to read this section.

The section first introduces the notion of "token patterns" which are
the way the tokens and keywords symbols in the EXTEND statement are
represented. Then follow the description of the type of the parameter
of ``Grammar.gcreate``.

Token patterns
--------------

A token pattern is a value of the type defined like this:

::

  type pattern = (string * string);

This type represents values of the token and keywords symbols in the
grammar rules.

For a token symbol in the grammar rules, the first string is the token
constructor name (starting with an uppercase character), the second
string indicates whether the match is "any" (the empty string) or some
specific value of the token (an non-empty string).

For a keyword symbol, the first string is empty and the second string
is the keyword itself.

For example, given this grammar rule:

::

  "for"; i = LIDENT; "="; e1 = SELF; "to"; e2 = SELF

the different symbols and keywords are represented by the following
pairs of strings:

- the keyword "for" is represented by ``("", "for")``,
- the keyword "=" by ``("", "=")``,
- the keyword "to" by ``("", "to")``),
- and the token symbol ``LIDENT`` by ``("LIDENT", "")``.

The symbol ``UIDENT "Foo"`` in a rule would be represented by the
token pattern:

::
  ("UIDENT", "Foo")

Notice that the symbol ``SELF`` is a specific symbol of the EXTEND
syntax: it does not correspond to a token pattern and is represented
differently. A token constructor name must not belong to the specific
symbols: SELF, NEXT, LIST0, LIST1, OPT and FLAG.

The lexer record
----------------

The type of the parameter of the function ``Grammar.gcreate`` is
``lexer``, defined in the module ``Plexing``. It is a record type with
the following fields:

``tok_func``
^^^^^^^^^^^^

It is the lexer itself. Its type is:

::

  Stream.t char -> (Stream.t (string * string) * location_function);

The lexer takes a character stream as parameter and return a couple of
containing: a token stream (the tokens being represented by a couple
of strings), and a location function.

The location function is a function taking, as parameter, a integer
corresponding to a token number in the stream (starting from zero),
and returning the location of this token in the source. This is
important to get good locations in the semantic actions of the grammar
rules.

Notice that, despite the lexer taking a character stream as parameter,
it is not mandatory to use the stream parsers technology to write the
lexer. What is important is that it does the job.

``tok_using``
^^^^^^^^^^^^^

Is a function of type:

::

  pattern -> unit

The parameter of this function is the representation of a token symbol
or a keyword symbol in grammar rules. See the section about token
patterns.

This function is called for each token symbol and each keyword
encountered in the grammar rules of the EXTEND statement. Its goal is
to allow the lexer to check that the tokens and keywords do respect
the lexer rules. It checks that the tokens exist and are not
mispelled. It can be also used to enter the keywords in the lexer
keyword tables.

Setting it as the function that does nothing is possible, but the
check of correctness of tokens is not done.

In case or error, the function must raise the exception
``Plexing.Error`` with an error message as parameter.

``tok_removing``
^^^^^^^^^^^^^^^^

Is a function of type:

::
  pattern -> unit


It is possibly called by the DELETE_RULE statement for tokens and
keywords no longer used in the grammar. The grammar system maintains a
number of usages of all tokens and keywords and calls this function
only when this number reaches zero. This can be interesting for
keywords: the lexer can remove them from its tables.

``tok_match``
^^^^^^^^^^^^^

Is a function of type:

::
  pattern -> ((string * string) -> unit)


The function tells how a token of the input stream is matched against
a token pattern. Both are represented by a couple of strings.

This function takes a token pattern as parameter and return a function
matching a token, returning the matched string or raising the
exception ``Stream.Failure`` if the token does not match.

Notice that, for efficiency, it is necessary to write this function as
a match of token patterns returning, for each case, the function which
matches the token, <em>not</em> a function matching the token pattern
and the token together and returning a string for each case.

An acceptable function is provided in the module ``Plexing`` and is
named "default_match". Its code looks like this:

::

  value default_match =
    fun
    [ (p_con, "") ->
        fun (con, prm) -> if con = p_con then prm else raise Stream.Failure
    | (p_con, p_prm) ->
        fun (con, prm) ->
          if con = p_con &amp;&amp; prm = p_prm then prm else raise Stream.Failure ]
  ;


``tok_text``
^^^^^^^^^^^^

Is a function of type:

::

  pattern -> string


Designed for error messages, it takes a token pattern as parameter and
returns the string giving its name.

It is possible to use the predefined function ``lexer_text`` of the
Plexing module. This function just returns the name of the token
pattern constructor and its parameter if any.

For example, with this default function, the token symbol IDENT would
be written as IDENT in error message (e.g. "IDENT expected").  The
"text" function may decide to print it differently, e.g., as
"identifier".

``tok_comm``
^^^^^^^^^^^^

Is a mutable field of type:

::
  option (list location)

It asks the lexer (the lexer function should do it) to record the
locations of the comments in the program. Setting this field to
``None`` indicates that the lexer must not record them. Setting it to
``Some []`` indicated that the lexer must put the comments location
list in the field, which is mutable.

Minimalist version
------------------

If a lexer have been written, named ``lexer``, here is the minimalist
version of the value suitable as parameter to ``Grammar.gcreate``:

::

  {Plexing.tok_func = lexer;
   Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
   Plexing.tok_match = Plexing.default_match;
   Plexing.tok_text = Plexing.lexer_text;
   Plexing.tok_comm = None}


Functorial interface
====================

The normal interface for grammars described in the previous sections
has two drawbacks:

- First, the type of tokens of the lexers must be ``(string *
  string)``
- Second, since the entry type has no parameter to specify the grammar
  it is bound to, there is no static check that entries are
  compatible, i.e.  belong to the same grammar. The check is done at
  run time.

The functorial interface resolve these two problems. The functor takes
a module as parameter where the token type has to be defined, together
with the lexer returning streams of tokens of this type. The resulting
module define entries compatible the ones to the other, and this is
controlled by the OCaml type checker.

The syntax extension must be done with the statement GEXTEND, instead
of EXTEND, and deletion by GDELETE_RULE instead of DELETE_RULE.

The lexer type
--------------

In the section about the interface with the lexer, we presented the
``Plexing.lexer`` type as a record without type parameter. Actually,
this type is defined as:

::

  type lexer 'te =
    { tok_func : lexer_func 'te;
      tok_using : pattern -> unit;
      tok_removing : pattern -> unit;
      tok_match : pattern -> 'te -> string;
      tok_text : pattern -> string;
      tok_comm : mutable option (list location) }
  ;

where the type parameter is the type of the token, which can be any
type, different from ``(string * string)``, providing the lexer
function (``tok_func``) returns a stream of this token type and the
match function (``tok_match``) indicates how to match values of this
token type against the token patterns (which remain defined as
``(string * string)``).

Here is an example of an user token type and the associated match
function:

::

  type mytoken =
    [ Ident of string
    | Int of int
    | Comma | Equal
    | Keyw of string  ]
  ;

  value mymatch =
    fun
    [ ("IDENT", "") ->
        fun [ Ident s -> s | _ -> raise Stream.Failure ]
    | ("INT", "") ->
        fun [ Int i -> string_of_int i | _ -> raise Stream.Failure ]
    | ("", ",") ->
        fun [ Comma -> "" | _ -> raise Stream.Failure ]
    | ("", "=") ->
        fun [ Equal -> "" | _ -> raise Stream.Failure ]
    | ("", s) ->
        fun
        [ Keyw k -> if k = s then "" else raise Stream.Failure
        | _ -> raise Stream.Failure ]
    | _ -> raise (Plexing.Error "bad token in match function") ]
  ;

The functor parameter
---------------------

The type of the functor parameter is defined as:

::

  module type GLexerType =
    sig
      type te = 'x;
      value lexer : Plexing.lexer te;
    end;

The token type must be specified (type ``te``) and the lexer also,
with the interface for lexers, of the lexer type defined above, the
record fields being described in the section "interface with the
lexer", but with a general token type.

The resulting grammar module
----------------------------

Once a module of type ``GLexerType`` has been built (previous
section), it is possible to create a grammar module by applying the
functor ``Grammar.GMake``. For example:

::

  module MyGram = Grammar.GMake MyLexer;

Notice that the function ``Entry.parse`` of this resulting module does
not take a character stream as parameter, but a value of type
``parsable``. This function is equivalent to the function
``parse_parsable`` of the non functorial interface. In short, the
parsing of some character stream ``cs`` by some entry ``e`` of the
example grammar above, must be done by:

::

  MyGram.Entry.parse e (MyGram.parsable cs)

instead of:

::

  MyGram.Entry.parse e cs

GEXTEND and GDELETE_RULE
------------------------

The ``GEXTEND`` and ``GDELETE_RULE`` statements are also added in the
expressions of the OCaml language when the syntax extension kit
``pa_extend.cmo`` is loaded. They must be used for grammars defined
with the functorial interface. Their syntax is:

::

           expression ::= gextend
                        | gdelete-rule
         gdelete-rule ::= "GDELETE_RULE" gdelete-rule-body "END"
              gextend ::= "GEXTEND" gextend-body "END"
         gextend-body ::= grammar-module-name extend-body
    gdelete-rule-body ::= grammar-module-name delete-rule-body
  grammar-module-name ::= qualid


See the syntax of the EXTEND statement for the meaning of the syntax
entries not defined above.

An example: arithmetic calculator
=================================

Here is a small calculator of expressions. They are given as
parameters of the command.

File "calc.ml":

::

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

Linking needs the library ``gramlib.cma`` provided with Camlp5:

::

  ocamlc -pp camlp5r -I +camlp5 gramlib.cma test/calc.ml -o calc

Examples:

::
  $ ./calc '239*4649'
  239*4649 = 1111111
  $ ./calc '(47+2)/3'
  (47+2)/3 = 16

