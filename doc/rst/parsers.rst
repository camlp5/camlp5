.. _stream_parsers:

Stream parsers
==============

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Stream parsers
      :name: stream-parsers
      :class: top

   We describe here the syntax and the semantics of the parsers of
   streams of Camlp5. Streams are kinds of lazy lists. The parsers of
   these streams use recursive descendent method without backtracking,
   which is the most natural one in functional languages. In particular,
   parsers are normal functions.

   Notice that the parsers have existed in OCaml since many years (the
   beginning of the 90ies), but some new features have been added in
   2007 (lookahead, "no error" optimization, let..in statement and left
   factorization) in Camlp5 distribution. This chapter describes them
   also.

   .. container::
      :name: tableofcontents

   .. rubric:: Introduction
      :name: introduction

   Parsers apply to values of type "Stream.t" defined in the module
   "Stream" of the standard library of OCaml. Like the type "list", the
   type "Stream.t" has a type parameter, indicating the type of its
   elements. They differ from the lists that they are lazy (the elements
   are evaluated as long as the parser need them for its actions), and
   imperative (parsers deletes their first elements when they take their
   parsing decisions): notice that purely functional parsers exist in
   Camlp5, where the corresponding streams are lazy and functional, the
   analyzed elements remaining in the initial stream and the semantic
   action returning the resulting stream together with the normal
   result, which allow natural limited backtrack but have the drawback
   that it is not easy to find the position of parsing errors when they
   happen.

   Parsers of lazy+imperative streams, which are described here, use a
   method named "recursive descendent": they look at the first element,
   they decide what to do in function of its value, and continue the
   parsing with the remaining elements. Parsers can call other parsers,
   and can be recursive, like normal functions.

   Actually, parsers are just pure syntactic sugar. When writing a
   parser in the syntax of the parser, Camlp5 transforms them into
   normal call to functions, use of patterns matchings and try..with
   statements. The pretty printer of Camlp5, by default, displays this
   expanded result, without syntax of parsers. A pretty printing kit,
   when added, can rebuild the parsers in their initial syntax and
   display it.

   .. rubric:: Syntax
      :name: syntax

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

   .. rubric:: Streams
      :name: streams

   The parsers are functions taking streams as parameter. Streams are
   are values of type "``Stream.t a``" for some type "``a``". It is
   possible to build streams using the functions defined in the module
   "``Stream``":

   .. rubric:: Stream.from
      :name: stream.from

   "``Stream.from f``" returns a stream built from the function "``f``".
   To create a new stream element, the function "``f``" is called with
   the current stream count, starting with zero. The user function
   "``f``" must return either "``Some <value>``" for a value or
   "``None``" to specify the end of the stream.

   .. rubric:: Stream.of_list
      :name: stream.of_list

   Return a stream built from the list in the same order.

   .. rubric:: Stream.of_string
      :name: stream.of_string

   Return a stream of the characters of the string parameter.

   .. rubric:: Stream.of_channel
      :name: stream.of_channel

   Return a stream of the characters read from the input channel
   parameter.

   .. rubric:: Semantics of parsers
      :name: semantics-of-parsers

   .. rubric:: Parser
      :name: parser

   A parser, defined with the syntax "parser" above, is of type
   "``Stream.t a -> b``" where "a" is the type of the elements of the
   streams and "b" the type of the result. The parser cases are tested
   in the order they are defined until one of them applies. The result
   is the semantic action of the parser case which applies. If no parser
   case applies, the exception "``Stream.Failure``" is raised.

   When testing a parser case, if the first stream pattern component
   matches, all remaining stream pattern components of the stream
   pattern must match also. If one does not match, the parser raises the
   exception "``Stream.Error``" which has a parameter of type string: by
   default, this string is the empty string, but if the stream pattern
   component which does not match is followed by a question mark and an
   expression, this expression is evaluated and given as parameter to
   "``Stream.Error``".

   In short, a parser can return with three ways:

   -  A normal result, of type "``b``" for a parser of type
      "``Stream.t a -> b``".
   -  Raising the exception "``Stream.Failure``".
   -  Raising the exception "``Stream.Error``".

   Fundamentally, the exception "``Stream.Failure``" means "this parser
   does not apply and no element have been removed from the initial
   stream". This is a normal case when parsing: the parser locally
   fails, but the parsing can continue.

   Conversely, the exception "``Stream.Error``" means that "this parser
   encountered a syntax error and elements have probably been removed
   from the stream". In this case, there is no way to recover the
   parsing, and it definitively fails.

   .. rubric:: Left factorization
      :name: left-factorization

   In parsers, *consecutive* rules starting with the same components are
   left factorized. It means that they are transformed into one only
   rule starting with the common path, and continuing with a call to a
   parser separating the two cases. The order is kept, except that the
   possible empty rule is inserted at the end.

   For example, the parser:

   ::

        parser
        [ [: `If; e1 = expr; `Then; e2 = expr; `Else; e3 = expr :] -> f e1 e2 e3
        | [: `If; e1 = expr; `Then; e2 = expr :] -> g e1 e2 ]

   is transformed into:

   ::

        parser
          [: `If; e1 = expr; `Then; e2 = expr;
             a =
               parser
               [ [: `Else; e3 = expr :] -> f e1 e2 e3
               | [: :] -> g e1 e2 ] :] -> a

   The version where rules are inverted:

   ::

        parser
        [ [: `If; e1 = expr; `Then; e2 = expr :] -> g e1 e2
        | [: `If; e1 = expr; `Then; e2 = expr; `Else; e3 = expr :] -> f e1 e2 e3 ]

   is transformed into the same parser.

   Notice that:

   -  Only *consecutive* rules are left factorized. In the following
      parser:

      ::

           parser
           [ [: `If; e1 = expr; `Then; e2 = expr; `Else; e3 = expr :] -> ...
           | [: a = b :] -> a
           | [: `If; e1 = expr; `Then; e2 = expr :] -> ... ]

      the two rules starting with "``If``" are not left factorized, and
      the second "``If``" rule will never work.

   -  The components which are not *identical* are not factorized. In
      the following parser:

      ::

           parser
           [ [: `If; e1 = expr; `Then; e2 = expr; `Else; e3 = expr :] -> ...
           | [: `If; e4 = expr; `Then; e2 = expr :] -> ... ]

      only the first component, "``If``" is factorized, the second one
      being different because of different patterns ("``e1``" and
      "``e4``").

   .. rubric:: Match with parser
      :name: match-with-parser

   The syntax "match expression with parser" allows to match a stream
   against a parser. It is, for "parser", the equivalent of "match
   expression with" for "fun". The same way we could say:

   ::

        match expression with ...

   could be considered as an equivalent to:

   ::

        (fun ...) expression

   we could consider that:

   ::

        match expression with parser ...

   is an equivalent to:

   ::

        (parser ...) expression

   .. rubric:: Error messages
      :name: error-messages

   A "``Stream.Error``" exception is raised when a stream pattern
   component does not match and that it is not the first one of the
   parser case. This exception has a parameter of type string, useful to
   specify the error message. By default, this is the empty string. To
   specify an error message, add a question mark and an expression after
   the stream pattern component. A typical error message is "that stream
   pattern component expected". Example with the parser of
   "if..then..else.." above:

   ::

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

   .. rubric:: Stream pattern component
      :name: stream-pattern-component

   In a stream pattern (starting with "``[:``" and ending with
   "``:]``"), the stream pattern components are separated with the
   semicolon character. There are three cases of stream pattern
   components with some sub-cases for some of them, and an extra syntax
   can be used with a "let..in" construction. The three cases are:

   -  A direct test of one or several stream elements (called
      **terminal** symbol), in three ways:

      #. The character "backquote" followed by a pattern, meaning: if
         the stream starts with an element which is matched by this
         pattern, the stream pattern component matches, and the stream
         element is removed from the stream.
      #. The character "backquote" followed by a pattern, the keyword
         "when" and an expression of type "``bool``", meaning: if the
         stream starts with an element which is matched by this pattern
         and if the evaluation of the expression is "``True``", the
         stream pattern component matches, and the first element of the
         stream is removed.
      #. The character "question mark" followed by the character "equal"
         and a lookahead expression (see further), meaning: if the
         lookahead applies, the stream pattern component matches. The
         lookahead may unfreeze one or several elements on the stream,
         but does not remove them.

   -  A pattern followed by the "equal" sign and an expression of type
      "``Stream.t x -> y``" for some types "``x``" and "``y``". This
      expression is called a **non terminal** symbol. It means: call the
      expression (which is a parser) with the current stream. If this
      sub-parser:

      #. Returns an element, the pattern is bound to this result and the
         next stream pattern component is tested.
      #. Raises the exception "``Stream.Failure``", there are two cases:

         -  if the stream pattern component is the first one of the
            stream case, the current parser also fails with the
            exception "``Stream.Failure``".
         -  if the stream pattern component is not the first one of the
            stream case, the current parser fails with the exception
            "``Stream.Error``".

         In this second case:

         -  If the stream pattern component is followed by a "question
            mark" and an expression (which must be of type
            "``string``"), the expression is evaluated and given as
            parameter of the exception "``Stream.Error``".
         -  If the expression is followed by an "exclamation mark", the
            test and conversion from "``Stream.Failure``" to
            "``Stream.Error``" is not done, and the parser just raises
            "``Stream.Failure``" again. This is an optimization which
            must be assumed by the programmer, in general when he knows
            that the sub-parser called never raises "``Stream.Failure``"
            (for example if the called parser ends with a parser case
            containing an empty stream pattern). See "no error
            optionization" below.
         -  Otherwise the exception parameter is the empty string.

   -  A pattern, which is bound to the current stream.

   Notice that patterns are bound immediately and can be used in the
   next stream pattern component.

   .. rubric:: Let statement
      :name: let-statement

   Between stream pattern components, it is possible to use the
   "let..in" construction. This is not considered as a real stream
   pattern component, in the fact that is is not tested against the
   exception "``Stream.Failure``" it may raise. It can be useful for
   intermediate computation. In particular, it is used internally by the
   lexers (see chapter about `lexers <lexers.html>`__ as character
   stream parsers).

   Example of use, when an expression have to be used several times (in
   the example, "``d a``", which is bound to the variable "``c``"):

   ::

        parser
          [: a = b;
             let c = d a in
             e =
               parser
               [ [: f = g :] -> h c
               | [: :] -> c ] :] -> e

   .. rubric:: Lookahead
      :name: lookahead

   The lookahead feature allows to look at several terminals in the
   stream without removing them, in order to take decisions when more
   than one terminal is necessary.

   For example, when parsing the normal syntax of the OCaml language,
   there is a problem, in recursing descendent parsing, for the cases
   where to treat and differentiate the following inputs:

   ::

        (-x+1)
        (-)

   The first case is treated in a rule, telling: "a left parenthesis,
   followed by an expression, and a right parenthesis". The second one
   is "a left parenthesis, an operator, a right parenthesis".
   Programming it like this (left factorizing the first parenthesis):

   ::

        parser
          [: `Lparen;
             e =
               parser
               [ [: e = expr; `Rparen :] -> e
               | [: `Minus; `Rparen :] -> minus_op ] :] -> e

   does not work if the input is "``(-)``" because the rule
   "``e = expr``" accepts the minus sign as expression start, removing
   it from the input stream and fails as parsing error, while
   encountering the right parenthesis.

   Conversely, writing it this way:

   ::

        parser
          [: `Lparen;
             e =
               parser
               [ [: `Minus; `Rparen :] -> minus_op
               | [: e = expr; `Rparen :] -> e ] :] -> e

   does not help, because if the input is "``(-x+1)``" the rule above
   starting with ":literal:`\`Minus`" is accepted and the exception
   "``Stream.Error``" is raised while encountering the variable "``x``"
   since a right parenthesis is expected.

   In general, this kind of situation is best resolved by a left
   factorization of the parser cases (see the section "Semantics"
   above), but that is not possible in this case. The solution is to
   test whether the character after the minus sign is a right
   parenthesis:

   ::

        parser
          [: `Lparen;
             e =
               parser
               [ [: ?= [ _ ; Rparen ]; `Minus; `Rparen :] -> minus_op
               | [: e = expr; `Rparen :] -> e ] :] -> e

   It is possible to put several lists of (semicolon-separated)
   patterns separated by a vertical bar in the lookahead construction,
   but with a limitation (due to the implementation): all lists of
   patterns must have the same number of elements.

   .. rubric:: No error optimization
      :name: no-error-optimization

   The "no error optimization" is the fact to end a stream pattern
   component of kind "non-terminal" ("pattern" "equal" "expression") by
   the character "exclamation mark". Like said above, this inhibits the
   transformation of the exception "``Stream.Failure``", possibly raised
   by the called parser, into the exception "``Stream.Error``".

   The code:

   ::

        parser [: a = b; c = d ! :] -> e

   is equivalent to:

   ::

        parser [: a = b; s :] -> let c = d s in e

   One interest of the first syntax is that it shows to readers that
   "``d``" is indeed a syntactic sub-parser. In the second syntax, it is
   called in the semantic action, which makes the parser case not so
   clear, as far as readability is concerned.

   If the stream pattern component is at end of the stream pattern, this
   allow possible tail recursion by the OCaml compiler, in the following
   case:

   ::

        parser [: a = b; c = d ! :] -> c

   since it is equivalent (with the fact that "``c``" is at the same
   time the pattern of the last case and the expression of the parser
   case semantic action) to:

   ::

        parser [: a = b; s :] -> d s

   The call to "``d s``" can be a tail recursive call. Without the use
   of the "exclamation mark" in the rule, the equivalent code is:

   ::

        parser [: a = b; s :] ->
          try d s with [ Stream.Failure -> raise (Stream.Error "") ]

   which is not tail recursive (due to the "try..with" construction
   pushes a context), preventing the compiler to optimize its code. This
   can be important when many recursive calls happen, since it can
   overflow the OCaml stack.

   .. rubric:: Position
      :name: position

   The optional "pattern" before and after a stream pattern is bound to
   the current stream count. Indeed, streams internally contain a count
   of their elements. At the beginning the count is zero. When an
   element is removed, the count is incremented. The example:

   ::

        parser [: a = b :] ep -> c

   is equivalent to:

   ::

        parser [: a = b; s :] -> let ep = Stream.count s in c

   There is no direct syntax equivalent to the optional pattern at
   beginning of the stream pattern:

   ::

        parser bp [: a = b :] -> c

   These optional patterns allow disposal of the stream count at the
   beginning and at the end of the parser case, allowing to compute
   locations of the rule in the source. In particular, if the stream is
   a stream of characters, these counts are the source location in
   number of characters.

   .. rubric:: Semantic action
      :name: semantic-action

   In a parser case, after the stream pattern, there is an "arrow" and
   an expression, called the "semantic action". If the parser case is
   matched the parser returns with the evaluated expression whose
   environment contains all values bound in the stream pattern.

   .. rubric:: Remarks
      :name: remarks

   .. rubric:: Simplicity vs Associativity
      :name: simplicity-vs-associativity

   This parsing technology has the advantage of simplicity of use and
   understanding, but it does not treat the associativity of operators.
   For example, if you write a parser like this (to compute arithmetic
   expressions):

   ::

        value rec expr =
          parser
          [ [: e1 = expr; `'+'; e2 = expr :] -> e1 + e2
          | [: `('0'..'9' as c) :] -> Char.code c - Char.code '0' ]

   this would loop endlessly, exactly as if you wrote code starting
   with:

   ::

        value rec expr e =
          let e1 = expr e in
          ...

   One solution is to treat the associativity "by hand": by reading a
   sub-expression, then looping with a parser which parses the operator
   and another sub-expression, and so on.

   An alternative solution is to write parsing "combinators". Indeed,
   parsers being normal functions, it is possible to make a function
   which takes a parser as parameter and returning a parser using it.
   For example, left and right associativity parsing combinators:

   ::

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

   which can be used, e.g. like this:

   ::

        value expr =
          List.fold_right (fun op elem -> op elem)
            [left_assoc (parser [: `'+' :] -> fun x y -> x +. y);
             left_assoc (parser [: `'*' :] -> fun x y -> x *. y);
             right_assoc (parser [: `'^' :] -> fun x y -> x ** y)]
            (parser [: `('0'..'9' as c) :] -> float (Char.code c - Char.code '0'))
        ;

   and tested, e.g. in the toplevel, like that:

   ::

        expr (Stream.of_string "2^3^2+1");

   The same way, it is possible to parse non-context free grammars, by
   programming parsers returning other parsers.

   A third solution, to resolve the problem of associativity, is to use
   the grammars of Camlp5, which have the other advantage that they are
   extensible.

   .. rubric:: Lexing vs Parsing
      :name: lexing-vs-parsing

   In general, while analyzing a language, there are two levels:

   -  The level where the input, considered as a stream of characters,
      is read to make a stream of tokens (for example "words", if it is
      a human language, or punctuation). This level is generally called
      "lexing".
   -  The level where the input is a stream of tokens where grammar
      rules are parsed. This level is generally called "parsing".

   The "parser" construction described here can be used for both, thanks
   to the polymorphism of OCaml:

   -  The lexing level is a "parser" of streams of characters returning
      tokens.
   -  The parsing level is a "parser" of streams of tokens returning
      syntax trees.

   By comparison, the programs "lex" and "yacc" use two different
   technologies. With "parser"s, it is possible to use the same one for
   both.

   .. rubric:: Lexer syntax vs Parser syntax
      :name: lexer-syntax-vs-parser-syntax

   For "lexers", i.e. for the specific case of parsers when the input is
   a stream of characters, it is possible to use a shorter syntax. See
   the chapter on `lexers <lexers.html>`__. They have another syntax,
   shorter and adapted for the specific type "``char``". But they still
   are internally parsers of streams with the same semantics.

   .. rubric:: Purely functional parsers
      :name: purely-functional-parsers

   This system of parsers is imperative: while parsing, the stream
   advances and the already parsed terminals disappear from the stream
   structure. This is useful because it is not necessary to return the
   remaining stream together with the normal result. This is the reason
   there is this "``Stream.Error``" exception: when it is raised, it
   means that some terminals have been consummed from the stream, which
   are definitively lost, and therefore that are no more possible parser
   cases to try.

   An alternative is to use `functional parsers <fparsers.html>`__ which
   use a new stream type, lazy but not destructive. Their advantage is
   that they use a limited backtrack: the case of "if..then..else.." and
   the shorter "if..then.." work without having to left factorize the
   parser cases, and there is no need to lookahead. They have no
   equivalent to the exception "``Stream.Error``": when all cases are
   tested, and have failed, the parsers return the value "``None``". The
   drawback is that, when a parsing error happens, it is not easily
   possible to know the location of the error in the input, as the
   initial stream has not been modified: the system would indicate a
   failure at the first character of the first line: this is a general
   drawback of backtracking parsers. See the solutions found to this
   problem in the chapter about `purely functional
   parsers <fparsers.html>`__.

   A second alternative is to use the `backtracking
   parsers <bparsers.html>`__. They use the same stream type as the
   functional parsers, but they test more cases than them. They have the
   same advantages and drawbacks than the functional parsers.

   .. container:: trailer
