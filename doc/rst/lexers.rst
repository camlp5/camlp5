Stream lexers
=============

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Stream lexers
      :name: stream-lexers
      :class: top

   The file "``pa_lexer.cmo``" is a Camlp5 syntax extension kit for
   parsers of streams of the type 'char'. This syntax is shorter and
   more readable than its equivalent version written with `classical
   stream parsers <parsers.html>`__. Like classical parsers, they use
   recursive descendant parsing. They are also pure syntax sugar, and
   each lexer written with this syntax can be written using normal
   parsers syntax.

   .. container::
      :name: tableofcontents

   (An old version, named "``pa_lex.cmo``" was provided before with a
   different syntax. It is no longer distributed, its proposed syntax
   being confusing.)

   .. rubric:: Introduction
      :name: introduction

   Classical parsers in OCaml apply to streams of any type of values.
   For the specific type "char", it has been possible to shorten the
   encoding in several ways, in particular by using strings to group
   several characters together, and by hidding the management of a
   "lexing buffer", a data structure recording the matched characters.

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

   The two codes are strictly equivalent, but the lexer version is
   easier to write and understand, and is much shorter.

   .. rubric:: Syntax
      :name: syntax

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

   The identifiers "``STRING``", "``CHAR``" and "``LIDENT``" above
   represent the OCaml tokens corresponding to string, character and
   lowercase identifier (identifier starting with a lowercase
   character).

   Moreover, together with that syntax extension, another extension is
   added the entry ``expression``, typically for the semantics actions
   of the "``lexer``" statement above, but not only. It is:

   ::

        expression ::= "$" "add" STRING
                     | "$" "buf"
                     | "$" "empty"
                     | "$" "pos"

   Remark: the identifiers "add", "buf", "empty" and "pos" are not
   keywords (they are not reserved words) but just identifiers. On the
   contrary, the identifier "``lexer``", which introduces the syntax, is
   a new keyword and cannot be used as variable identifier any more.

   .. rubric:: Semantics
      :name: semantics

   A lexer defined in the syntax above is a shortcut version of a parser
   applied to the specific case of streams of characters. It could be
   written with a normal parser. The proposed syntax is much shorter,
   easier to use and to understand, and silently takes care of the
   lexing buffer for the programmer. The lexing buffers are data
   structures, which are passed as parameters to called lexers and
   returned by them.

   Our lexers are of the type:

   ::

        Plexing.Lexbuf.t -> Stream.t char -> u

   where "``u``" is a type which depends on what the lexer returns. If
   there is no semantic action (since it it optional), this type is
   automatically "``Plexing.Lexbuf.t``" also.

   A lexer is, actually, a function with two implicit parameters: the
   first one is the lexing buffer itself, and the second one the stream.
   When called, it tries to match the stream against its first rule. If
   it fails, it tries its second rule, and so on, up to its last rule.
   If the last rule fails, the lexer fails by raising the exception
   "``Stream.Failure``". All of this is the `usual behaviour of stream
   parsers <parsers.html>`__.

   In a rule, when a character is matched, it is inserted into the
   lexing buffer, except if the "no record" feature is used (see
   further).

   Rules which have no semantic action return the lexing buffer itself.

   .. rubric:: Symbols
      :name: symbols

   The different kinds or symbols in a rule are:

   -  The token "underscore", which represents any character. Fails only
      if the stream is empty.
   -  A character which represents a matching of this character.
   -  A character followed by the minus sign and by another character
      which represent all characters in the range between the two
      characters in question.
   -  A string with represents a matching of all its characters, one
      after the other.
   -  An expression corresponding to a call to another lexer, which
      takes the buffer as first parameter and returns another lexing
      buffer with all characters found in the stream added to the
      initial lexing buffer.
   -  The sequence "``?=``" introducing lookahead characters.
   -  A rule, recursively, between brackets, inlining a lexer.

   In the cases matching characters (namely underscore, character,
   characters range and string), the symbol can be optionally followed
   by the "no record" character "slash" specifying that the found
   character(s) are not added into the lexing buffer. By default, they
   are. This feature is useful, for example, writing a lexer which
   parses strings, when the initial double quote and final double quote
   should not be part of the string itself.

   Moreover, a symbol can be followed by an optional error indicator,
   which can be:

   -  The character ``?`` (question mark) followed by a string
      expression, telling that, if there is a syntax error at this point
      (i.e. the symbol is not matched although the beginning of the rule
      was), the exception ``Stream.Error`` is raised with that string as
      parameter. Without this indicator, it is raised with the empty
      string. This is the same behaviour than with classical `stream
      parsers <parsers.html>`__.
   -  The character ``!`` (exclamation mark), which is just an indicator
      to let the syntax expander optimize the code. If the programmer is
      sure that the symbol never fails (i.e. never raises
      ``Stream.Failure``), in particular if this symbol recognizes the
      empty rule, he can add this exclamation mark. If it is used
      correctly (the compiler cannot check it), the behaviour is
      identical as without the ``!``, except that the code is shorter
      and faster, and can sometimes be tail recursive. If the indication
      is not correct, the behaviour of the lexer is undefined.

   .. rubric:: Specific expressions
      :name: specific-expressions

   When loading this syntax extension, the entry ``<expression>``, at
   level labelled "simple" of the OCaml language is extended with the
   following rules:

   -  ``$add`` followed by a string, specifing that the programmer wants
      to add all characters of the string in the lexing buffer. It
      returns the new lexing buffer. It corresponds to an iteration of
      calls to ``Plexing.Lexbuf.add`` with all characters of the string
      with the current lexing buffer as initial parameter.
   -  ``$buf`` which returns the lexing buffer converted into string.
   -  ``$empty`` which returns an empty lexing buffer.
   -  ``$pos`` which returns the current position of the stream in
      number of characters (starting at zero).

   .. rubric:: Lookahead
      :name: lookahead

   Lookahead is useful in some cases, when factorization of rules is
   impossible. To understand how it is useful, a first remark must be
   done, about the usual behaviour of Camlp5 stream parsers.

   Stream parsers (including these lexers) use a limited parsing
   algorithm, in a way that when the first symbol of a rule is matched,
   all the following symbols of the same rule must apply, otherwise it
   is a syntax error. There is no backtrack. In most of the cases, left
   factorization of rules resolve conflicting problems. For example, in
   parsers of tokens (which is not our case here, since we parse only
   characters), when one writes a parser to recognize both typical
   grammar rules "if..then..else" and the shorter "if..then..", the
   system transforms them into a single rule starting with "if..then.."
   followed by a call to a parser recognizing "else.." or nothing.

   Sometimes, however, this left factorization is not possible. A
   lookahead of the stream to check the presence of some elements (these
   elements being characters, if we are using this "lexer" syntax) might
   be necessary to decide if is a good idea to start the rule. This
   lookahead feature may unfreeze several characters from the input
   stream but without removing them.

   Syntactically, a lookahead starts with ``?=`` and is followed by one
   or several lookahead sequences separated by the vertical bar ``|``,
   the whole list being enclosed by braces.

   If there are several lookaheads, they must all be of the same size
   (contain the same number of characters).

   If the lookahead sequence is just a string, it corresponds to all
   characters of this string in the order (which is different for
   strings outside lookahead sequences, representing a choice of all
   characters).

   Examples of lookaheads:

   ::

        ?= [ _ ''' | '\\' _ ]
        ?= [ "<<" | "<:" ]

   The first line above matches a stream whose second character is a
   quote or a stream whose first character is a backslash (real example
   in the lexer of OCaml, in the library of Camlp5, named "plexer.ml").
   The second line matches a stream starting with the two characters
   ``<`` and ``<`` or starting with the two characters ``<`` and ``:``
   (this is another example in the same file).

   .. rubric:: Semantic actions of rules
      :name: semantic-actions-of-rules

   By default, the result of a "lexer" is the current lexing buffer,
   which is of type "``Plexing.Lexbuf.t``". But it is possible to return
   other values, by adding "``->``" at end of rules followed by the
   expression you want to return, as in usual pattern matching in OCaml.

   An interesting result, for example, could be the string corresponding
   to the characters of the lexing buffer. This can be obtained by
   returning the value "``$buf``".

   .. rubric:: A complete example
      :name: a-complete-example

   A complete example can be seen in the sources of Camlp5, file
   "lib/plexer.ml". This is the lexer of OCaml, either "normal" or
   "revised" syntax.

   .. rubric:: Compiling
      :name: compiling

   To compile a file containing lexers, just load ``pa_lexer.cmo`` using
   one of the following methods:

   -  Either by adding ``pa_lexer.cmo`` among the Camlp5 options. See
      the Camlp5 manual page or documentation.
   -  Or by adding ``#load "pa_lexer.cmo";`` anywhere in the file,
      before the usages of this "lexer" syntax.

   .. rubric:: How to display the generated code
      :name: how-to-display-the-generated-code

   You can see the generated code, for a file "bar.ml" containing
   lexers, by typing in a command line:

   ::

        camlp5r pa_lexer.cmo pr_r.cmo bar.ml

   To see the equivalent code with stream parsers, use:

   ::

        camlp5r pa_lexer.cmo pr_r.cmo pr_rp.cmo bar.ml

   .. container:: trailer
