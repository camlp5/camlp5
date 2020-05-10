Functional parsers
==================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Functional parsers
      :name: functional-parsers
      :class: top

   Purely functional parsers are an alternative of `stream
   parsers <parsers.html>`__ where the used stream type is a lazy
   non-destructive type. These streams are lazy values, as in classical
   stream parsers, but the values are not removed as long as the parsing
   advances.

   To make them work, the parsers of purely functional streams return,
   not the simple values, but a value of type option : "``None``"
   meaning "no match" (the equivalent of the exception
   "``Parse.Failure``" of normal streams) and "``Some (r, s)``" meaning
   "the result is r and the remaining stream is s".

   .. container::
      :name: tableofcontents

   .. rubric:: Syntax
      :name: syntax

   The syntax of purely functional parsers, when loading
   "pa_fstream.cmo", is the following:

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

   .. rubric:: Streams
      :name: streams

   The functional parsers are functions taking as parameters functional
   streams, which are values of type "``Fstream.t   a``" for some type
   "``a``". It is possible to build functional streams using the
   functions defined in the module "``Fstream``":

   .. rubric:: Fstream.from
      :name: fstream.from

   "``Fstream.from f``" returns a stream built from the function
   "``f``". To create a new stream element, the function "``f``" is
   called with the current stream count, starting with zero. The user
   function "``f``" must return either "``Some <value>``" for a value or
   "``None``" to specify the end of the stream.

   .. rubric:: Fstream.of_list
      :name: fstream.of_list

   Return a stream built from the list in the same order.

   .. rubric:: Fstream.of_string
      :name: fstream.of_string

   Return a stream of the characters of the string parameter.

   .. rubric:: Fstream.of_channel
      :name: fstream.of_channel

   Return a stream of the characters read from the input channel
   parameter.

   .. rubric:: Semantics of parsers
      :name: semantics-of-parsers

   .. rubric:: Fparser
      :name: fparser

   The purely functional parsers act like classical parsers, with a
   recursive descent algorithm, except that:

   -  If the first stream pattern component matches the beginning of the
      stream, there is no error if the following stream patterns
      components do not match: the control simply passes to the next
      parser case with the initial stream.
   -  If the semantic actions are of type "``t``", the result of the
      parser is of type "``option (t * Fstream.t)``", not just "``t``"
      like in classical parsers. If a stream pattern matches, the
      semantic action is evaluated, giving some result "``e``" and the
      result of the parser is "``Some (e, strm)``" where "``strm``" is
      the remaining stream.
   -  If no parser case matches, the result of the parser is "``None``".

   .. rubric:: Error position
      :name: error-position

   A difficulty, with purely functional parsers, is how to find the
   position of the syntax error, when the input is wrong. Since the
   system tries all parsers cases before returning "``None``", and that
   the initial stream is not affected, it is not possible to directly
   find where the error happened. This is a problem for parsing using
   backtracking (here, it is limited backtracking, but the problem is
   the same).

   The solution is to use the function "``Fstream.count_unfrozen``"
   applied to the initial stream. Like its name says, it returns the
   number of unfrozen elements of the stream, which is exactly the
   longest match found. If the input is a stream of characters, the
   return of this function is exactly the position in number of
   characters from the beginning of the stream.

   However, it is not possible to know directly which rule failed and
   therefore it is not possible, as in classical parsers, to specify and
   get clear error messages. Future versions of purely functional
   parsers may propose solutions to resolve this problem.

   Notice that, if using the "``count_unfrozen``" method, it is not
   possible to reuse that same stream to call another parser, and hope
   to get the right position of the error, if another error happens,
   since it may test less terminals than the first parser. Use a fresh
   stream in this case, if possible.

   .. container:: trailer
