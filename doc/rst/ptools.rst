Parsing and Printing tools
==========================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Parsing and Printing tools
      :name: parsing-and-printing-tools
      :class: top

   Camlp5 provides two parsing tools:

   -  stream parsers
   -  extensible grammars

   The first parsing tool, the stream parsers, is the elementary system.
   It is pure syntactic sugar, i.e. the code is directly converted into
   basic OCaml statements: essentially functions, pattern matchings,
   try. A stream parser is just a function. But the system does not
   manage associativity, nor parsing level. Left recursion results on
   infinite loops, just like functions whose first action would be a
   call to itself.

   The second parsing tool, the extensible grammars, are more
   sophisticated. A grammar written with them is more readable, and look
   like grammars written with tools like "yacc". They take care of
   associativity, left recursion, and level of parsing. They are
   dynamically extensible, what allows the syntax extensions what Camlp5
   provides for OCaml syntax.

   In both cases, the input data are streams.

   Camlp5 also provides:

   -  a pretty printing module
   -  extensible printers

   The next sections give an overview of the parsing and printing tools.

   .. container::
      :name: tableofcontents

   .. rubric:: Stream parsers
      :name: stream-parsers

   The stream parsers is a system of recursive descendant parsing.
   Streams are actually lazy lists. At each step, the head of the list
   is compared against a *stream pattern*. There are three kinds of
   streams parsers:

   -  The imperative `streams parsers <parsers.html>`__, where the
      elements are removed from the stream as long as they are parsed.
      Parsers return either:

      -  A value, in case of success,
      -  The exception "``Stream.Failure``" when the parser does not
         apply and no elements have been removed from the stream,
         indicating that, possibly, other parsers may apply,
      -  The exception "``Stream.Error``" when the parser does not
         apply, but one or several elements have been removed from the
         stream, indicating that nothing can to be done to make up the
         error.

   -  The `functional stream parsers <fparsers.html>`__ where the
      elements are not removed from the stream during the parsing. These
      parsers return a value of type "option", i.e either:

      -  "Some" a value and the remaining stream, in case of success,
      -  "None", in case of failure.

   -  The `backtracking stream parsers <bparsers.html>`__ which are like
      the functional stream parsers but with a backtracking algorithm,
      testing all possibilities. These parsers also return a value of
      type "option" different from the functional stream parsers, i.e
      either:

      -  "Some" a value, the remaining stream and a continuation, in
         case of success,
      -  "None", in case of failure.

   The differences are about:

   -  Syntax errors: in the imperative version, the location of the
      error is clear, it is at the current position of the stream, and
      the system provides a specific error message (typically, that some
      "element" was "expected"). On the other hand, in the functional
      and backtracking version, the position is not clear since it
      returns nothing and the initial stream is unaffected. The only
      solution to know where the error happened is to analyze that
      stream to see how many elements have be unfrozen. No clear error
      message is available, just "syntax error" (but this could be
      improved in a future version).
   -  Power: in the imperative version, when a rule raises the exception
      "``Stream.Error``", the parsing cannot continue. In the functional
      version, the parsing can continue by analyzing the next rule with
      the initial unaffected stream: this is *limited backtrack*. In the
      backtracking version, more powerful, the parsing continues by
      analyzing the next case of the previous symbol of the rule;
      moreover it is possible to get the list of all possible solutions.
   -  Neatness: functional streams are neater, just like functional
      programming is neater than imperative programming.

   The imperative parsers implement what is called "predictive parsing",
   i.e. recursive descendant parsing without backtrack.

   In the imperative version, there also exist `lexers <lexers.html>`__,
   a shorter syntax when the stream elements are of the specific type
   '``char``'.

   .. rubric:: Extensible grammars
      :name: extensible-grammars

   Extensible grammars manipulate *grammar entries*. Grammar entries are
   abstract values internally containing mutable stream parsers. When a
   grammar entry is created, its internal parser is empty, i.e. it
   always fails when used. A specific syntactic construction, with the
   keyword "``EXTEND``" allows one to extend grammar entries with new
   grammar rules.

   In opposition to stream parsers, grammar entries manage
   associativity, left factorization, and levels. Moreover, these
   grammars allow optional calls, lists and lists with separators. They
   are not however functions and hence cannot have parameters.

   Since the internal system is stream parsers, extensible grammars use
   recursive descendant parsing.

   The parsers of the OCaml language in Camlp5 are written with
   extensible grammars.

   .. rubric:: Pretty module
      :name: pretty-module

   The "``Pretty``" module is an original tool allowing control over the
   displaying of lines. The user must specify two functions where:

   -  the data is printed on a single line
   -  the data is printed on several lines

   The system first tries to print on a single line. At any time, if the
   line overflows, i.e. if its size is greater than some "line length"
   specified in the module interface, or if it contains newlines, the
   function is aborted and control is given to the second function, to
   print on several lines.

   This is a basic, but powerful, system. It supposes that the
   programmer takes care of the current indentation, and the beginning
   and the end of its lines.

   The module will be extended in the future to hide the management of
   indendations and line continuations, and by the supply of functions
   combinating the two cases above, in which the programmer can specify
   the possible places where newlines can be inserted.

   .. rubric:: Extensible printers
      :name: extensible-printers

   The extensible printers are symmetric to the extensible grammars. The
   extensible grammars take syntax rules and return syntax trees. The
   extensible printers are actually extensible functions taking syntax
   trees as parameters and returning the pretty printed statements in
   strings.

   The extensible printers can have printing levels, just like grammars
   have parsing levels, and it is possible to take the associativity
   into account by provided functions to call either the current level
   or the next level.

   The printers of the OCaml language are written with extensible
   printers.

   .. container:: trailer
