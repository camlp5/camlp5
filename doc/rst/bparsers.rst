Backtracking parsers
====================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Backtracking parsers
      :name: backtracking-parsers
      :class: top

   Backtracking parsers are a second alternative of `stream
   parsers <parsers.html>`__ and `functional parsers <fparsers.html>`__.

   Backtracking parsers are close to functional parsers: they use the
   same stream type, "``Fstream.t``", and their syntax is almost
   identical, its introducing keyword being "``bparser``" instead of
   "``fparser``".

   The difference is that they are implemented with *full backtracking*
   and that they return values of the type "``option``" of the triplet:
   1/ value, 2/ remaining stream and 3/ continuation.

   .. container::
      :name: tableofcontents

   .. rubric:: Syntax
      :name: syntax

   The syntax of backtracking parsers is added together with the syntax
   of functional parsers, when the kit "pa_fstream.cmo" is loaded. It
   is:

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

   .. rubric:: Semantics
      :name: semantics

   .. rubric:: Algorithm
      :name: algorithm

   The backtracking parsers, like classical parsers and functional
   parsers, use a recursive descent algorithm. But:

   -  If a stream pattern component does not match the current position
      of the input stream, the control is given to the next case of the
      stream pattern component before it. If it is the first stream
      pattern component, the rule (the stream pattern) is left and the
      next rule is tested.

   For example, the following grammar:

   ::

         E -> X Y
         X -> a b | a
         Y -> b

   works, with the backtracking algorithm, for the input "``a   b``".

   Parsing with the non-terminal "``E``", the non-terminal "``X``" first
   accepts the input "``a b``" with its first rule. Then when "``Y``" is
   called, the parsing fails since nothing remains in the input stream.

   In the rule "``X Y``" of the non-terminal "``E``", the non-terminal
   "``Y``" having failed, the control is given the the continuation of
   the non-terminal "``X``". This continuation is its second rule
   containing only "``a``". Then "``Y``" is called and accepted.

   This case does not work with functional parsers since when the rule
   "``a b``" of the non-terminal "``X``" is accepted, it is definitive.
   If the input starts with "``a b``", there is no way to apply its
   second rule.

   Backtracking parsers are strictly more powerful than functional
   parsers.

   .. rubric:: Type
      :name: type

   A backtracking parser whose stream elements are of type "``t1``", and
   whose semantic actions are of some type "``t2``", is of type:

   ::

         Fstream.t t1 -> option (t * Fstream.t t1 * Fstream.kont t1 t2)

   If the backtracking parsers fails, its returning value is "``None``".

   If it succeeds, its returning value is "``Some (x, strm, k)``" where
   "``x``" is its result, "``strm``" the remaining stream, and "``k``"
   the continuation.

   The continuation is internally used in the backtracking algorithm,
   but is can also be used in the main call to compute the next
   solution, using the function "``Fstream.bcontinue``".

   It is also possible to directly get the list of all solutions by
   calling the function "``Fstream.bparse_all``".

   .. rubric:: Syntax errors
      :name: syntax-errors

   Like for `functional parsers <fparsers.html>`__, in case of syntax
   error, the error position can be found by using the function
   "``Fstream.count_unfrozen``", the token in error being the last
   unfrozen element of the stream.

   A syntax error is not really an error: for the backtracking parsers,
   like for functional parsers, it is viewed as a "non-working" case and
   another solution is searched.

   In the backtracking algorithm, depending on the grammar and the
   input, the search of the next solution can be very long. A solution
   is proposed for that in the `extensible grammars <grammars.html>`__
   system when the parsing algorithm is set to "backtracking".

   .. rubric:: Example
      :name: example

   Here is an example which just shows the backtracking algorithm but
   without parsing, an empty stream being given as parameter and never
   referred.

   It creates a list of three strings, each of them being choosen
   between ``"A"``, ``"B"`` and ``"C"``.

   The code is:

   ::

        #load "pa_fstream.cmo";
        value choice = bparser [ [: :] -> "A" | [: :] -> "B" | [: :] -> "C" ];
        value combine = bparser [: x = choice; y = choice; z = choice :] -> [x; y; z];

   The function "combine" returns the first solution:

   ::

        # combine (fstream [: :]);
        - : option (list string * Fstream.t '_a * Fstream.kont '_a (list string)) =
        Some (["A"; "A"; "A"], <abstr>, Fstream.K <fun>)

   The function "Fstream.bparse_all" returns the list of all solutions,
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

   .. container:: trailer
