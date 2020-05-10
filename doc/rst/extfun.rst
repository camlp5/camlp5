Extensible functions
====================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Extensible functions
      :name: extensible-functions
      :class: top

   Extensible functions allows the definition of pattern matching
   functions which are extensible by adding new cases that are inserted
   automatically at the proper place by comparing the patterns. The
   pattern cases are ordered according to syntax trees representing
   them, "when" statements being inserted before the cases without
   "when".

   Notice that extensible functions are functional: when extending a
   function, a new function is returned.

   The extensible functions are used in the `pretty
   printing <pretty.html>`__ system of Camlp5.

   .. container::
      :name: tableofcontents

   .. rubric:: Syntax
      :name: syntax

   The syntax of the extensible functions, when loading "pa_extfun.cmo",
   is the following:

   ::

                 expression ::= extensible-function
        extensible-function ::= "extfun" expression "with" "[" match-cases "]"
                match-cases ::= match-case "|" match-cases
                 match-case ::= pattern "->" expression
                              | pattern "when" expression "->" expression

   It is an extension of the same syntax as the "match" and "try"
   constructions.

   .. rubric:: Semantics
      :name: semantics

   The statement "extend" defined by the syntax takes an extensible
   function and return another extensible function with the new match
   cases inserted at the proper place within the initial extensible
   function.

   Extensible functions are of type "``Extfun.t a b``", which is an
   abstract type, where "``a``" and "``b``" are respectively the type of
   the patterns and the type of the expressions. It corresponds to a
   function of type "``a -> b``".

   The function "``Extfun.apply``" takes an extensible function as
   parameter and returns a function which can be applied like a normal
   function.

   The value "``Extfun.empty``" is an empty extensible function, of type
   "``Extfun.t 'a 'b``". When applied with "``Extfun.apply``" and a
   parameter, it raises the exception "``Extfun.Failure``" whatever the
   parameter.

   For debugging, it is possible to use the function "``Extfun.print``"
   which displays the match cases of the extensible functions. (Only the
   patterns are displayed in clear text, the associated expressions are
   not.)

   The match cases are inserted according to the following rules:

   -  The match cases are inserted in the order they are defined in the
      syntax "``extend``"
   -  A match case pattern with "when" is inserted before a match case
      pattern without "when".
   -  Two match cases patterns both with "when" or both without "when"
      are inserted according to the alphabetic order of some internal
      syntax tree of the patterns where bound variables names are not
      taken into account.
   -  If two match cases patterns without "when" have the same patterns
      internal syntax tree, the initial one is silently removed.
   -  If two match cases patterns with "when" have the same patterns
      internal syntax tree, the new one is inserted before the old one.

   .. container:: trailer
