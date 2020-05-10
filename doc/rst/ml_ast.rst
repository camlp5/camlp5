Syntax tree
===========

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Syntax tree
      :name: syntax-tree
      :class: top

   In Camlp5, one often uses syntax trees. For example, in grammars of
   the language (semantic actions), in pretty printing (as patterns), in
   optimizing syntax code (typically stream parsers). Syntax trees are
   mainly defined by sum types, one for each kind of tree: "``expr``"
   for expressions, "``patt``" for patterns, "``ctyp``" for types,
   "``str_item``" for structure items, and so on. Each node corresponds
   to a possible value of this type.

   .. container::
      :name: tableofcontents

   .. rubric:: Transitional and Strict modes
      :name: transitional-and-strict-modes

   Since version 5.00 of Camlp5, the definition of the syntax tree has
   been different according to the mode Camlp5 has been installed:

   -  In `transitional <ast_transi.html>`__ mode, this definition is the
      same than in the previous Camlp5 versions.
   -  In `strict <ast_strict.html>`__ mode, many constructor parameters
      have a type enclosed by the predefined type "``Ploc.vala``".

   The advantage of the transitional mode is that the abstract syntax
   tree is fully compatible with previous versions of Camlp5. Its
   drawback is that when using the `syntax tree quotations in user
   syntax <q_ast.html>`__, it is not possible to use antiquotations, a
   significatant limitation.

   In strict mode, the abstract syntax is not compatible with versions
   of Camlp5 previous to 5.00. Most of the parameters of the constructor
   are enclosed with the type "``Ploc.vala``" whose aim is to allow
   nodes to be either of the type argument, or an antiquotation. In this
   mode, the syntax tree quotations in user syntax can be used, with the
   same power of the previous syntax tree quotations provided by Camlp5.

   .. rubric:: Compatibility
      :name: compatibility

   As there is a problem of compatibility in strict mode, a good
   solution, for the programmer, is to always use syntax trees using
   quotations, which is backward compatible. See the chapter about
   `syntax tree in strict mode <ast_strict.html>`__.

   For example, if the program made a value of the syntax tree of the
   "let" statement, like this:

   ::

        ExLet loc rf pel e

   In strict mode, to be equivalent, this expression should be rewritten
   like this:

   ::

        ExLet loc (Ploc.VaVal rf) (Ploc.VaVal pel) e

   where "``Ploc.VaVal``" is a value of the type "``vala``" defined in
   the module `Ploc <library.html>`__ (see its section "pervasives").

   This necessary conversion is a drawback if the programmer wants that
   his programs remain compilable with previous versions of Camlp5.

   The recommended solution is to always write this code with
   quotations, namely, in this example, like this:

   ::

        <:expr< let $flag:rf$ $list:pel$ in $e$ >>

   The quotation expanders ensure that, in strict mode, the variable
   "rf" is still of type "``bool``", and that the variable "pel" of type
   "``list (patt * expr)``", by enclosing them around "``Ploc.VaVal``".

   In transitional mode, it is equivalent to the first form above. In
   strict mode, it is equivalent to the second form. And the previous
   versions of Camlp5 also recognizes this form.

   .. rubric:: Two quotations expanders
      :name: two-quotations-expanders

   Camlp5 provides two quotations expanders of syntax trees:
   "``q_MLast.cmo``" and "``q_ast.cmo``".

   Both allow writing syntax trees in concrete syntax as explained in
   the previous section.

   The first one, "``q_MLast.cmo``" requires that the contents of the
   quotation be in `revised syntax <revsynt.html>`__ without any syntax
   extension (even the `stream parsers <parsers.html>`__). It works in
   transitional and in strict modes.

   The second one, "``q_ast.cmo``" requires that the contents of the
   quotation be in the current user syntax (normal, revised, lisp,
   scheme, or other) and can accept all the syntax extensions he added
   to compile his program. It fully works only in strict mode. In
   transitional mode, the antiquotations are not available.

   .. rubric:: Syntax tree and Quotations in the two modes
      :name: syntax-tree-and-quotations-in-the-two-modes

   For the detail of the syntax tree and the quotations forms, see the
   chapters about the `syntax tree in transitional
   mode <ast_transi.html>`__ and the `syntax tree in strict
   mode <ast_strict.html>`__.

   .. container:: trailer
