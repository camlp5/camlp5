Transitional and Strict modes
=============================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Transitional and Strict modes
      :name: transitional-and-strict-modes
      :class: top

   Since version 5.00, Camlp5 has been able to be installed in two
   modes: the *transitional* mode and the *strict* mode. When Camlp5 is
   installed, it works with one only of these modes (the two modes
   contain indeed different definitions of some interfaces and are
   incompatible with one another). The user must choose in which mode he
   wants to use Camlp5.

   This notion has been introduced to ensure backward compatibility of
   the Camlp5 syntax tree, together with the usage of a new quotation
   kit "``q_ast.cmo``", which allows to use Camlp5 syntax tree
   quotations in user syntax (with all its possible extensions).

   A short example of these syntax tree quotations:
      If the syntax of the `extensible grammars <grammars.html>`__ has
      been added, it is possible to write things like:

      ::

           <:expr< EXTEND a: [ [ c = d -> $e$ ] ]; END >>;

      representing the syntax tree of this statement: this is not
      possible with the classical quotation kit "``q_MLast.cmo``"
      because all quotations must be there only in `revised
      syntax <revsynt.html>`__ and without syntax extensions.

   Here are the differences between the two modes:

   Transitional
      Compatibility
         The syntax tree is fully compatible with the previous versions
         of Camlp5, no changes has to be done in the users' programs.
      Quotation kit "``q_ast.cmo``"
         The antiquotations are not available: when used, a syntax error
         message is displayed.

   Strict
      Compatibility
         The syntax tree is different, users' programs may have to be
         modified, but not necessarily.
      Quotation kit "``q_ast.cmo``"
         All antiquotations are available.

   In strict mode, the programs have more chances to be compatible with
   the previous versions if they use syntax tree quotations rather than
   syntax tree nodes. A solution is therefore to change the expressions
   and patterns using nodes into expressions and patterns using
   quotations (which is backward compatible).

   .. rubric:: Which mode is installed ?
      :name: which-mode-is-installed

   To determine the mode of an installed version of Camlp5, type:

   ::

        camlp5 -pmode

   .. rubric:: Selecting mode when compiling Camlp5
      :name: selecting-mode-when-compiling-camlp5

   When compiling Camlp5 from source, the mode must first be selected at
   configuration time. The *configure* script must be run with one of
   these options:

   ::

        ./configure -strict
        ./configure -transitional

   The default is "transitional", i.e. without option, the sources are
   compiled in transitional mode.

   .. container:: trailer
