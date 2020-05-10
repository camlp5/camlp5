Syntax tree quotations in user syntax
=====================================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Syntax tree quotations in user syntax
      :name: syntax-tree-quotations-in-user-syntax
      :class: top

   The quotation kit "``q_ast.cmo``" allows to use syntax tree
   quotations in user syntax. It fully works only in "strict" mode. In
   "transitional" mode, there is no way to use antiquotations, which
   restricts its utility.

   If this kit is loaded, when a quotation of syntax tree is found, the
   current OCaml language parser is called. Then, the resulting tree is
   reified (except the antiquotations) to represent *the syntax tree of
   the syntax tree*.

   .. rubric:: Antiquotations
      :name: antiquotations

   The OCaml langage parser used, and its possible extensions, must have
   been built to allow the places of the antiquotations. The symbols
   enclosed by the meta-symbol "``V``" (see the chapter about
   `extensible grammars <grammars.html>`__, section "symbols"), define
   where antiquotations can take place.

   There is no need to specify antiquotations for the main types defined
   in the AST tree module ("``MLast``"): "``expr``", "``patt``",
   "``expr``", "``str_item``", "``sig_item``", and so on. All syntax
   parts of these types are automatically antiquotable.

   For example, in Camlp5 sources, the grammar rule defining the
   "let..in" statement is:

   ::

         "let"; r = V (FLAG "rec") "flag" "opt";
          l = V (LIST1 let_binding SEP "and"); "in"; x = expr

   All symbols of these rules, except the keywords, are antiquotable:

   -  The "rec" flag, because enclosed by the "V" meta symbol. The two
      strings which follow it gives the possible antiquotation kinds:
      "flag" (the normal antiquotation kind) and "opt" (kept by backward
      compatibility, but not recommended). It is therefore possible to
      antiquote it as: "``$flag:...$``" or "``$opt:...$``" where the
      "``...``" is an expression or a pattern depending on the position
      of the enclosing quotation
   -  The binding list is also antiquotable, since it is also enclosed
      by the "V" meta symbol. Its antiquotation kind is "list" (the
      default when the meta symbol parameter is a list). It is therefore
      possible to write "``$list:...$``" at the place of the binding
      list.
   -  The expression after the "in" is also antiquotable, because it
      belongs to the main types defined in the module "``MLast``".

   In that example, the variable "``r``" is of type
   "``Ploc.vala   bool``", the variable "``r``" of type
   "``Ploc.vala (list   (patt * expr))``" and the variable "``x``" of
   type "``MLast.expr``".

   ... to be completed ...

   .. container:: trailer
