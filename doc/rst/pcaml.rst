The Pcaml module
================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: The Pcaml module
      :name: the-pcaml-module
      :class: top

   All about language parsing entries, language printing functions,
   quotation management at parsing time, extensible directives,
   extensible options, and generalities about Camlp5.

   .. container::
      :name: tableofcontents

   .. rubric:: Language parsing
      :name: language-parsing

   .. rubric:: Main parsing functions
      :name: main-parsing-functions

   | The two functions below are called when parsing an interface (.mli
     file) or an implementation (.ml file) to build the syntax tree; the
     returned list contains the phrases (signature items or structure
     items) and their locations; the boolean tells whether the parser
     has encountered a directive; in this case, since the directive may
     change the syntax, the parsing stops, the directive is evaluated,
     and this function is called again.
   | These functions are references, because they can be changed to use
     another technology than the Camlp5 extended grammars. By default,
     they use the grammars entries [implem] and [interf] defined below.

   ::

      value parse_interf :
        ref (Stream.t char -> (list (MLast.sig_item * MLast.loc) * bool));

   Function called when parsing an interface (".mli") file
   ::

      value parse_implem :
        ref (Stream.t char -> (list (MLast.str_item * MLast.loc) * bool));

   Function called when parsing an implementation (".ml") file
   .. rubric:: Grammar
      :name: grammar

   ``value gram : Grammar.g;``
      Grammar variable of the language.

   .. rubric:: Entries
      :name: entries

   Grammar entries which return `syntax trees <ml_ast.html>`__. These
   are set by the parsing kit of the current syntax, through the
   statement `EXTEND <grammars.html>`__. They are usable by other
   possible user syntax extensions.

   ``value expr : Grammar.Entry.e MLast.expr;``
      Expressions.
   ``value patt : Grammar.Entry.e MLast.patt;``
      Patterns.
   ``value ctyp : Grammar.Entry.e MLast.ctyp;``
      Types.

   ``value sig_item : Grammar.Entry.e MLast.sig_item;``
      Signature items, i.e. items between "``sig``" and "``end``", or
      inside an interface (".mli") file.
   ``value str_item : Grammar.Entry.e MLast.str_item;``
      Structure items, i.e. items between "``struct``" and "``end``", or
      inside an implementation (".ml") file.

   ``value module_type : Grammar.Entry.e MLast.module_type;``
      Module types, e.g. signatures, functors, identifiers.
   ``value module_expr : Grammar.Entry.e MLast.module_expr;``
      Module expressions, e.g. structures, functors, identifiers.

   ``value let_binding : Grammar.Entry.e (MLast.patt *       MLast.expr);``
      Specific entry for the "let binding", i.e. the association "let
      pattern = expression".
   ``value type_declaration : Grammar.Entry.e       MLast.type_decl;``
      Specific entry for the "type declaration", i.e. the association
      "type name = type-expression"

   ``value class_sig_item : Grammar.Entry.e       MLast.class_sig_item;``
      Class signature items, i.e. items of class objects types.
   ``value class_str_item : Grammar.Entry.e       MLast.class_str_item;``
      Class structure items, i.e. items of class objects.
   ``value class_type : Grammar.Entry.e MLast.class_type;``
      Class types, e.g. object types, class types functions,
      identifiers.
   ``value class_expr : Grammar.Entry.e MLast.class_expr;``
      Class expressions, e.g. objects, class functions, identifiers.

   ``value interf : Grammar.Entry.e (list (MLast.sig_item * MLast.loc) * bool);``
      Interface, i.e. files with extension ".mli". The location is the
      top of the tree. The boolean says whether the parsing stopped
      because of the presence of a directive (which potentially could
      change the syntax).
   ``value implem : Grammar.Entry.e (list (MLast.str_item * MLast.loc) * bool);``
      Implementation, i.e. files with extension ".ml". Same remark about
      the location and the boolean.
   ``value top_phrase : Grammar.Entry.e (option       MLast.str_item);``
      Phrases of the OCaml interactive toplevel. Return "None" in case
      of end of file.
   ``value use_file : Grammar.Entry.e (list MLast.str_item *       bool);``
      Phrases in files included by the directive "``#use``". The boolean
      indicates whether the parsing stopped because of a directive (as
      for "``interf``" above).

   .. rubric:: Language printing
      :name: language-printing

   .. rubric:: Main printing functions
      :name: main-printing-functions

   | The two function below are called when printing an interface (.mli
     file) of an implementation (.ml file) from the syntax tree; the
     list is the result of the corresponding parsing function.
   | These functions are references, to allow using other technologies
     than the Camlp5 extended printers.

   ::

      value print_interf :
        ref (list (MLast.sig_item * MLast.loc) -> unit);

   Function called when printing an interface (".mli") file
   ::

      value print_implem :
        ref (list (MLast.str_item * MLast.loc) -> unit);

   Function called when printing an implementation (".ml") file
   By default, these functions fail. The printer kit "``pr_dump.cmo``"
   (loaded by most Camlp5 commands) sets them to functions dumping the
   syntax tree in binary (for the OCaml compiler). The pretty printer
   kits, such as "``pr_r.cmo``" and "``pr_o.cmo``" set them to functions
   calling the predefined printers (see next section).

   .. rubric:: Printers
      :name: printers

   Printers taking `syntax trees <ml_ast.html>`__ as parameters and
   returning pretty printed strings. These are set by the printing kits,
   through the statement `EXTEND_PRINTER <printers.html>`__. They are
   usable by other possible user printing extensions.

   ``value pr_expr : Eprinter.t MLast.expr;``
      Expressions.
   ``value pr_patt : Eprinter.t MLast.patt;``
      Patterns.
   ``value pr_ctyp : Eprinter.t MLast.ctyp;``
      Types.

   ``value pr_sig_item : Eprinter.t MLast.sig_item;``
      Signature items, i.e. items between "``sig``" and "``end``", or
      inside an interface (".mli") file.
   ``value pr_str_item : Eprinter.t MLast.str_item;``
      Structure items, i.e. items between "``struct``" and "``end``", or
      inside an implementation (".ml") file.

   ``value pr_module_type : Eprinter.t MLast.module_type;``
      Module types, e.g. signatures, functors, identifiers.
   ``value pr_module_expr : Eprinter.t MLast.module_expr;``
      Module expressions, e.g. structures, functors, identifiers.

   ``value pr_class_sig_item : Eprinter.t       MLast.class_sig_item;``
      Class signature items, i.e. items of class objects types.
   ``value pr_class_str_item : Eprinter.t       MLast.class_str_item;``
      Class structure items, i.e. items of class objects.
   ``value pr_class_type : Eprinter.t MLast.class_type;``
      Class types, e.g. object types, class types functions,
      identifiers.
   ``value pr_class_expr : Eprinter.t MLast.class_expr;``
      Class expressions, e.g. objects, class functions, identifiers.

   .. rubric:: Quotation management
      :name: quotation-management

   ``value handle_expr_quotation : MLast.loc -> (string * string)       -> MLast.expr;``
      Called in the semantic actions of the rules parsing a quotation in
      position of expression.
   ``value handle_patt_quotation : MLast.loc -> (string * string)       -> MLast.patt;``
      Called in the semantic actions of the rules parsing a quotation in
      position of pattern.

   ``value quotation_dump_file : ref (option string);``
      "``Pcaml.quotation_dump_file``" optionally tells the compiler to
      dump the result of an expander (of kind "generating a string") if
      this result is syntactically incorrect. If "``None``" (default),
      this result is not dumped. If "``Some       fname``", the result
      is dumped in the file "``fname``". The same effect can be done
      with the option "``-QD``" of Camlp5 commands.
   ``value quotation_location : unit -> Ploc.t;``
      While expanding a quotation, returns the location of the quotation
      text (between the quotation quotes) in the source; raises
      "``Failure``" if not in the context of a quotation expander.

   .. rubric:: Extensible directives and options
      :name: extensible-directives-and-options

   ``type directive_fun = option MLast.expr -> unit;``
      The type of functions called to treat a directive with its
      syntactic parameter. Directives act by side effect.
   ``value add_directive : string -> directive_fun -> unit;``
      Add a new directive.
   ``value find_directive : string -> directive_fun;``
      Find the function associated with a directive. Raises
      "``Not_found``" if the directive does not exists.

   ``value add_option : string -> Arg.spec -> string -> unit;``
      Add an option to the command line of the Camlp5 command.

   .. rubric:: Equalities over syntax trees
      :name: equalities-over-syntax-trees

   These equalities skip the locations.

   ::

      value eq_expr : MLast.expr -> MLast.expr -> bool;
      value eq_patt : MLast.patt -> MLast.patt -> bool;
      value eq_ctyp : MLast.ctyp -> MLast.ctyp -> bool;
      value eq_str_item : MLast.str_item -> MLast.str_item -> bool;
      value eq_sig_item : MLast.sig_item -> MLast.sig_item -> bool;
      value eq_module_expr : MLast.module_expr -> MLast.module_expr -> bool;
      value eq_module_type : MLast.module_type -> MLast.module_type -> bool;
      value eq_class_sig_item : MLast.class_sig_item -> MLast.class_sig_item -> bool;
      value eq_class_str_item : MLast.class_str_item -> MLast.class_str_item -> bool;
      value eq_class_type : MLast.class_type -> MLast.class_type -> bool;
      value eq_class_expr : MLast.class_expr -> MLast.class_expr -> bool;

   .. rubric:: Generalities
      :name: generalities

   ``value version : string;``
      The current version of Camlp5.

   ``value syntax_name : ref string;``
      The name of the current syntax. Set by the loaded syntax kit.

   ``value input_file : ref string;``
      The file currently being parsed.

   ``value output_file : ref (option string);``
      The output file, stdout if None (default).

   ``value no_constructors_arity : ref bool;``
      True if the current syntax does not generate constructor arity,
      which is the case of the normal syntax, and not of the revised
      one. This has an impact when converting Camlp5 syntax tree into
      OCaml compiler syntax tree.

   .. container:: trailer
