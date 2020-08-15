Commands and Files
==================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Commands and Files
      :name: commands-and-files
      :class: top

   The main command of Camlp5 is "``camlp5``". It is an OCaml program in
   bytecode (compiled with ocamlc, not ocamlopt), able to dynamically
   load OCaml object files (ending with ".cmo" and ".cma").

   We repeat (as explained in ::ref:`introduction`) that it should
   almost never be necessary to use the ``camlp5`` command directly:
   instead, specifying ``-syntax`` and various preprocessor packages to
   ocamlfind should be sufficient.

   Most other Camlp5 commands derive from that one: they are the command
   "``camlp5``" with some implicitely applied parameters.

   Two other commands are provided: "``mkcamlp5``" and
   "``mkcamlp5.opt``". They allow to create camlp5 executables with
   already loaded kits.

   All commands have an option "``-help``" which display all possible
   command parameters and options. Notice that some parameters (the
   parsing and pretting kits) may add new options. For example, the
   command:

   ::

        camlp5 pr_r.cmo -help

   prints more lines than just:

   ::

        camlp5 -help

   The first parameter ("load options") allows to specify parsing and
   printing kits (".cmo" and ".cma" files) which are loaded inside the
   "``camlp5``" core before any action. Other options may follow.

   .. container::
      :name: tableofcontents

   .. rubric:: Parsing and Printing Kits
      :name: parsing-and-printing-kits

   .. rubric:: Parsing kits
      :name: parsing-kits

   .. rubric:: language parsing kits
      :name: language-parsing-kits

   ``pa_r.cmo``
      Revised syntax (without parsers).
   ``pa_rp.cmo``
      Add revised syntax parsers.
   ``pa_o.cmo``
      Normal syntax (without parsers). Option added:

      ``-no_quot``
         don't parse quotations, allowing to use, e.g. "``<:>``" as
         token.

   ``pa_op.cmo``
      Add normal syntax parsers.
   ``pa_oop.cmo``
      Add normal syntax parsers without code optimization.
   ``pa_lexer.cmo``
      Add stream lexers.

   .. rubric:: extensible grammars
      :name: extensible-grammars

   ``pa_extend.cmo``
      Add the EXTEND statement. Options added:

      ``-split_ext``
         split EXTEND by functions to turn around a PowerPC problem.
      ``-quotify``
         generate code for quotations (internally used to synchronize
         q_MLast and pa_r)
      ``-meta_action``
         undocumented (internally used for compiled version)

   ``pa_extfold.cmo``
      Add the specific symbols FOLD0 and FOLD1 to the EXTEND statement.

   .. rubric:: extensible functions and printers
      :name: extensible-functions-and-printers

   ``pa_extfun.cmo``
      Add the extensible function ("extfun" statement).

   ``pa_extprint.cmo``
      Add the EXTEND_PRINTER statement.

   .. rubric:: functional parsers
      :name: functional-parsers

   ``pa_fstream.cmo``
      Add the functional parsers ("fparser" statement) and the
      backtracking parsers ("bparser" statement).

   .. rubric:: other languages
      :name: other-languages

   ``pa_lisp.cmo``
      Lisp syntax.
   ``pa_scheme.cmo``
      Scheme syntax.
   ``pa_sml.cmo``
      SML syntax.

   .. rubric:: other parsing kits
      :name: other-parsing-kits

   ``pa_lefteval.cmo``
      Add guarantee of left evaluation in functions calls.
   ``pa_macro.cmo``
      Add macros. Options added:

      ``-D <string>``
         define for IFDEF statement
      ``-U <string>``
         undefine for IFDEF statement
      ``-defined``
         print the defined macros and exit

   ``pa_pragma.cmo``
      Add pragma directive: evaluations at parse time

   .. rubric:: Printing kits
      :name: printing-kits

   .. rubric:: language printing kits
      :name: language-printing-kits

   ``pr_r.cmo``
      Display in revised syntax. Added options:

      ``-flag <str>``
         Change pretty printing behaviour according to "``<str>``":
         A/a enable/disable all flags
         C/c enable/disable comments in phrases
         D/d enable/disable allowing expanding 'declare'
         E/e enable/disable equilibrate cases
         L/l enable/disable allowing printing 'let..in' horizontally
         S/s enable/disable printing sequences beginners at end of lines
         default setting is "aS".
      ``-wflag <str>``
         Change displaying 'where' statements instead of 'let':
         A/a enable/disable all flags
         I/i enable/disable 'where' after 'in'
         L/l enable/disable 'where' after 'let..='
         M/m enable/disable 'where' after 'match' and 'try'
         P/p enable/disable 'where' after left parenthesis
         R/r enable/disable 'where' after 'record_field..='
         S/s enable/disable 'where' in sequences
         T/t enable/disable 'where' after 'then' or 'else'
         V/v enable/disable 'where' after 'value..='
         W/w enable/disable 'where' after '``->``'
         default setting is "Ars".
      ``-l <length>``
         Maximum line length for pretty printing (default 78)
      ``-sep_src``
         Read source file for text between phrases (default).
      ``-sep <string>``
         Use this string between phrases instead of reading source.

   ``pr_ro.cmo``
      Add display objects, labels and variants in revised syntax.
   ``pr_rp.cmo``
      Add display parsers with their (revised) syntax.
   ``pr_o.cmo``
      Display in normal syntax. Added options:

      ``-flag <str>``
         Change pretty printing behaviour according to ``<str>``:
         A/a enable/disable all flags
         C/c enable/disable comments in phrases
         E/e enable/disable equilibrate cases
         L/l enable/disable allowing printing 'let..in' horizontally
         M/m enable/disable printing double semicolons
         default setting is "Am".
      ``-l <length>``
         Maximum line length for pretty printing (default 78)
      ``-sep_src``
         Read source file for text between phrases (default).
      ``-sep <string>``
         Use this string between phrases instead of reading source.

   ``pr_op.cmo``
      Add displaying parsers with their (normal) syntax.

   .. rubric:: extensible parsers
      :name: extensible-parsers

   ``pr_extend.cmo``
      Add the displaying of EXTEND statements in their initial
      syntax.Option added:

      ``-no_slist``
         Don't reconstruct SLIST, SOPT, SFLAG

   .. rubric:: extensible functions and printers
      :name: extensible-functions-and-printers-1

   ``pr_extfun.cmo``
      Add displaying extensible functions ("extfun" statement) in their
      initial syntax.

   ``pr_extprint.cmo``
      Add displaying extensible printers ("EXTEND_PRINTER" statement) in
      their initial syntax.

   .. rubric:: other language
      :name: other-language

   ``pr_scheme.cmo``
      Display in Scheme syntax. Option added:

      ``-l <length>``
         Maximum line length for pretty printing (default 78)
      ``-sep <string>``
         Use this string between phrases instead of reading source.

   ``pr_schemep.cmo``
      Add display parsers with their (Scheme) syntax.

   .. rubric:: other printing kits
      :name: other-printing-kits

   ``pr_depend.cmo``
      Display dependencies. Option added:

      ``-I dir``
         Add "dir" to the list of search directories.

   ``pr_dump.cmo``
      Dump the syntax tree in binary (for the OCaml compiler)
   ``pr_null.cmo``
      No output.

   .. rubric:: Quotations expanders
      :name: quotations-expanders

   ``q_MLast.cmo``
      Syntax tree quotations. Define the quotations named: "expr",
      "patt", "ctyp", "str_item", "sig_item", "module_type",
      "module_expr", "class_type", "class_expr", "class_sig_item",
      "class_str_item", "with_constr" and "poly_variant".
   ``q_phony.cmo``
      Transform quotations into phony variables to be able to pretty
      print the quotations in their initial form (not suitable for
      compilation)

   .. rubric:: Commands
      :name: commands

   ``camlp5r``
      Shortcut for "``camlp5 pa_r.cmo pa_rp.cmo pr_dump.cmo``"
   ``camlp5r.opt``
      Same as previous, but in native code instead of bytecode,
      therefore faster. But not extensible: it is not possible to add
      other parsing or printing kits neither in command arguments nor
      with the "load" directive inside sources. Suitable for compiling
      sources not using other syntax extensions.
   ``camlp5o``
      Shortcut for "``camlp5 pa_o.cmo pa_op.cmo pr_dump.cmo``"
   ``camlp5o.opt``
      Same as previous, and like "``camlp5r.opt``", faster and not
      extensible. Moreover, this has been produced by compilation of
      Camlp5 grammars, resulting in a still faster executable.
   ``camlp5sch``
      Shortcut for "``camlp5 pa_scheme.cmo pr_dump.cmo``"
   ``mkcamlp5``
      creates camlp5 executables with almost the same options than
      ocamlmktop. The interfaces to be visible must be explicitly added
      in the command line as ".cmi" files. ``mkcamlp5`` is a wrapper around
      ``ocamlfind``, and typically arguments to ocamlfind are passed-thru.
      So for instance, to add the OCaml module "str":
      "``mkcamlp5 -package camlp5,str str.cmi -o camlp5str``"
   ``mkcamlp5.opt``
      creates camlp5 executables like ``mkcamlp5``, except that it is in
      native code, therefore faster, but not extensible; the added kits
      must be ocamlfind packages (or cmx or cmxa files)

   .. rubric:: Environment variable
      :name: environment-variable

   When running a program using extensible grammars (in particular, the
   camlp5 commands), the environment variable "``CAMLP5PARAM``" is
   consulted. It sets the grammar parsing algoritm parameters.

   This variable must be a sequence of parameter specifications. A
   parameter specification is a letter optionally followed by an = and a
   value, with any separator. There are four possible parameters:

   ``b``
      Set the full backtrack algorithm as default.
   ``f``
      Set the limited backtrack algorithm as default.
   ``t``
      Trace symbols (terminals and non-terminals) while parsing with
      backtracking.
   ``y``
      In backtracking, trace the advance in the input stream (number of
      unfrozen tokens) and the possible stalling (number of tokens
      tests).
   ``l=value``
      Set the maximum stalling value.

   .. rubric:: OCaml toplevel files
      :name: ocaml-toplevel-files

   These object files can be loaded in the OCaml toplevel to make Camlp5
   parse the input. It is possible to load them either by putting them
   as parameters of the toplevel, or by using the directive "load". The
   option "``-I +camlp5``" (or ":literal:`-I   `camlp5 -where\``") must
   be added to the "``ocaml``" command (the OCaml toplevel).

   ``camlp5r.cma``
      Read phrases and display results in revised syntax
   ``camlp5o.cma``
      Read phrases and display results in normal syntax
   ``camlp5sch.cma``
      Read phrases in Scheme syntax

   .. rubric:: Library files
      :name: library-files

   The `Camlp5 library <library.html>`__ is named "``gramlib.cma``" and
   its native code version is "``gramlib.cmxa``". They contain the
   modules:

   -  Ploc : building and combining `locations <locations.html>`__
   -  Plexing : lexing for Camlp5 grammars
   -  Plexer : lexer used in revised and normal syntax
   -  Gramext : implementation of extensible grammars
   -  Grammar : `extensible grammars <grammars.html>`__
   -  Extfold : functions for grammar extensions FOLD0 and FOLD1
   -  Extfun : functions for `extensible functions <extfun.html>`__
   -  Eprinter : `extensible printers <printers.html>`__
   -  Fstream : `functional streams <fparsers.html>`__
   -  Pretty : `pretty printing <pretty.html>`__ on strings

   This is a pure library : when linking with it, the Camlp5 program is
   *not* included.

   .. container:: trailer
