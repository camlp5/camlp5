Directives
==========

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Directives
      :name: directives
      :class: top

   Directives in normal or revised syntax are statements at top level,
   or, more generally, as signature items or structure items, which
   stops the preprocessor for evaluate things - which can change the
   behaviour of the preprocessor, for example to add syntax, load syntax
   extensions and so on. After the directive is evaluated, the parsing
   resumes.

   Directives begin with '#', followed by an identifier, and,
   optionnally by an expression. They are usable in source files the and
   generally in the ocaml toplevel too.

   Four predefined directives exist: #load, #directory, #option and
   #use. It is also possible to add other directives. An example of that
   is the parsing kit `pa_pragma.cmo <pragma.html>`__ which adds a new
   directive #pragma.

   .. container::
      :name: tableofcontents

   .. rubric:: Predefined directives
      :name: predefined-directives

   The predefined directives are:

   .. rubric:: #load "name"
      :name: load-name

   Loads an object file (ocaml cmo or cma file) in the core, evaluating
   it. This is typically to be used in the ocaml toplevel to add an
   syntax extension kit.

   For example, in the toplevel, loading the `quotation <quot.html>`__
   expander of `ocaml syntax trees <ast_strict.html>`__:

   ::

        # #load "q_MLast.cmo";

        # value loc = Ploc.dummy;
        value loc : Ploc.t = <abstr>

        # <:expr< fun x -> x >>;
        - : MLast.expr =
        MLast.ExFun <abstr>
          (Ploc.VaVal
             [(MLast.PaLid <abstr> (Ploc.VaVal "x"), Ploc.VaVal None,
               MLast.ExLid <abstr> (Ploc.VaVal "x"))])

   In a source file, the '#load' directive is equivalent to put the
   object file as camlp5 parameter among the 'load options':

   ::

         $ cat myfile.ml

         #load "pa_extend.cmo";
         value g = Grammar.gcreate (Plexer.gmake ());
         value e = Grammar.Entry.create g "e";

         EXTEND e: [[ i = INT -> i ]]; END;

         $ ocamlc -pp camlp5r -I +camlp5 -c myfile.ml

   which is equivalent to, without using '#load':

   ::

         $ cat myfile2.ml

         value g = Grammar.gcreate (Plexer.gmake ());
         value e = Grammar.Entry.create g "e";

         EXTEND e: [[ i = INT -> i ]]; END;

   and compiling it like this:

   ::

         $ ocamlc -pp 'camlp5r pa_extend.cmo' -I +camlp5 -c myfile2.ml

   .. rubric:: #directory "name"
      :name: directory-name

   Adds a new directory in the camlp5 path searching for loaded files
   (using the directive #load above). This is equivalent to the option
   '-I' of the camlp5 command. See the camlp5 man page.

   .. rubric:: #use "name"
      :name: use-name

   Loads a source file name. Useful in the ocaml toplevel to test a
   source file.

   .. rubric:: #option "option"
      :name: option-option

   Adds an option as if it were added in camlp5 command line (to be used
   in a source file, not in the ocaml toplevel). Implemented only on
   options without an extra parameter.

   For example, the syntax kit `pa_extend.cmo <grammars.html>`__ adds an
   option named '-split_ext'. This can be viewed through the command:

   ::

        camlp5r pa_extend.cmo -help

   Thanks to the directive '#option', the following command in the
   shell:

   ::

        $ camlp5r pa_extend.cmo -split_ext file.ml

   can be used only as:

   ::

        $ camlp5r file.ml

   providing the file starts with:

   ::

        #load "pa_extend.cmo";
        #option "-split_ext";

   .. rubric:: User directives
      :name: user-directives

   It is possible to add any extra directive. The syntax kit
   `pragma.cmo <pragma.html>`__, for example, adds a directive named
   '#pragma'.

   A user syntax kit can add its directives using the function
   "add_directive" of the module `Pcaml <pcaml.html>`__.

   .. container:: trailer
