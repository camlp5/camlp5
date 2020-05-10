Redefining OCaml syntax
=======================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Redefining OCaml syntax
      :name: redefining-ocaml-syntax
      :class: top

   Better than just `syntax extensions <syntext.html>`__, it is possible
   to redefine the whole syntax of the language. For example, to:

   -  define your own syntax, like the `revised syntax <revsynt.html>`__
      does,
   -  have a version whose keywords are translated in your native
      language,
   -  restrict the OCaml language,
   -  interpret XML (or other languages) as OCaml source,
   -  and so on...

   .. container::
      :name: tableofcontents

   .. rubric:: Starting with an example
      :name: starting-with-an-example

   A way to start doing this is to take, in Camlp5 sources, one of the
   files "etc/pa_o.ml" or file "meta/pa_r.ml". The first one defines the
   OCaml standard syntax and the second one the revised syntax.

   Let's say you want to take the normal syntax and make some
   readjustments. You first make a copy of "etc/pa_o.ml" naming it,
   e.g., "mysyntax.ml" (the example below works similarly if you take
   "meta/pa_r.ml" instead):

   To test, you can compile it with the command:

   ::

          ocamlc -pp camlp5r -I $(camlp5 -where) -c mysyntax.ml

   This produces the file "mysyntax.cmo". Now you can compile one of
   your files, e.g. "foo.ml", if written in this syntax, i.e. the normal
   OCaml syntax if you made no changes in "mysyntax.ml":

   ::

          ocamlc -pp 'camlp5 ./mysyntax.cmo pr_dump.cmo' -c foo.ml

   If there si no changes in "mysyntax.ml" from "pa_o.ml", this is just
   a compilation with the normal OCaml syntax. To make changes, you can
   edit the file "mysyntax.ml" and recompile it. As an exercice, try to
   translate some keywords in your native language (or another language
   if it is not English).

   Reading the way Camlp5 `extensible grammars <grammars.html>`__ and
   `syntax tree <ast_strict.html>`__ work (both used in "pa_o.ml" and
   "pa_r.ml"), you can make more complicated changes or change
   everything, if you want.

   .. rubric:: A file for an OCaml syntax
      :name: a-file-for-an-ocaml-syntax

   This is what you can find in the files "pa_o.ml" and "pa_r.ml".

   An OCaml syntax files uses the Camlp5 library module
   `Pcaml <pcaml.html>`__. All grammar entries are defined there. The
   first thing is the reinitialization of the grammar (which clear all
   tokens and define a lexer) and all grammar entries, to be sure that
   no possible previous loaded grammars remain.

   If using the same lexer (provided in Camlp5 library module
   `Plexer <library.html#a:Plexer-module>`__), it is done by:

   ::

          Grammar.Unsafe.gram_reinit Pcaml.gram (Plexer.gmake ())

   The cleanup of all grammar entries are done by calls to the function
   "Grammar.Unsafe.clear_entry". The main entries are Pcaml.interf, for
   compiling an interface (a ".mli" file) and Pcaml.implem, for
   compiling an implementation (a ".ml" file). And all other grammars
   entries you want to use must be cleared:

   ::

          Grammar.Unsafe.clear_entry Pcaml.interf;
          Grammar.Unsafe.clear_entry Pcaml.implem;
          Grammar.Unsafe.clear_entry Pcaml.expr;
          Grammar.Unsafe.clear_entry Pcaml.patt;
          ...

   Actually, the camlp5 command can compile the input file with other
   ways than using the Camlp5 grammars. The variables
   "Pcaml.parse_interf" and "Pcaml.parse_implem" are references to the
   functions called by camlp5. By default, it is the Camlp5 grammar
   syntax, but to be sure it goes on using it (if a previous load
   changed that), the following statement are added:

   ::

          Pcaml.parse_interf.val := Pcaml.Grammar.Entry.parse interf;
          Pcaml.parse_implem.val := Pcaml.Grammar.Entry.parse implem;

   In the files "pa_o.ml" and "pa_r.ml", some local functions follow,
   which are themselves followed by a call to the big statement
   "EXTEND", the main statement of the Camlp5 extensible grammars
   system.

   .. container:: trailer
