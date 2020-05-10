Camlp5 sources
==============

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Camlp5 sources
      :name: camlp5-sources
      :class: top

   Information for developpers of the Camlp5 program.

   .. container::
      :name: tableofcontents

   .. rubric:: Kernel
      :name: kernel

   The sources are composed of:

   -  the OCaml stuff, copied from the OCaml compiler
   -  the *kernel* composed of the directories:

      -  odyl : the dynamic loading system
      -  lib : the library
      -  main : the main program camlp5
      -  meta : the parsers for revised syntax, ast quotations, EXTEND
         statement, etc/

   -  the rest: directories etc, compile, ocpp

   Some other directories contain configuration files, tools,
   documentation and manual pages.

   The kernel is sufficient to make the core system work: it is possible
   to compile and bootstrap only it. All sources being in revised
   syntax, the first compilation of Camlp5 is done by a version of this
   kernel in pure OCaml syntax, located in the directory ocaml_src.

   These sources in pure OCaml syntax are not modified by hand. When
   changes are made to the kernel, and a check is done that it correctly
   compiles and bootstraps, the kernel in pure OCaml syntax is rebuilt
   using Camlp5 pretty print. This is done by the command "make
   bootstrap_sources".

   .. rubric:: Compatibility
      :name: compatibility

   This distribution of Camlp5 is compatible with several versions of
   OCaml. The definition of OCaml syntax trees may change from OCaml
   version to version, which can be a problem. Since OCaml does not
   install the sources nor the compiled versions of its syntax tree, a
   copy of the necessary source files, borrowed from the source of the
   OCaml compiler is in the directory 'ocaml_stuff', in subdirectories
   with the OCaml version number.

   If the present distribution of Camlp5 is not compatible with the
   version of OCaml you have (the command 'configure' tells you), it is
   possible to add it. For that, you need the sources to your specific
   OCaml distribution. If you have them then a 'configure' telling you
   that camlp5 is not compatible, do:

   ::

        make steal OCAML_SRC=<path-to-OCaml-sources>

   This creates a new directory in 'ocaml_stuff' with sources of the
   syntax tree of your OCaml compiler.

   If you want to check that the sources of the syntax tree of OCaml are
   up-to-date (e.g. if this is the current OCaml developpement), do:

   ::

        make compare_stolen OCAML_SRC=<path-to-OCaml-sources>

   The compatibility is also done with the file 'lib/versdep.ml', which
   is a module containing miscellaneous features depending to the
   version of OCaml.

   In the directory 'ocaml_src' which contains the pure OCaml sources of
   the Camlp5 core (see chapter TREE STRUCTURE below), there are as many
   versions of this files as versions of OCaml. They are named
   'version.ml' in the directory 'lib/versdep'. If you are adding a new
   version of OCaml, you need this file. As a first step, make a copy
   from a close version:

   ::

        cd ocaml_src/lib/versdep
        cp <close_version>.ml <version>.ml

   Then, you can rerun "configure" and do "make core". If the file
   'ocaml_src/lib/versdep.ml' has compilation problems, fix them 'make
   core' again. When it compiles, copy it into the subdirectory
   'versdep' as '<version>.ml', overwriting the version you copied from
   the close version.

   Later, the same file 'lib/versdep.ml' in Camlp5 syntax may have
   similar compilation problems. There is only a single version of this
   file, thanks to IFDEF constructs used here or there.

   While compiling with some specific version of OCaml, this file is
   compiled with 'OCAML_vers' defined where 'vers' is the version number
   form the beginning to the first space or charcter '+' with all dots
   converted into underscores. For example, if your OCaml version is
   7.04.2+dev35, you can see in the compilation process of versdep.ml
   that OCAML_7_04_2 is defined, and you can add statements defined by
   the syntax extension 'pa_macro.cmo', for example IFDEF OCAML_7_04_2.
   Add statements like that in 'lib/versdep.ml' to make it compile
   successfully.

   .. rubric:: Tree structure
      :name: tree-structure

   The directory 'ocaml_src' contains images in pure OCaml syntax of the
   directories odyl lib main and meta. This allows the creation of a
   core version of Camlp5 with only the OCaml compiler installed.

   You can decompose the building of the Camlp5 core into:

   1. make library_cold
      just makes the directory 'ocaml_src/lib' and copy the cmo and cmi
      files into the directory 'boot'
   2. make compile_cold
      makes the other directories of ocaml_src
   3. make promote_cold
      copies the executables "camlp5", "camlp5r" and the syntax
      extensions (cmo files) into the directory 'boot'

   From this point, the core Camlp5 is in directory 'boot'. The real
   sources in the top directories odyl, lib, main and meta, which are
   written in revised syntax with some syntax extensions (grammars,
   quotations) can be compiled. To achieve their compilation, you can
   do:

   ::

        make core

   Or to compile everything do:

   ::

        make all

   or just:

   ::

        make

   Notice that doing "make core" or "make all" from scratch (after a
   make clean), automatically starts by making the core files from their
   pure OCaml versions.

   .. rubric:: Fast compilation from scratch
      :name: fast-compilation-from-scratch

   ::

        ./configure
        make clean core compare
        make coreboot
        make all opt opt.opt

   .. rubric:: Testing changes
      :name: testing-changes

   1. do your changes

   2. do:

   ::

        make core compare

   if it says that the bootstrap is ok, you can do:

   ::

        make all
        make opt
        make opt.opt

   otherwise, to make sure everything is ok, first do:

   ::

        make coreboot

   sometimes two bootstraps ('make coreboot' twice) are necessary, in
   particular if you change things in the directory 'lib'. It is even
   possible that three bootstraps are necessary.

   If things go wrong, it is possible to return to the previous version
   by typing:

   ::

        make restore clean_hot

   then you can change what is necessary and continue by typing:

   ::

        make core

   and test the bootstrap again:

   ::

        make coreboot

   After several bootstraps (by 'make coreboot' or 'make bootstrap'),
   many versions are pushed in the directory 'boot' (you can type 'find
   boot -type d -print' to see that). If your system correctly
   bootstraps, you can clean that by typing:

   ::

        make cleanboot

   which keeps only two versions. (The command 'make clean' also removes
   these stack of versions.)

   .. rubric:: Before committing your changes
      :name: before-committing-your-changes

   Make sure that the cold start with pure OCaml sources work. For that,
   do:

   ::

        make compare_sources | less

   This shows you the changes that would be done in the OCaml pure
   sources of the directory ocaml_src.

   To make the new versions, do:

   ::

        make new_sources
        make promote_sources

   Notice that these pure OCaml sources are not supposed to be modified
   by hand, but only created by the above commands. Although their
   source is pretty printed they are usually not easy to read,
   particularly for expanded grammars (of the statement 'EXTEND').

   If these sources do not compile, due to changes in the OCaml
   compiler, it is possible however to edit them. In this case, similar
   changes may need to be performed in the normal sources in revised
   syntax.

   After doing 'make new_sources' above, and before doing 'make
   promote_sources' below, it is possible to do 'make untouch_sources'
   which changes the dates of the newly created files with the dates of
   the old files if they are not modified. This way, the "svn commit"
   will not need to compare these files, which may be important if your
   network is not fast.

   The 'make new_sources' builds a directory named 'ocaml_src.new'. If
   this directory still exists, due to a previous 'make new_sources',
   the command fails. In this case, just delete it (rm -rf
   ocaml_src.new) without problem: this directory is not part of the
   distribution, it is just temporary.

   The 'make clean_sources' deletes old versions of ocaml_src, keeping
   only the last and the before last ones.

   The command:

   ::

        make bootstrap_sources

   is a shortcut for:

   ::

        make new_sources
        make untouch_sources
        make promote_sources
        make clean_sources

   If there are changes in the specific file 'lib/versdep.ml', do also:

   ::

        make compare_all_versdep

   and possibly:

   ::

        make bootstrap_all_versdep

   because this file, in 'ocaml_src/lib/versdep' directory has different
   versions according to the OCaml version.

   After having rebuilt the pure OCaml sources, check that they work by
   rebuilding everything from scratch, starting with "configure".

   .. rubric:: If you change the main parser
      :name: if-you-change-the-main-parser

   If you change the main parser 'meta/pa_r.ml', you should check that
   the quotations expanders of syntax tree 'meta/q_MLast.ml' match the
   new version. For that, do:

   ::

        cd meta
        make compare_q_MLast

   If no differences are displayed, it means that 'q_MLast.ml' is ok,
   relatively to 'pa_r.ml'.

   Otherwise, if the displayed differences seem reasonable, update the
   version by typing:

   ::

        make bootstrap_q_MLast

   Then returning to the top directory, do 'make core compare' and
   possibly 'make coreboot' (one of several times) to check the
   correctness of the file.

   And don't forget, if you want to commit, to re-create the pure OCaml
   sources like indicated above.

   .. rubric:: Adding new nodes to the syntax tree
      :name: adding-new-nodes-to-the-syntax-tree

   If new nodes are necessary in the syntax tree, for example because
   the OCaml language added itself new nodes, the steps are the
   following (with the example of adding the "lazy" pattern node).

   -  Add the node in the file 'main/mLast.mli'. Please respect the
      design of the nodes by looking at the other nodes. Example:

      ::

               PaLaz of loc and patt


   -  Try to compile (do 'make' in the main directory). You are going to
      have some errors in files telling you that nodes are missing in
      some pattern matchings. Add them, according to the new nodes of
      OCaml or looking at other nodes.
   -  Once the compilation is done, try a 'make bootstrap' to be sure
      everything is OK.
   -  When it is, add the possible concrete syntax in the revised
      syntax, i.e. in 'meta/pa_r.ml'. Since the quotation is not yet
      implemented, put it in syntax without quotation. Example:

      ::

           "lazy"; p = SELF -> MLast.PaLaz loc p

   -  Do 'make bootstrap' again.
   -  Go to the directory 'meta' and type:

      ::

           make compare_q_MLast

      This command try to compare what should be the AST quotation if it
      perfectly matched the syntax. If this comparison seems reasonable,
      change the file 'q_MLast.ml' by typing:

      ::

           make bootstrap_q_MLast

   -  Do a 'make bootstrap' again to check everything is OK. If it is
      change the line of 'meta/pa_r.ml'. In the example, from:

      ::

           "lazy"; p = SELF -> MLast.PaLaz loc p

      to:

      ::

           "lazy"; p = SELF -> <:patt< lazy $p$ >>

   -  The new syntax should work now in revised syntax. You can complete
      the compilation, do a 'make install' and check with the toplevel
      that it works. Complete with the rest like said above.
   -  You can then complete the other syntaxes (the 'normal' syntax, for
      example in 'etc/pa_o.ml') and the pretty printers.

   .. rubric:: Switching between transitional and strict mode
      :name: switching-between-transitional-and-strict-mode

   If Camlp5 is compiled in some mode, it is possible to change its mode
   in two boostrapping steps. Type:

   ::

        make MODE=T coreboot

   to switch to transitional mode, or:

   ::

        make MODE=S coreboot

   to switch to strict mode.

   After two (necessary) bootstraps, the kernel is compiled in the new
   mode. Complete the compilation by:

   ::

        make MODE=T all opt opt.opt

   or:

   ::

        make MODE=S all opt opt.opt

   according to the new mode you want to use.

   Another solution is, of course, recompile everything from scratch:

   ::

        make clean
        ./configure -transitional
        make world.opt

   or:

   ::

        make clean
        ./configure -strict
        make world.opt

   .. rubric:: Bootstrapping
      :name: bootstrapping

   Camlp5 is bootstrapped in numerous ways.

   .. rubric:: Camlp5 executable bootstrapping
      :name: camlp5-executable-bootstrapping

   The file 'main/camlp5r' is rebuilt each time a bootstrapping command
   is used (like 'make coreboot' or 'make bootstrap'). This
   bootstrapping command starts with copying it in the directory 'boot'.
   The file 'boot/camlp5r' is used to recompile the sources, creating
   another file 'main/camlp5r'. When both files are the same (byte by
   byte), the Camlp5 executable is bootstrapped.

   Sometimes, in particular when changes are done in the library
   (directory 'lib'), it is necessary to bootstrap twice before having
   the message 'Fixpoint reached, bootstrap succeeded'.

   The command 'make compare' tells you whether the Camlp5 executable is
   currently bootstrapped or not.

   .. rubric:: Source bootstrapping
      :name: source-bootstrapping

   The compilation of Camlp5 starts with the compilation of files of the
   directory ocaml_src written in pure OCaml. This creates the files
   'camlp5' and 'camlp5r' in the directory boot. This is called the
   'cold start'.

   Once done, the sources of Camlp5 can be compiled using revised syntax
   and several syntax extensions, like the statement 'EXTEND', for
   example, and the quotations of syntax trees.

   The core files of Camlp5 are in the directories lib, main, meta,
   odyl. There are the same directories in the directory ocaml_src where
   all files are equivalent.

   When changes are done in the core files, and when the printer kit in
   normal syntax 'etc/pr_o.cmo' has been created, the files of the
   directory ocaml_src can be rebuilt using the command 'make
   bootstrap_sources'. This updates the files in ocaml_src to exactly
   reflect the ones in the core, but in pure OCaml syntax.

   Bootstrap: the1 files in ocaml_src creates the first Camlp5
   executable. The Camlp5 executable can rebuild the files in ocaml_src.

   .. rubric:: Source file q_MLast.ml bootstrapping
      :name: source-file-q_mlast.ml-bootstrapping

   The source file meta/q_MLast.ml (quotation of syntax trees) can be
   recreated using the file meta/pa_r.ml (revised syntax). When changes
   are done in the file meta/pa_r.ml, a good usage is to go to the
   directory 'meta' and type:

   ::

          make compare_q_MLast

   This shows the possible changes that will be applied to
   meta/q_MLast.ml. If they seem to be reasonable, do:

   ::

          make bootstrap_q_MLast

   This changes the source file meta/q_MLast.ml. After this command, a
   new 'make compare_q_MLast' indicates no differences.

   After that, a new 'make bootstrap' in the top directory ensures that
   everythings works.

   Bootstrap: the file meta/pa_r.ml uses the quotation expander
   meta/q_MLast.cmo. The source file meta/q_MLast.ml is recreated by
   meta/pa_r.ml.

   .. rubric:: Source file q_ast.ml bootstrapping
      :name: source-file-q_ast.ml-bootstrapping

   The source file meta/q_ast.ml contains another version of the
   quotation expander of syntax trees which follows the current syntax
   used (in normal syntax if the current syntax is used). This works
   only in strict mode.

   This file depends on the definition of the syntax tree
   main/mLast.mli. When changes are done in this file, it is possible to
   see what changes are impacted in meta/q_ast.ml. For this, go to the
   directory 'meta' and type:

   ::

          make compare_q_ast

   This shows the possible changes that will be applied to
   meta/q_ast.ml. If they seem to be reasonable, do:

   ::

          make bootstrap_q_ast

   This changes the source file meta/q_ast.ml. After this command, a new
   'make compare_q_ast' indicates no differences.

   After that, a new 'make bootstrap' in the top directory ensures that
   everythings works.

   .. rubric:: Lisp and Scheme syntax bootstrapping
      :name: lisp-and-scheme-syntax-bootstrapping

   The Lisp syntax is written in Lisp syntax in the directory etc. It is
   the file 'etc/pa_lisp.ml'. To compile this file, there is another
   file, named 'etc/pa_lispr.ml' written in revised syntax.

   When changes are done in etc/pa_lisp.ml, the file etc/pa_lispr.ml
   must be rebuilt. First, go to the directory 'etc' and type:

   ::

          make compare_lisp

   If changes seem to be reasonable, do:

   ::

          make boostrap_lisp

   This rebuilds 'etc/pa_lispr.ml'. A new 'make' in the directory 'etc'
   will recompile it and recompile the Lisp version 'etc/pa_lisp.ml'.

   Bootstrap: etc/pa_lispr.ml allows to compile etc/pa_lisp.ml, and
   changes is etc/pa_lisp.ml are reported in the source file
   etc/pa_lispr.ml through 'make bootstrap_lisp'.

   Same for the Scheme syntax: the files are etc/pa_scheme.ml and
   'etc/pa_scheme.ml'.

   .. rubric:: EXTEND statement bootstrapping
      :name: extend-statement-bootstrapping

   The EXTEND statement of Camlp5 is a syntax extension. The file
   'meta/pa_extend.ml' contains the statement for the adding of this
   syntax extension, therefore something like:

   ::

          EXTEND
            expr:
              [ [ "EXTEND" .....

   To be compiled, the file 'meta/pa_extend.ml' needs 'pa_extend.cmo'.
   This is actually its previous version in the directory 'boot'. When
   checking for a correct bootstrapping of Camlp5 (with the command
   'make compare', for example), a test is done to verify that the
   binary files 'meta/pa_extend.cmo' and 'boot/pa_extend.cmo' are the
   same.

   Notice that there is also a file 'ocaml_src/meta/pa_extend.ml' in
   pure OCaml syntax, but, although this file is pretty printed, is is
   hardly editable, because the expansion of the 'EXTEND' statement is a
   very long expression rather difficult to understand. But this file
   need not to be changes, since the command 'make bootstrap_sources'
   (see above) rebuilts it.

   .. container:: trailer
