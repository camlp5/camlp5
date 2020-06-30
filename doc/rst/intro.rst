============
Introduction
============



Camlp5 is a preprocessor and pretty-printer for OCaml programs. It
also provides parsing and printing tools.

As a preprocessor, it allows to:

-  extend the syntax of OCaml,
-  redefine the whole syntax of the language.

As a pretty printer, it allows to:

-  display OCaml programs in an elegant way,
-  convert from one syntax to another,
-  check the results of syntax extensions.

Camlp5 also provides some parsing and pretty printing tools:

-  extensible grammars
-  extensible printers
-  stream parsers and lexers
-  pretty print module

It works as a shell command and can also be used in the OCaml
toplevel.


.. contents::
  :local:

Quickstart with `ocamlfind`
===========================

The easiest (and the one I use) way to use camlp5 is with ``ocamlfind``.
Once Camlp5 is installed, ``ocamlfind list | grep camlp5`` produces a
long list of packages: each of these corresponds to a feature of
camlp5, and this documentation will explain how to use them.  Camlp5
can be used in the ocaml toplevel, and the tutorials in this
documentation will use this capability also.

But overall, the general idea is that we compile ocaml files,
specifying their syntax (typically ``camlp5o``, but perhaps ``camlp5r``),
and requiring the ``camlp5`` package and maybe other packages.  So for
instance, to compile an original-syntax ocaml file::

  ocamlfind ocamlc -package camlp5,fmt -syntax camlp5o -linkall -linkpkg streams.ml -o streams

Let's unpack that:

1. use ``ocamlfind ocamlc``

2. specify packages ``camlp5`` and ``fmt`` (for some pretty-printing in the program)

3. specify original syntax: ``-syntax camlp5o``

4. various link-flags: ``-linkall -linkpkg``

If the file were in revised syntax, we would compile it thus::

  ocamlfind ocamlc -package camlp5,fmt -syntax camlp5r -linkall -linkpkg streams.ml -o streams

And if it contained code that worked with extensible grammars, we'd use::

  ocamlfind ocamlc -package camlp5,fmt,camlp5.extend -syntax camlp5r -linkall -linkpkg streams.ml -o streams

Note the package ``camlp5.extend`` (that provides extensible grammar syntax support).

For users of camlp5 who do not wish to write new syntax-manipulating
code, but only use existing packages, this is typically enough: there
are packages like `pa_ppx <https://github.com/chetmurthy/pa_ppx>`_
that use camlp5, and those packages also provide their functionality
as a collection of ocamlfind packages, which are used in exactly the
same manner as above.

Camlp5 Package Naming and Overview
==================================

Briefly, there is a ``camlp5`` package, and a number of sub-packages.
Below is a list, and basically *everything* in Camlp5 is exposed as an
ocamlfind package.  Here, categorized (a bit) are the available
packages:

1. the main package

 - ``camlp5``: the main camlp5 package

2. grammar support: this is packages that setup the grammar for parsing ML files

 - ``camlp5.pa_o``: grammar for original syntax
 - ``camlp5.pa_op``: *stream* parser grammar support for original syntax
 - ``camlp5.pa_r``: grammar for revised syntax
 - ``camlp5.pa_scheme``: grammar for scheme syntax (written in scheme syntax)
 - ``camlp5.pa_schemer``: grammar support for scheme syntax (written in revised syntax)

3. printer support: this is packages that setup the printer used to print out ML ASTs

 - ``camlp5.pr_depend``: printing support for depend generation (deprecated)
 - ``camlp5.pr_dump``: printer that dumps out official Ocaml AST (the default way camlp5 outputs its result AST)
 - ``camlp5.pr_o``: ML AST printer to original syntax (implemented using Camlp5's printer machinery, hence extensible)
 - ``camlp5.pr_official``: ML AST printer using Ocaml's official compiler-libs printer machinery
 - ``camlp5.pr_r``: ML AST printer to revised syntax (again, implemented using Camlp5's printery machinery)
 - ``camlp5.pr_scheme``: ML AST printer to Scheme syntax

4. Syntax extensions for writing AST-manipulating code: these are
   packages that aid the programmer in writing new AST-manipulating
   code (like the code in the above packages):

 - ``camlp5.extend``: extensible grammars
 - ``camlp5.extfun``: extensible functions
 - ``camlp5.extprint``: extensible printers
 - ``camlp5.fstream``: functional streams
 - ``camlp5.gramlib``: the grammar-interpreter machinery, as a separate package
 - ``camlp5.pa_lexer``: syntax extension for writing lexers
 - ``camlp5.macro``: IFDEF-like syntax extension
 - ``camlp5.phony_quotations``: grammar support for phony quotations (only for developers)
 - ``camlp5.pprintf``: syntax extensions for Camlp5's ``pprintf'' pretty-printer
 - ``camlp5.pragma``: experimental pragma support (don't use this)
 - ``camlp5.quotations``: support for quotations and anti-quotations in ML code

There are three ways that a piece of Ocaml code can be used, and this
applies equally to Camlp5 packages.  So, for a camlp5
package ``X`` above, we can done one of:

1. load into the preprocessor::

     ocamlfind ocamlc -package X ....
     ocamlfind ocamlopt -package X ....

2. load into the toplevel (and used to preprocess there, but also linked-in)::

     #require "X" ;;

3. link with the program (e.g. with a final link-command using ``ocamlc``)::

     ocamlfind ocamlc -package X.link ....
     ocamlfind ocamlopt -package X.link ....

Notice that for use #3, we supply the name ``X.link`` instead of
``X``.  For example, to link revised-syntax grammar support into a
program, we'd use package ``camlp5.pa_r.link``.

The Ocaml Toplevel
==================

A warning for users who use some frontend to interact with the Ocaml
toplevel: many frontends have a baked-in understanding of Ocaml's
syntax, and specifically that toplevel phrases always end with ``;;``
(e.g. ``tuareg-mode`` in Emacs).  If you load the revised syntax into
an Ocaml toplevel accessed via one of these front-ends, you will find
that it doesn't work: you may various find that you get no response
back to input, or that the front-end inserts extra semicolons, or
other weirdness.  When I use Emacs with revised syntax Ocaml, I
typically do so in a ``M-x shell RET`` window.

To use camlp5 from the toplevel, first decide which syntax you wish to use. Then

1. Start the ocaml toplevel.
2. "use" the findlib/camlp5 include file.
3. then select your syntax.
4. Proceed to use the toplevel.

For original syntax:

::

           OCaml version 4.10.0

   # #use "topfind.camlp5";;
   - : unit = ()
   Findlib has been successfully loaded. Additional directives:
     #require "package";;      to load a package
     #list;;                   to list the available packages
     #camlp4o;;                to load camlp4 (standard syntax)
     #camlp4r;;                to load camlp4 (revised syntax)
     #predicates "p,q,...";;   to set these predicates
     Topfind.reset();;         to force that packages will be reloaded
     #thread;;                 to enable threads

   - : unit = ()
   Additional Camlp5 directives:
     #camlp5o;;                to load camlp5 (standard syntax)
     #camlp5r;;                to load camlp5 (revised syntax)

   - : unit = ()
   # #camlp5o ;;
   /home/chetsky/Hack/Ocaml/GENERIC/4.10.0/lib/camlp5: added to search path
   /home/chetsky/Hack/Ocaml/GENERIC/4.10.0/lib/camlp5/camlp5o.cma: loaded
   	Camlp5 parsing version 8.00-alpha01

   # 

Again, just the commands:

::

   #use "topfind.camlp5";;
   #camlp5o ;;

For the revised syntax, just replace the last line with ``#camlp5r
;;`` The tutorial has examples of loading packages and code into a
toplevel using camlp5. [Again, I reiterate that revised syntax and
(e.g.) the ``tuareg-mode`` front-end will *not* interact well.]

Low-level Shell usage
=====================

The main shell commands are:

-  ``camlp5o`` : to treat files written in normal OCaml syntax,
-  ``camlp5r`` : to treat files written in a new syntax named :ref:`revised_syntax` .

These commands can be given as parameters of the option ``-pp`` of
the OCaml compiler. Examples:

::

    ocamlc -pp camlp5o foo.ml
    ocamlc -pp camlp5r bar.ml

This way, the parsing is done by Camlp5. In case of syntax errors,
the parsing fails with an error message and the compilation is
aborted. Otherwise, the OCaml compiler continues with the syntax tree
provided by Camlp5.

In the toplevel, it is possible to preprocess the input phrases by
loading one of the files "``camlp5o.cma``" or "``camlp5r.cma``". The
common usage is:

::

    ocaml -I +camlp5 camlp5o.cma
    ocaml -I +camlp5 camlp5r.cma

It is possible that, in your installation, the Camlp5 library is not
in the OCaml directory. In this case, the commands must be:

::

    ocaml -I `camlp5 -where` camlp5o.cma
    ocaml -I `camlp5 -where` camlp5r.cma

In general, in this documentation, when a command requires:

::

    -I +camlp5

it can be replaced by:

::

    -I `camlp5 -where`

or, by:

::

    -I <directory>

where "directory" is the directory path where the Camlp5 library
files are installed.

Parsing and Printing kits
=========================

Parsing and printing extensions are OCaml object files, i.e. files
with the extension "``.cmo``" or "``.cma``". They are the result of
the compilation of OCaml source files containing what is necessary to
do the parsing or printing. These object files are named parsing and
printing *kits*.

These files cannot be linked to produce executables because they
generally call functions and use variables defined only in Camlp5
core, typically belonging to the module "``Pcaml``". The kits are
designed to be loaded by the Camlp5 commands, either through their
command arguments or through directives in the source files.

It is therefore important to compile the *kits* with the option
"``-c``" of the OCaml compiler (i.e. just compilation, not producing
an executable) and with the option "``-I   +camlp5``" (or
":literal:`-I `camlp5 -where\``") to inform the compiler to find
module interfaces in installed Camlp5 library.

In the OCaml toplevel, it is possible to use a kit by simply loading
it with the directive "``#load``".

Extending syntax
================

A syntax extension is a Camlp5 parsing kit. There are two ways to use
a syntax extension:

-  Either by giving this object file as parameter to the Camlp5
  command. For example:

  ::

        ocamlc -pp "camlp5o ./myext.cmo" foo.ml

-  Or by adding the directive "``#load``" in the source file:

  ::

        #load "./myext.cmo";;

  and then compile it simply like this:

  ::

        ocamlc -pp camlp5o foo.ml

Several syntax extensions can be used for a single file. The way to
create one's own syntax extensions is explained in this document.

Pretty printing
===============

As for syntax extensions, the pretty printing is defined or extended
through Camlp5 printing kits. Some pretty printing kits are provided
by Camlp5, the main ones being:

-  ``pr_o.cmo``: to pretty print in normal syntax,
-  ``pr_r.cmo``: to pretty print in revised syntax.

Examples: if we have a file, ``foo.ml``, written in normal syntax and
and another one, ``bar.ml``, written in revised syntax, here are the
commands to pretty print them in their own syntax:

::

    camlp5o pr_o.cmo foo.ml
    camlp5r pr_r.cmo bar.ml

And how to convert them into the other syntax:

::

    camlp5o pr_r.cmo foo.ml
    camlp5r pr_o.cmo foo.ml

The way to create one's own pretty printing extensions is explained
in this document.

Note: the revised syntax
========================

The *revised syntax* is a specific syntax whose aim is to resolve
some problems and inconsistencies of the normal OCaml syntax. A
chapter will explain the differences between the normal and the
revised syntax.

All examples of this documentation are written in that revised
syntax. Even if you don't know it, it is not difficult to understand.
The same examples can be written in normal syntax. In case of
problems, refer to the chapter describing it.

.. container:: trailer
