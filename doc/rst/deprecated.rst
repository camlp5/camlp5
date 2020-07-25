======================
Deprecated Information
======================

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
