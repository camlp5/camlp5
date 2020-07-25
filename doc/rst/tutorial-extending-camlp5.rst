.. _tutorial_extending_ocaml:

==========================================
 Tutorial: Extending OCaml with New Syntax
==========================================

In this tutorial we'll explain how to extend Camlp5's with new syntax
and logic to convert that syntax into standard Ocaml AST.  Since most
users will prefer to use PPX rewriters, I'll just note that you can
find PPX rewriters based on Camlp5 in the `pa_ppx <https://github.com/chetmurthy/pa_ppx>`_
project.

The code for this tutorial can be found in the directory
``tutorials``, and in each case, you'll find a buildable tree (with
Makefile), and (sometimes) simple tests.

.. contents::
  :local:


A simple example: ``sum 1 ; 2 end``
===================================

The code for this example is in ``tutorials/sum``.  In this example,
we'll add new syntax of the form

::

   sum 1 ; 2 ; 3 end

to the Ocaml syntax.  Since ";" is an infix expression operator in the
original syntax, this necessarily means that the grammar will be
different for revised syntax, than it is for original syntax.  We'll
describe both.

The new syntactic form
----------------------

We're going to extend Ocaml's syntax to accept

::

   sum end --> 0
   sum 5 end --> 5
   sum 4 ; 6 end --> 10
   let x = 2 in sum x ; x end --> 4
   ... etc ...

Code for original syntax
------------------------

Here's the code to extend the original syntax with this new syntactic
form.  (For grins) It's written in original syntax, but could have
been written in revised syntax: the syntax of the extension's source
code has nothing to do with it's usage.

::

   open Pcaml
   EXTEND
     expr: BEFORE "expr1"
     [ [ "sum";
         e =
         FOLD0 (fun e1 e2 -> <:expr< $e2$ + $e1$ >>) <:expr< 0 >>
           expr LEVEL "expr1" SEP ";";
         "end" -> e ] ] ;
   END

To build:

::

   ocamlfind ocamlc -package fmt,camlp5.extend,camlp5.extfold,camlp5.quotations \
       -syntax camlp5o -c sum_original.ml

To use it in a toplevel:

::

   #use "topfind.camlp5";;
   #camlp5o ;;
   #load "sum_original.cmo";;
   let x = 1 in sum x ; x ; 2 end ;;

with the obvious output

::

   - : int = 4

Instead of loading the object, we could load the source (but this
requires loading parsing kits):

::

   #use "topfind.camlp5";;
   #camlp5o ;;
   #require "camlp5.extend,camlp5.extfold,camlp5.quotations";;
   #use "sum_original.ml";;
   let x = 1 in sum x ; x ; 2 end ;;

Code for revised syntax
-----------------------

Here's the code to extend the revised syntax with this new syntactic
form.  It's written in revised syntax, but could have been written in
original syntax: the syntax of the extension's source code has nothing
to do with it's usage.

::

   open Pcaml ;
   EXTEND
     expr:
     [ [ "sum";
         e =
         FOLD0 (fun e1 e2 -> <:expr< $e2$ + $e1$ >>) <:expr< 0 >>
           expr SEP ";";
         "end" -> e ] ] ;
   END;

To build:

::

   ocamlfind ocamlc -package fmt,camlp5.extend,camlp5.extfold,camlp5.quotations \
       -syntax camlp5r -c sum_revised.ml

To use it in a toplevel:

::

   #use "topfind.camlp5";;
   #camlp54 ;;
   #load "sum_revised.cmo";;
   let x = 1 in sum x ; x ; 2 end ;;

with the obvious output

::

   - : int = 4

Instead of loading the object, we could load the source (but this
requires loading parsing kits):

::

   #use "topfind.camlp5";;
   #camlp5r ;;
   #require "camlp5.extend,camlp5.extfold,camlp5.quotations";;
   #use "sum_revised.ml";;
   let x = 1 in sum x ; x ; 2 end ;;

Discussion
----------

The differences between the two versions are only in that, since
original syntax already has the ";" operator as an infix operator on
expressions, adding this new operator at the precedence level of
expressions would not change that "1;2" is already an expression:
hence, ``sum 1 ; 2 end`` would be parsed as ``sum (1 ; 2) end``.  By
inserting this new syntax at level ``"expr"`` (which binds more
tightly than ";") we get the desired parsing behaviour.

Since in the revised syntax ";" is not an infix operator between
expressions (it is only operational in "do" blocks) there's no problem
there.

There are three parsing kits used here.  Briefly,

* ``camlp5.extend``: grammar extension syntax support
* ``camlp5.extfold``: support for ``FOLD`` operators in grammars
* ``camlp5.quotations``: support for quotations (e.g. ``<<:expr< 0 >>``)

Using camlp5 from the commandline and toplevel is discussed in
:ref:`introduction_quickstart` and :ref:`introduction_toplevel` .

.. container:: trailer
