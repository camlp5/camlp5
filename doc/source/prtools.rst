##############
Printing tools
##############

.. _extensible-printers:

*******************
Extensible printers
*******************

This chapter describes the syntax and semantics of the extensible
printers of Camlp5.

Similar to the :ref:'grammars', the extensible printers allow to
define and extend printers of data or programs. A specific statement
``EXTEND_PRINTER`` allow to define these extensions.

Getting started
===============

A printer is a value of type ``Eprinter.t a`` where ``a`` is the type
of the item to be printed. When applied, a printer returns a string,
representing the printed item.

To create a printer, one must use the function ``Eprinter.make`` with,
as parameter, the name of the printer, (used in error messages). A
printer is created empty, i.e. it fails if it is applied.

As with grammar entries, printers may have several levels. When the
function ``Eprinter.apply`` is applied to a printer, the first level
is called.  The function ``Eprinter.apply_level`` allows to call a
printer at some specific level possibly different from the first
one. When a level does not match any value of the printed item, the
next level is tested. If there is no more levels, the printer
fails.

In semantic actions of printers, functions are provided to recursively
call the current level and the next level. Moreover, a *printing
context* variable is also given, giving the current indentation, what
should be printed before in the same line and what should be printed
after in the same line (it is not mandatory to use them).

The extension of printers can be done with the ``EXTEND_PRINTER``
statement added by the *parsing kit* ``pa_extprint.cmo``.

Syntax of the EXTEND_PRINTER statement
======================================

::

        expression ::= extend-statement
  extend-statement ::= "EXTEND_PRINTER" extend-body "END"
       extend-body ::= extend-printers
   extend-printers ::= extend-printer extend-printers
                     | <nothing>
    extend-printer ::= printer-name ":" position-opt "[" levels "]"
      position-opt ::= "FIRST"
                     | "LAST"
                     | "BEFORE" label
                     | "AFTER" label
                     | "LEVEL" label
                     | <nothing>
            levels ::= level "|" levels
                     | level
             level ::= label-opt "[" rules "]"
         label-opt ::= label
                     | <nothing>
             rules ::= rule "|" rules
                     | rule
              rule ::= pattern "->" expression
                     | pattern "when" expression "->" expression
      printer-name ::= qualid
            qualid ::= qualid "." qualid
                     | uident
                     | lident
            uident ::= 'A'-'Z' ident
            lident ::= ('a'-'z' | '_' | misc-byte) ident
             ident ::= ident-char*
        ident-char ::= ('a'-'a' | 'A'-'Z' | '0'-'9' | '_' | ''' | misc-byte)
         misc-byte ::= '\128'-'\255'


Semantics of EXTEND_PRINTER
===========================

Printers definition list
------------------------

All printers are extended according to their corresponding definitions
which start with an optional "position" and follow with the "levels"
definition.

Optional position
^^^^^^^^^^^^^^^^^

After the colon, it is possible to specify where to insert the defined
levels:

- The identifier ``FIRST`` (resp. ``LAST``) indicates that the level
  must be inserted before (resp. after) all possibly existing levels
  of the entry. They become their first (resp. last) levels.
- The identifier ``BEFORE`` (resp. ``AFTER``) followed by a level
  label (a string) indicates that the levels must be inserted before
  (resp. after) that level, if it exists. If it does not exist, the
  extend statement fails at run time.
- The identifier ``LEVEL`` followed by a label indicates that the
  first level defined in the extend statement must be inserted at the
  given level, extending and modifying it. The other levels defined in
  the statement are inserted after this level, and before the possible
  levels following this level. If there is no level with this label,
  the extend statement fails at run time.
- By default, if the entry has no level, the levels defined in the
  statement are inserted in the entry. Otherwise the first defined
  level is inserted at the first level of the entry, extending or
  modifying it. The other levels are inserted afterwards (before the
  possible second level which may previously exist in the entry).


Levels
^^^^^^

After the optional "position", the *level* list follow. The levels are
separated by vertical bars, the whole list being between brackets.

A level starts with an optional label, which corresponds to its
name. This label is useful to specify this level in case of future
extensions, using the *position* (see previous section) or for
possible direct calls to this specific level.

Rules
^^^^^

A level is a list of *rules* separated by vertical bars, the
whole list being between brackets.

A rule is an usual pattern association (in a function or in the
"match" statement), i.e. a pattern, an arrow and an expression. The
expression is the semantic action which must be of type ``string``.

Rules insertion
---------------

The rules are sorted by their patterns, according to the rules of
:ref:`extensible-functions`.

Semantic action
---------------

The semantic action, i.e. the expression following the right arrow in
rules, contains in its environment the variables bound by the pattern
and three more variables:

- The variable ``curr`` which is a function which can be called to
  recursively invoke the printer at the current level,
- The variable ``next`` which is a function which can be called to
  invoke the printer at the next level,
- The variable ``pc`` which contains the printing context of type
  ``Pprintf.pr_context`` (see :ref:`pprintf`).

The variables ``curr`` and ``next`` are of type:

::

  pr_context -> t -> string

where ``t`` is the type of the printer (i.e. the type of its
patterns).

The variable ``curr``, ``next`` and ``pc`` have predefined names and
can hide the possible identifiers having the same names in the pattern
or in the environment of the ``EXTEND_PRINTER`` statement.

The Eprinter module
===================

See :ref:`library_eprinter_module`.

Examples
========

Parser and Printer of expressions
---------------------------------

This example illustrates the symmetry between parsers and printers. A
simple type of expressions is defined. A parser converts a string to a
value of this type, and a printer converts a value of this type to a
string.

In the printer, there is no use of the ``pc`` parameter and no use of
the ``Pretty`` module. The strings are printed on a single line.

Here is the source (file ``foo.ml``):

::

  #load "pa_extend.cmo";
  #load "pa_extprint.cmo";

  open Printf;

  type expr =
    [ Op of string and expr and expr
    | Int of int
    | Var of string ]
  ;

  value g = Grammar.gcreate (Plexer.gmake ());
  value pa_e = Grammar.Entry.create g "expr";
  value pr_e = Eprinter.make "expr";

  EXTEND
    pa_e:
      [ [ x = SELF; "+"; y = SELF -> Op "+" x y
        | x = SELF; "-"; y = SELF -> Op "-" x y ]
      | [ x = SELF; "*"; y = SELF -> Op "*" x y
        | x = SELF; "/"; y = SELF -> Op "/" x y ]
      | [ x = INT -> Int (int_of_string x)
        | x = LIDENT -> Var x
        | "("; x = SELF; ")" -> x ] ]
    ;
  END;

  EXTEND_PRINTER
    pr_e:
      [ [ Op "+" x y -> sprintf "%s + %s" (curr pc x) (next pc y)
        | Op "-" x y -> sprintf "%s - %s" (curr pc x) (next pc y) ]
      | [ Op "*" x y -> sprintf "%s * %s" (curr pc x) (next pc y)
        | Op "/" x y -> sprintf "%s / %s" (curr pc x) (next pc y) ]
      | [ Int x -> string_of_int x
        | Var x -> x
        | x -> sprintf "(%s)" (Eprinter.apply pr_e pc x) ] ]
    ;
  END;

  value parse s = Grammar.Entry.parse pa_e (Stream.of_string s);
  value print e = Eprinter.apply pr_e Pprintf.empty_pc e;

  if Sys.interactive.val then ()
  else print_endline (print (parse Sys.argv.(1)));

Remark on the use of ``curr`` and ``next`` while printing operators:
due to left associativity, the first operand uses ``curr`` and the
second operand uses ``next``. For right associativity operators, they
should be inverted. For no associativity, both should use ``next``.

The last line of the file allows use in either the OCaml toplevel or
as standalone program, taking the string to be printed as
parameter. It can be compiled this way:

::

  ocamlc -pp camlp5r -I +camlp5 gramlib.cma foo.ml


Examples of use (notice the redundant parentheses automatically
removed by the printing algorithm):

::

  $ ./a.out "(3 * x) + (2 / y)"
  3 * x + 2 / y
  $ ./a.out "(x+y)*(x-y)"
  (x + y) * (x - y)
  $ ./a.out "x + y - z"
  x + y - z
  $ ./a.out "(x + y) - z"
  x + y - z
  $ ./a.out "x + (y - z)"
  x + (y - z)

Printing OCaml programs
-----------------------

Complete examples of usage of extensible printers are the printers in
syntaxes and extended syntaxes provided by Camlp5 in the pretty
printing *kits*:

- ``pr_r.cmo``: pretty print in revised syntax
- ``pr_o.cmo``: pretty print in normal syntax
- ``pr_rp.cmo``: also pretty print the parsers in revised syntax
- ``pr_op.cmo``: also pretty print the parsers in normal syntax

See the chapter entitled :ref:`extensions-of-printing`.

.. _pprintf:

*******
Pprintf
*******

This chapter describes ``pprintf``, a statement to pretty print data.
It looks like the ``sprintf`` function of the OCaml library, and borrows
some ideas of the Format OCaml library. Another statement, ``lprintf``,
is a slightly different version of ``pprintf`` handling with locations.


Syntax of the pprintf statement
===============================

The "pprintf" statement is added by the *parsing kit*
``pa_pprintf.cmo``.

Notice that, in opposition to ``printf``, ``fprintf``, ``sprintf``, and all
its variants, which are functions, this ``pprintf`` is a
*statement*, not a function: ``pprintf`` is a keyword and the
expander analyzes its string format parameter to generate specific
statements. In particular, it cannot be used alone and has no type by
itself.

::

        expression ::= pprintf-statement
 pprintf-statement ::= "pprintf" qualid format expressions
            qualid ::= qualid "." qualid
                     | uident
                     | lident
            format ::= string
       expressions ::= expression expressions
                     | <nothing>


Semantics of pprintf
====================

The ``pprintf`` statement converts the format string into a string like
the ``sprintf`` of the OCaml library ``Printf`` does (see the OCaml manual
for details). The string format can accept new conversion
specifications, ``%p`` and ``%q``, and some pretty printing annotations,
starting with ``@`` like in the OCaml library ``Format``.

The ``pprintf`` statement takes as first parameter, a value of type
``pr_context`` defined below. Its second parameter is the extended
format string. It can take other parameters, depending on the format,
like ``sprintf``.

The result of ``pprintf`` is always a string. There is no versions
applying to files or buffers.

The strings built by ``pprintf`` are concatenated by the function
``Pretty.sprintf`` (see the chapter entitled :ref:`pretty-print`)
which controls the line length and prevents overflowing.

Printing context
----------------

The "pprintf" statement takes, as first parameter, a *printing
context*. It is a value of the following type:

::

  type pr_context =
    { ind : int;
      bef : string;
      aft : string;
      dang : string };


The fields are:

- ``ind`` : the current indendation
- ``bef`` : what should be printed before, in the same line
- ``aft`` : what should be printed after, in the same line
- ``dang`` : the dangling token to know whether parentheses are
  necessary

Basically, the ``pprintf`` statement concats the ``bef`` string, the
formatted string and the ``aft`` string. The example:

::

  pprintf pc "hello world"


is equivalent to (and indeed generates):

::

  Pretty.sprintf "%shello world%s" pc.bef pc.aft


But if the format string contains conversion specifications ``%p`` or
``%q``, the ``bef`` and ``aft`` strings are actually transmitted to the
corresponding functions:

::

  pprintf pc "hello %p world" f x


is equivalent to:

::

  f {(pc) with
     bef = Pretty.sprintf "%shello " pc.bef;
     aft = Pretty.sprintf " world%s" pc.aft}
    x


Thus, the decision of including the ``bef`` and the ``aft`` strings are
delayed to the called function, allowing this function to possibly
concatenate ``bef`` and ``aft`` to its own strings.

A typical case is, while printing programs, when an expression needs
to be printed between parentheses. The code which does that looks
like:

::

  pprintf pc "(%p)" expr e


The right parenthesis of this string format is included in the ``aft``
string transmitted to the function ``expr``. In a situation when several
right parentheses are concatened this way, the fact that all these
parentheses are grouped together allows the function which eventually
print them to decide to break the line or not, these parentheses being
taken into account in the line length.

For example, if the code contains a print of an program containing an
application whose source is:

::

  myfunction myarg


and if the ``aft`` contains ``))))))``, the decision of printing in one
line as:

::

  myfunction myarg))))))

or in two lines as:

::

  myfunction
    myarg))))))


is exact, the right parentheses being added to ``myarg`` to determine
whether the line overflows or not.

Extended format
---------------

The extended format used by ``pprintf`` may contain any strings and
conversion specifications allowed by the ``sprintf`` function (see
module ``Printf`` of the OCaml library), plus:

- the conversion specifications: ``%p`` and ``q``,
- the pretty printing annotations introduced by, ``@`` and followed
  by:

  - the character ``;`` (semicolon), optionally followed by ``<``, two numbers and ``>``,
  - the character `` `` (space),
  - the character ``[``, optionally followed by the character ``<`` and either:

    - the character ``a``
    - the character ``b``
    - a number

    and the character ``>``, then followed by format string, and ended
    with ``@]``

The format string is applied like in the ``sprintf`` function. Specific
actions are done for the extended features. The result is a string
like for the ``sprintf`` function. The "string before" and "string
after" defined by the fields ``bef`` and ``aft`` of the printing context
are taken into account and it is not necessary to add them in the
format.

Example:

::

  pprintf pc "hello, world"


generates:

::

  Pretty.sprintf "%shello, world%s" pc.bef pc.aft;


An empty format:

::

  pprintf pc "";

just prints the "before" and "after" strings:

::
  Pretty.sprintf "%s%s" pc.bef pc.aft;


Line length
-----------

The function ``pprintf`` uses the Camlp5 ``Pretty`` module. The line
length can be set by changing the value of the reference
``Pretty.line_length``.

The conversion specifications ``p`` and ``q``
---------------------------------------------

The ``%p`` conversion specification works like the ``%a`` of the printf
statement. It takes two arguments and applies the first one to the
printing context and to the second argument. The first argument must
therefore have type ``pr_context -> t -> unit`` (for some type ``t``)
and the second one ``t``.

Notice that this function can be called twice: one to test whether the
resulting string holds in the line, and another one to possibly recall
this function to print it in several lines. In the two cases, the
printing context given as parameter is different.

It uses the functions defined in the :ref:`pretty-print` module.

Example: the following statement:

::

  pprintf pc "hello, %p, world" f x


is equivalent to:

::

  f {(pc) with
     bef = Pretty.sprintf "%shello, " pc.bef;
     aft = Pretty.sprintf ", world%s" pc.aft}
    x


The ``%q`` conversion specification is like ``%p`` except that it
takes a third argument which is the value of the ``dang`` field,
useful when the syntax has "dangling" problems requiring
parentheses. See :ref:`extensions-of-printing` for more explanations
about dangling problems.

The same example with ``%q``:

::

  pprintf pc "hello, %q, world" f x "abc"


is equivalent to:

::

  f {(pc) with
     bef = Pretty.sprintf "%shello, " pc.bef;
     aft = Pretty.sprintf ", world%s" pc.aft;
     dang = "abc"}
    x


The pretty printing annotations
-------------------------------

Breaks
^^^^^^

The pretty printing annotations allow to indicate places where lines
can be broken. They all start with the "at" sign "@". The main ones
are called *breaks* and are:

- ``@;`` specifying: *write a space or 'a newline and an indentation
  incremented by 2 spaces'*
- ``@ `` specifying: *write a space or 'a newline and the
  indentation'*

Example - where ``pc`` is a variable of type ``pr_context`` (for  example ``Pprintf.empty_pc``):

::

  pprintf pc "hello,@;world"


builds the string, if it holds in the line:

::

  hello, world

and if it does not:

::

  hello,
    world


The second form:

::

  pprintf pc "hello,@ world"

is printed the same way, if it holds in the line, and if it does not,
as:

::

  hello,
  world

The general form is:

- ``@;<s o>``, which is a break with ``s`` spaces if the string
  holds in the line, or an indentation offset (incrementation of the
  indentation) of ``o`` spaces if the string does not hold in the
  line.

<p>The break ``@;`` is therefore equivalent to ``@;<1 2>`` and ``@ `` is equivalent to ``@;<1 0>``.

Parentheses
^^^^^^^^^^^

A second form of the pretty printing annotations is the
parenthesization of format strings possibly containing other pretty
printing annotations. They start with ``@[`` and end with ``@]``.

It allows to change the associativity of the breaks. For example:

::

  pprintf pc "@[the quick brown fox@;jumps@]@;over the lazy dog"


If the whole string holds on the line, it is printed:

::

  the quick brown fox jumps over the lazy dog


If the whole string does not fit on the line, but ``the quick brow fox
jumps`` does, it is printed:

::

  the quick brown fox jumps
    over the lazy dog


If the string ``the quick brown fox jumps`` does not fit on the line, the whole string is printed:

::

  the quick brown fox
    jumps
    over the lazy dog


Conversely, if the code is right associated:

::

  pprintf pc "the quick brown fox@;@[jumps@;over the lazy dog@]"


It can be printed:

::

  the quick brown fox jumps over the lazy dog


or:

::

  the quick brown fox
    jumps over the lazy dog


or:

::

  the quick brown fox
    jumps
      over the lazy dog


The default is left associativity: without parentheses, it is printed
like in the first example.

Incrementation of indentation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The open parenthesis of the parenthesized form, ``@[`` can be followed
by ``<n>`` where ``n`` is a number. It increments the current
indentation (for possible newlines in the parenthesized text) with
this number.

Example:

::

  pprintf pc "@[<4>Incrementation@;actually of six characters@]"


makes the string (if not holding in the line):

::

  Incrementation
        actually of six characters


Break all or nothing
^^^^^^^^^^^^^^^^^^^^

The open parenthesis of the parenthesized form, ``@[`` can be followed
by ``<a>``. It specifies that if the string does not hold in the
line, all breaks between the parentheses (at one only level) are
printed in two lines, even if sub-strings could hold on the line. For
example:

::

  pprintf pc "@[<a>the quick brown fox@;jumps@;over the lazy dog@]"


can be printed only as:

::

  the quick brown fox jumps over the lazy dog


or as:

::
  the quick brown fox
    jumps
    over the lazy dog


Break all
^^^^^^^^^

The open parenthesis of the parenthesized form, ``@[`` can be followed
by ``<b>``. It specifies that all breaks are always printed in two
lines. For example:

::

  pprintf pc "@[<b>the quick brown fox@;jumps@;over the lazy dog@]"


is printed in all circumstances:

::

  the quick brown fox
    jumps
    over the lazy dog


Break all if
^^^^^^^^^^^^

The open parenthesis of the parenthesized form, ``@[`` can be followed
by ``<i>``. Depending on the value of the boolean variable of the
argument list, the breaks are all printed in two lines like with the
"break all" option above, or not.  For example:

::

  pprintf pc "%s@;@[<i>%s,@;%s@]" "good" True "morning" "everybody";
  pprintf pc "%s@;@[<i>%s,@;%s@]" "good" False "morning" "everybody";


are printed:

::

  good
    morning,
      everybody
  good morning, everybody


Parentheses not neighbours of breaks
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In the examples above, we can remark that the left parentheses are
always the begin of the string or are preceeded by a break, and that
the right parentheses are always the end of the string or followed by
a break.

When the parentheses ``@[`` and ``@]`` are not preceeded or followed
by the string begin nor end, nor preceeded or followed by breaks, they
are considered as the "bef" or "aft" part of the neighbour string. For
example, the following forms:

::

  pprintf pc "the quick brown fox@[ jumps over@]"


and:

::

  pprintf pc "@[the quick brown fox @]jumps over"

are respectively equivalent to:

::

  let pc = {(pc) with aft = sprintf " jumps over%s" pc.aft} in
  Pretty.sprintf "%sthe quick brown fox%s" pc.bef pc.aft


and:

::

  let pc = {(pc) with bef = sprintf "%sthe quick brown fox" pc.bef} in
  Pretty.sprintf "%sjumps over%s" pc.bef pc.aft


In these examples, the results are identical, but it can be important
if the non-parenthesized part contain one or several ``%p``. In this
case, the corresponding function receives the ``bef`` or ``aft`` part
in its ``pr_context`` variable and can take it into account when
printing its data.

Lprintf
-------

``Lprintf`` is like ``pprintf`` with the same parameters. It is equivalent
to an call to the function ``expand_lprintf``:

::

   lprintf pc "..."


is equivalent to:

::
   expand_lprintf pc loc (fun pc -> pprintf pc "...")


The function ``expand_lprintf`` and the variable ``loc`` must be defined
by the user in the environment where ``lprintf`` is used.

``Lprintf`` is used in predefined printers ``pr_r.ml`` and ``pr_o.ml`` to
allow optional insertions of location comments in the output.

Comparison with the OCaml modules Printf and Format
===================================================

Pprintf and Printf
------------------

The statement ``pprintf`` acts like the function
``Printf.sprintf``. But since it requires this extra parameter of type
``pr_context`` and needs the ``%p`` and ``%q`` conversions
specifications (which do not exist in ``Printf``), it was not possible
to use the ``Printf`` machinery directly and a new statement had to be
added.

The principle of ``pprintf`` and ``sprintf`` are the same. However,
``pprintf`` is a syntax extension and has no type by itself. It cannot
be used alone or without all its required parameters.

Pprintf and Format
------------------

The pretty printing annotations look like the ones of the OCaml module
Format. Actually, they have different semantics. They do not use
<em>boxes</em> like ``Format`` does. In ``pprintf`` statement, the
machinery acts only on indentations.

Notice that, with ``pprintf``, it is always possible to know the current
indentation (it is the field ``ind`` of the ``pr_context`` variable) and
it is therefore possible to take decisions before printing.

For example, it is possible, in a printer of OCaml statements, to
decide to print all match cases symmetrically, i.e. all with one line
for each case or all with newlines after the patterns.

It is what is done in the option ``-flag E`` added by the pretty
printing kits ``pr_r.cmo`` (pretty print in revised syntax) and
``pr_o.cmo`` (pretty print in normal syntax). See chapter
:ref:`commands_and_files` or type ``camlp5 pr_r.cmo -help`` or
``camlp5 pr_o.cmo -help``.

Another difference is that the internal behaviour of this printing
system is accessible, and it is always possible to use the basic
functions of the ``Pretty`` module (``horiz_vertic`` and ``sprintf``) if the
behaviour of ``pprintf`` is not what is desired by the programmer.

Relation with the Camlp5 extensible printers
============================================

The extensible printers of Camlp5 (see :ref:`extensible-printers`) use
the type ``pr_context`` of ``pprintf``. It is therefore possible to
use ``pprintf`` in the semantic actions of the extensible printers.  But
it is not mandatory. An extensible printer can just use the ``Pretty``
module or even neither ``pprintf`` nor ``Pretty``.</p>

The printing kits ``pr_r.ml`` and ``pr_o.ml`` (respectively pretty
print in revised and in normal syntax) and some other related to them,
are examples of usage of the "pprintf" statement.

The Pprintf module
==================

See its :ref:`library_pprintf_module` in the chapter "Library".

.. _pretty-print:

************
Pretty print
************

A pretty print system is provided in the library module ``Pretty``. It
allows one to pretty print data or programs. The ``Pretty`` module
contains:

- The function ``horiz_vertic`` to specify how data must be printed.
- The function ``sprintf`` to format strings.
- The variable ``line_length`` which is a reference specifying the
  maximum lines lengths.

Module description
==================

horiz_vertic
------------

The function ``horiz_vertic`` takes two functions as parameters. When
invoked, it calls its first function. If that function fails with some
specific internal error (that the function ``sprintf``
below may raise), the second function is called.

The type of ``horiz_vertic`` is:

::

  (unit -> 'a) -> (unit -> 'a) -> 'a


the horizontal function
^^^^^^^^^^^^^^^^^^^^^^^

The first function is said to be the "horizontal" function. It tries
to pretty print the data on a single line. In the context of this
function, if the strings built by the function ``sprintf`` (see below)
contain newlines or have lengths greater than ``line_length``, the
function fails (with a internal exception local to the module).

the vertical function
^^^^^^^^^^^^^^^^^^^^^

In case of failure of the "horizontal function", the second function
of ``horiz_vertic``, the "vertical" function, is called. In the context
of that function, the ``sprintf`` function behaves like the normal
``sprintf`` function of the OCaml library module ``Printf``.

sprintf
-------

The function ``sprintf`` works like its equivalent in the module
``Printf`` of the OCaml library, and takes the same parameters. Its
difference is that if it is called in the context of the first
function (the "horizontal" function) of the function ``horiz_vertic``
(above), all strings built by ``sprintf`` are checked for newlines or
length greater than the maximum line length. If either occurs, the
``sprintf`` function fails and the horizontal function fails.

If ``sprintf`` is not in the context of the horizontal function, it
behaves like the usual ``sprintf`` function.

line_length
-----------

The variable ``line_length`` is a reference holding the maximum line
length of lines printed horizontally. Its default is 78. This can be
changed by the user before using ``horiz_vertic``.

horizontally
------------

The call ``horizontally ()`` returns a boolean telling whether the
context is horizontal.

Example
=======

Suppose you want to pretty print the XML code
``"<li>something</li>"``. If the "something" is short, you
want to see:

::

  <li>something</li>


If the "something" has several lines, you want to see that:

::

  <li>
    something
  </li>


A possible implementation is:

::

  open Pretty;
  horiz_vertic
    (fun () -> sprintf "<li>something</li>")
    (fun () -> sprintf "<li>\n  something\n</li>");


Notice that the ``sprintf`` above is the one of the library
Pretty.

Notice also that, in a program displaying XML code, this "something"
may contain other XML tags, and is therefore generally the result of
other pretty printing functions, and the program should rather look
like:

::

  horiz_vertic
    (fun () -> sprintf "<li>%s</li>" (print something))
    (fun () -> sprintf "<li>\n  %s\n</li>" (print something))


Parts of this "something" can be printed horizontally and other
vertically using other calls to ``horiz_vertic`` in the user function
"print" above. But it is important to remark that if they are called
in the context of the first function parameter of ``horiz_vertic``
above, only horizontal functions are accepted: the first failing
"horizontal" function triggers the failure of the horizontal pretty
printing.

Programming with Pretty
=======================

Hints
-----

Just start with a call to ``horiz_vertic``.

As its first function, use ``sprintf`` just to concat the strings
without putting any newlines or indentations, e.g. just using spaces
to separate pieces of data.

As its second function, consider how you want your data to be cut.  At
the cutting point or points, add newlines. Notice that you probably
need to give the current indentation string as parameter of the called
functions because they need to be taken into account in the called
"horizontal" functions.

In the example below, don't put the indentation in the sprintf
function but give it as parameter of your "print" function:

::

  horiz_vertic
    (fun () -> sprintf "<li>%s</li>" (print "" something))
    (fun () -> sprintf "<li>\n%s\n</li>" (print "  " something))


Now, the "print" function could look like, supposing you print other
things with "other" of the current indentation and "things" with a new
shifted one:

::

  value print ind something =
    horiz_vertic
      (fun () -> sprintf "%sother things..." ind)
      (fun () -> sprintf "%sother\n%s  things..." ind ind);


Supposing than "other" and "things" are the result of two other
functions "print_other" and "print_things", your program could look
like:

::

  value print ind (x, y) =
    horiz_vertic
      (fun () -> sprintf "%s%s %s" ind (print_other 0 x) (print_things 0 y))
      (fun () -> sprintf "%s\n%s" (print_other ind x) (print_things (ind ^ "  ") y));


How to cancel a horizontal print
--------------------------------

If you want to prevent a pretty printing function from being called in
a horizontal context, constraining the pretty print to be on several
lines in the calling function, just do:

::

  horiz_vertic
    (fun () -> sprintf "\n")
    (fun () -> ... (* your normal pretty print *))


In this case, the horizontal print always fails, due to the newline
character in the sprintf format.

Remarks
=======

Kernel
------

The module ``Pretty`` is intended to be basic, a "kernel" module to
pretty print data. It presumes that the user takes care of the
indentation. Programs using ``Pretty`` are not as short as the ones
using ``Format`` of the OCaml library, but are more flexible. To pretty
print with a shorter syntax like in the OCaml module ``Format`` (with
the ``@`` convention), see :ref:`pprintf` (which internally uses the module
``Pretty``).

Strings vs Channels
-------------------

In ``Pretty``, the pretty printing is done only on strings, not on
files. To pretty print files, just build the strings and print them
afterwards with the usual output functions. Notice that OCaml
allocates and frees strings quickly, and if pretty printed values are
not huge, which is generally the case, it is not a real problem,
memory sizes these days being more than enough for this job.

Strings or other types
----------------------

The ``horiz_vertic`` function can return values of types other than
"string". For example, if you are interested only in the result of
horizontal context and not on the vertical one, it is perfectly
correct to write:

::

  horiz_vertic
    (fun () -> Some (sprintf "I hold on a single line")
    (fun () -> None)


Why raising exceptions ?
------------------------

One could ask why this pretty print system raises internal
exceptions. Why not simply write the pretty printing program like
this:

- first build the data horizontally (without newlines)
- if the string length is lower than the maximum line length, return
  it
- if not, build the string by adding newlines in the specific places

This method works but is generally very slow (exponential in time)
because while printing horizontally, many useless strings are
built. If, for example, the final printed data holds on 50 lines, tens
of lines may be built uselessly again and again before the overflowing
is corrected.

