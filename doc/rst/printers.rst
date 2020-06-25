.. _extensible_printers:

Extensible printers
===================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Extensible printers
      :name: extensible-printers
      :class: top

   This chapter describes the syntax and semantics of the extensible
   printers of Camlp5.

   Similar to the `extensible grammars <grammars.html>`__, the
   extensible printers allow to define and extend printers of data or
   programs. A specific statement "``EXTEND_PRINTER``" allow to define
   these extensions.

   .. container::
      :name: tableofcontents

   .. rubric:: Getting started
      :name: getting-started

   A printer is a value of type "``Eprinter.t a``" where "``a``" is the
   type of the item to be printed. When applied, a printer returns a
   string, representing the printed item.

   To create a printer, one must use the function "``Eprinter.make``"
   with, as parameter, the name of the printer, (used in error
   messages). A printer is created empty, i.e. it fails if it is
   applied.

   As with grammar entries, printers may have several levels. When the
   function "``Eprinter.apply``" is applied to a printer, the first
   level is called. The function "``Eprinter.apply_level``" allows to
   call a printer at some specific level possibly different from the
   first one. When a level does not match any value of the printed item,
   the next level is tested. If there is no more levels, the printer
   fails.

   In semantic actions of printers, functions are provided to
   recursively call the current level and the next level. Moreover, a
   *printing context* variable is also given, giving the current
   indentation, what should be printed before in the same line and what
   should be printed after in the same line (it is not mandatory to use
   them).

   The extension of printers can be done with the "``EXTEND_PRINTER``"
   statement added by the *parsing kit* "``pa_extprint.cmo``".

   .. rubric:: Syntax of the EXTEND_PRINTER statement
      :name: syntax-of-the-extend_printer-statement

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

   .. rubric:: Semantics of EXTEND_PRINTER
      :name: semantics-of-extend_printer

   .. rubric:: Printers definition list
      :name: printers-definition-list

   All printers are extended according to their corresponding
   definitions which start with an optional "position" and follow with
   the "levels" definition.

   .. rubric:: Optional position
      :name: optional-position

   After the colon, it is possible to specify where to insert the
   defined levels:

   -  The identifier "``FIRST``" (resp. "``LAST``") indicates that the
      level must be inserted before (resp. after) all possibly existing
      levels of the entry. They become their first (resp. last) levels.
   -  The identifier "``BEFORE``" (resp. "``AFTER``") followed by a
      level label (a string) indicates that the levels must be inserted
      before (resp. after) that level, if it exists. If it does not
      exist, the extend statement fails at run time.
   -  The identifier "``LEVEL``" followed by a label indicates that the
      first level defined in the extend statement must be inserted at
      the given level, extending and modifying it. The other levels
      defined in the statement are inserted after this level, and before
      the possible levels following this level. If there is no level
      with this label, the extend statement fails at run time.
   -  By default, if the entry has no level, the levels defined in the
      statement are inserted in the entry. Otherwise the first defined
      level is inserted at the first level of the entry, extending or
      modifying it. The other levels are inserted afterwards (before the
      possible second level which may previously exist in the entry).

   .. rubric:: Levels
      :name: levels

   After the optional "position", the *level* list follow. The levels
   are separated by vertical bars, the whole list being between
   brackets.

   A level starts with an optional label, which corresponds to its name.
   This label is useful to specify this level in case of future
   extensions, using the *position* (see previous section) or for
   possible direct calls to this specific level.

   .. rubric:: Rules
      :name: rules

   A level is a list of *rules* separated by vertical bars, the whole
   list being between brackets.

   A rule is an usual pattern association (in a function or in the
   "match" statement), i.e. a pattern, an arrow and an expression. The
   expression is the semantic action which must be of type "``string``".

   .. rubric:: Rules insertion
      :name: rules-insertion

   The rules are sorted by their patterns, according to the rules of the
   `extensible functions <extfun.html>`__.

   .. rubric:: Semantic action
      :name: semantic-action

   The semantic action, i.e. the expression following the right arrow in
   rules, contains in its environment the variables bound by the pattern
   and three more variables:

   -  The variable "``curr``" which is a function which can be called to
      recursively invoke the printer at the current level,
   -  The variable "``next``" which is a function which can be called to
      invoke the printer at the next level,
   -  The variable "``pc``" which contains the printing context of type
      "``Pprintf.pr_context``" (see chapter `Pprintf <pprintf.html>`__).

   The variables "``curr``" and "``next``" are of type:

   ::

        pr_context -> t -> string

   where "``t``" is the type of the printer (i.e. the type of its
   patterns).

   The variable "``curr``", "``next``" and "``pc``" have predefined
   names and can hide the possible identifiers having the same names in
   the pattern or in the environment of the "``EXTEND_PRINTER``"
   statement.

   .. rubric:: The Eprinter module
      :name: the-eprinter-module

   See its `section <library.html#a:Eprinter-module>`__ in the chapter
   "Library".

   .. rubric:: Examples
      :name: examples

   .. rubric:: Parser and Printer of expressions
      :name: parser-and-printer-of-expressions

   This example illustrates the symmetry between parsers and printers. A
   simple type of expressions is defined. A parser converts a string to
   a value of this type, and a printer converts a value of this type to
   a string.

   In the printer, there is no use of the "``pc``" parameter and no use
   of the "``Pretty``" module. The strings are printed on a single line.

   Here is the source (file "``foo.ml``"):

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

   Remark on the use of "curr" and "next" while printing operators: due
   to left associativity, the first operand uses "curr" and the second
   operand uses "next". For right associativity operators, they should
   be inverted. For no associativity, both should use "next".

   The last line of the file allows use in either the OCaml toplevel or
   as standalone program, taking the string to be printed as parameter.
   It can be compiled this way:

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

   .. rubric:: Printing OCaml programs
      :name: printing-ocaml-programs

   Complete examples of usage of extensible printers are the printers in
   syntaxes and extended syntaxes provided by Camlp5 in the pretty
   printing *kits*:

   -  ``pr_r.cmo``: pretty print in revised syntax
   -  ``pr_o.cmo``: pretty print in normal syntax
   -  ``pr_rp.cmo``: also pretty print the parsers in revised syntax
   -  ``pr_op.cmo``: also pretty print the parsers in normal syntax

   See the chapter entitled "`Printing programs <opretty.html>`__".

   .. container:: trailer
