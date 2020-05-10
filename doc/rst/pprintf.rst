Pprintf
=======

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Pprintf
      :name: pprintf
      :class: top

   This chapter describes "pprintf", a statement to pretty print data.
   It looks like the "sprintf" function of the OCaml library, and
   borrows some ideas of the Format OCaml library. Another statement,
   "lprintf", is a slightly different version of "pprintf" handling with
   locations.

   .. container::
      :name: tableofcontents

   .. rubric:: Syntax of the pprintf statement
      :name: syntax-of-the-pprintf-statement

   The "pprintf" statement is added by the *parsing kit*
   "``pa_pprintf.cmo``".

   Notice that, in opposition to "printf", "fprintf", "sprintf", and all
   its variants, which are functions, this "pprintf" is a *statement*,
   not a function: "pprintf" is a keyword and the expander analyzes its
   string format parameter to generate specific statements. In
   particular, it cannot be used alone and has no type by itself.

   ::

              expression ::= pprintf-statement
       pprintf-statement ::= "pprintf" qualid format expressions
                  qualid ::= qualid "." qualid
                           | uident
                           | lident
                  format ::= string
             expressions ::= expression expressions
                           | <nothing>

   .. rubric:: Semantics of pprintf
      :name: semantics-of-pprintf

   The "pprintf" statement converts the format string into a string like
   the "sprintf" of the OCaml library "Printf" does (see the OCaml
   manual for details). The string format can accept new conversion
   specifications, "%p" and "%q", and some pretty printing annotations,
   starting with "@" like in the OCaml library "Format".

   The "pprintf" statement takes as first parameter, a value of type
   "pr_context" defined below. Its second parameter is the extended
   format string. It can take other parameters, depending on the format,
   like "sprintf".

   The result of "pprintf" is always a string. There is no versions
   applying to files or buffers.

   The strings built by "pprintf" are concatened by the function
   "Pretty.sprintf" (see the chapter entitled "`Pretty
   Print <pretty.html>`__") which controls the line length and prevents
   overflowing.

   .. rubric:: Printing context
      :name: printing-context

   The "pprintf" statement takes, as first parameter, a *printing
   context*. It is a value of the following type:

   ::

        type pr_context =
          { ind : int;
            bef : string;
            aft : string;
            dang : string };

   The fields are:

   -  "``ind``" : the current indendation
   -  "``bef``" : what should be printed before, in the same line
   -  "``aft``" : what should be printed after, in the same line
   -  "``dang``" : the dangling token to know whether parentheses are
      necessary

   Basically, the "pprintf" statement concats the "bef" string, the
   formatted string and the "aft" string. The example:

   ::

        pprintf pc "hello world"

   is equivalent to (and indeed generates):

   ::

        Pretty.sprintf "%shello world%s" pc.bef pc.aft

   But if the format string contains conversion specifications "%p" or
   "%q", the "bef" and "aft" strings are actually transmitted to the
   corresponding functions:

   ::

        pprintf pc "hello %p world" f x

   is equivalent to:

   ::

        f {(pc) with
           bef = Pretty.sprintf "%shello " pc.bef;
           aft = Pretty.sprintf " world%s" pc.aft}
          x

   Thus, the decision of including the "bef" and the "aft" strings are
   delayed to the called function, allowing this function to possibly
   concatenate "bef" and "aft" to its own strings.

   A typical case is, while printing programs, when an expression needs
   to be printed between parentheses. The code which does that looks
   like:

   ::

        pprintf pc "(%p)" expr e

   The right parenthesis of this string format is included in the "aft"
   string transmitted to the function "expr". In a situation when
   several right parentheses are concatened this way, the fact that all
   these parentheses are grouped together allows the function which
   eventually print them to decide to break the line or not, these
   parentheses being taken into account in the line length.

   For example, if the code contains a print of an program containing an
   application whose source is:

   ::

        myfunction myarg

   and if the "aft" contains "))))))", the decision of printing in one
   line as:

   ::

        myfunction myarg))))))

   or in two lines as:

   ::

        myfunction
          myarg))))))

   is exact, the right parentheses being added to "myarg" to determine
   whether the line overflows or not.

   .. rubric:: Extended format
      :name: extended-format

   The extended format used by "pprintf" may contain any strings and
   conversion specifications allowed by the "sprintf" function (see
   module "Printf" of the OCaml library), plus:

   -  the conversion specifications: "``%p``" and "``q``",
   -  the pretty printing annotations introduced by, "``@``" and
      followed by:

      -  the character "``;``" (semicolon), optionally followed by
         "``<``", two numbers and "``>``",
      -  the character "`` ``" (space),
      -  the character "``[``", optionally followed by the character
         "``<``" and either:

         -  the character "``a``"
         -  the character "``b``"
         -  a number

         and the character "``>``", then followed by format string, and
         ended with "``@]``"

   The format string is applied like in the "sprintf" function. Specific
   actions are done for the extended features. The result is a string
   like for the "sprintf" function. The "string before" and "string
   after" defined by the fields "bef" and "aft" of the printing context
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

   .. rubric:: Line length
      :name: line-length

   The function "pprintf" uses the Camlp5 "Pretty" module. The line
   length can be set by changing the value of the reference
   "Pretty.line_length".

   .. rubric:: The conversion specifications "p" and "q"
      :name: the-conversion-specifications-p-and-q

   The "%p" conversion specification works like the "%a" of the printf
   statement. It takes two arguments and applies the first one to the
   printing context and to the second argument. The first argument must
   therefore have type "``pr_context -> t -> unit``" (for some type
   "``t``") and the second one "t".

   Notice that this function can be called twice: one to test whether
   the resulting string holds in the line, and another one to possibly
   recall this function to print it in several lines. In the two cases,
   the printing context given as parameter is different.

   It uses the functions defined in the "`Pretty <pretty.html>`__"
   module.

   Example: the following statement:

   ::

        pprintf pc "hello, %p, world" f x

   is equivalent to:

   ::

        f {(pc) with
           bef = Pretty.sprintf "%shello, " pc.bef;
           aft = Pretty.sprintf ", world%s" pc.aft}
          x

   The "%q" conversion specification is like "%p" except that it takes a
   third argument which is the value of the "dang" field, useful when
   the syntax has "dangling" problems requiring parentheses. See chapter
   `Extensions of printing <opretty.html>`__ for more explanations about
   dangling problems.

   The same example with "%q":

   ::

        pprintf pc "hello, %q, world" f x "abc"

   is equivalent to:

   ::

        f {(pc) with
           bef = Pretty.sprintf "%shello, " pc.bef;
           aft = Pretty.sprintf ", world%s" pc.aft;
           dang = "abc"}
          x

   .. rubric:: The pretty printing annotations
      :name: the-pretty-printing-annotations

   .. rubric:: Breaks
      :name: breaks

   The pretty printing annotations allow to indicate places where lines
   can be broken. They all start with the "at" sign "@". The main ones
   are called *breaks* and are:

   -  "``@;``" specifying: *write a space or 'a newline and an
      indentation incremented by 2 spaces'*
   -  "``@ ``" specifying: *write a space or 'a newline and the
      indentation'*

   Example - where "pc" is a variable of type "pr_context" (for example
   "Pprintf.empty_pc"):

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

   -  "``@;<s o>``", which is a break with "``s``" spaces if the string
      holds in the line, or an indentation offset (incrementation of the
      indentation) of "``o``" spaces if the string does not hold in the
      line.

   The break "``@;``" is therefore equivalent to "``@;<1   2>``" and
   "``@ ``" is equivalent to "``@;<1   0>``".

   .. rubric:: Parentheses
      :name: parentheses

   A second form of the pretty printing annotations is the
   parenthesization of format strings possibly containing other pretty
   printing annotations. They start with "``@[``" and end with "``@]``".

   It allows to change the associativity of the breaks. For example:

   ::

        pprintf pc "@[the quick brown fox@;jumps@]@;over the lazy dog"

   If the whole string holds on the line, it is printed:

   ::

        the quick brown fox jumps over the lazy dog

   If the whole string does not hold on the line, but "the quick brow
   fox jumps" does, it is printed:

   ::

        the quick brown fox jumps
          over the lazy dog

   If the string "the quick brown fox jumps" does not hold on the line,
   the whole string is printed:

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

   .. rubric:: Incrementation of indentation
      :name: incrementation-of-indentation

   The open parenthesis of the parenthesized form, "``@[``" can be
   followed by "``<n>``" where "``n``" is a number. It increments the
   current indentation (for possible newlines in the parenthesized text)
   with this number.

   Example:

   ::

        pprintf pc "@[<4>Incrementation@;actually of six characters@]"

   makes the string (if not holding in the line):

   ::

        Incrementation
              actually of six characters

   .. rubric:: Break all or nothing
      :name: break-all-or-nothing

   The open parenthesis of the parenthesized form, "``@[``" can be
   followed by "``<a>``". It specifies that if the string does not hold
   in the line, all breaks between the parentheses (at one only level)
   are printed in two lines, even if sub-strings could hold on the line.
   For example:

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

   .. rubric:: Break all
      :name: break-all

   The open parenthesis of the parenthesized form, "``@[``" can be
   followed by "``<b>``". It specifies that all breaks are always
   printed in two lines. For example:

   ::

        pprintf pc "@[<b>the quick brown fox@;jumps@;over the lazy dog@]"

   is printed in all circumstances:

   ::

        the quick brown fox
          jumps
          over the lazy dog

   .. rubric:: Break all if
      :name: break-all-if

   The open parenthesis of the parenthesized form, "``@[``" can be
   followed by "``<i>``". Depending on the value of the boolean variable
   of the argument list, the breaks are all printed in two lines like
   with the "break all" option above, or not. For example:

   ::

        pprintf pc "%s@;@[<i>%s,@;%s@]" "good" True "morning" "everybody";
        pprintf pc "%s@;@[<i>%s,@;%s@]" "good" False "morning" "everybody";

   are printed:

   ::

        good
          morning,
            everybody
        good morning, everybody

   .. rubric:: Parentheses not neighbours of breaks
      :name: parentheses-not-neighbours-of-breaks

   In the examples above, we can remark that the left parentheses are
   always the begin of the string or are preceeded by a break, and that
   the right parentheses are always the end of the string or followed by
   a break.

   When the parentheses "``@[``" and "``@]``" are not preceeded or
   followed by the string begin nor end, nor preceeded or followed by
   breaks, they are considered as the "bef" or "aft" part of the
   neighbour string. For example, the following forms:

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
   if the non-parenthesized part contain one or several "%p". In this
   case, the corresponding function receives the "bef" or "aft" part in
   its pr_context variable and can take it into account when printing
   its data.

   .. rubric:: Lprintf
      :name: lprintf

   "Lprintf" is like "pprintf" with the same parameters. It is
   equivalent to an call to the function "expand_lprintf":

   ::

         lprintf pc "..."

   is equivalent to:

   ::

         expand_lprintf pc loc (fun pc -< pprintf pc "...")

   The function "expand_lprintf" and the variable "loc" must be defined
   by the user in the environment where "lprintf" is used.

   "Lprintf" is used in predefined printers "pr_r.ml" and "pr_o.ml" to
   allow optional insertions of location comments in the output.

   .. rubric:: Comparison with the OCaml modules Printf and Format
      :name: comparison-with-the-ocaml-modules-printf-and-format

   .. rubric:: Pprintf and Printf
      :name: pprintf-and-printf

   The statement "pprintf" acts like the function "Printf.sprintf". But
   since it requires this extra parameter of type "pr_context" and needs
   the "%p" and "%q" conversions specifications (which do not exist in
   "Printf"), it was not possible to use the "Printf" machinery directly
   and a new statement had to be added.

   The principle of "pprintf" and "sprintf" are the same. However,
   "pprintf" is a syntax extension and has no type by itself. It cannot
   be used alone or without all its required parameters.

   .. rubric:: Pprintf and Format
      :name: pprintf-and-format

   The pretty printing annotations look like the ones of the OCaml
   module Format. Actually, they have different semantics. They do not
   use *boxes* like "Format" does. In "pprintf" statement, the machinery
   acts only on indentations.

   Notice that, with "pprintf", it is always possible to know the
   current indentation (it is the field "ind" of the "pr_context"
   variable) and it is therefore possible to take decisions before
   printing.

   For example, it is possible, in a printer of OCaml statements, to
   decide to print all match cases symmetrically, i.e. all with one line
   for each case or all with newlines after the patterns.

   It is what is done in the option "``-flag E``" added by the pretty
   printing kits "pr_r.cmo" (pretty print in revised syntax) and
   "pr_o.cmo" (pretty print in normal syntax). See chapter `Commands and
   Files <commands.html>`__ or type "``camlp5 pr_r.cmo -help``" or
   "``camlp5 pr_o.cmo   -help``".

   Another difference is that the internal behaviour of this printing
   system is accessible, and it is always possible to use the basic
   functions of the "Pretty" module ("horiz_vertic" and "sprintf") if
   the behaviour of "pprintf" is not what is desired by the programmer.

   .. rubric:: Relation with the Camlp5 extensible printers
      :name: relation-with-the-camlp5-extensible-printers

   The extensible printers of Camlp5 (see its corresponding
   `chapter <printers.html>`__) use the type "``pr_context``" of
   "pprintf". It is therefore possible to use "pprintf" in the semantic
   actions of the extensible printers. But it is not mandatory. An
   extensible printer can just use the "Pretty" module or even neither
   "pprintf" nor "Pretty".

   The printing kits "``pr_r.ml``" and "``pr_o.ml``" (respectively
   pretty print in revised and in normal syntax) and some other related
   to them, are examples of usage of the "pprintf" statement.

   .. rubric:: The Pprintf module
      :name: the-pprintf-module

   See its `section <library.html#a:Pprintf-module>`__ in the chapter
   "Library".

   .. container:: trailer
