Extensions of printing
======================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Extensions of printing
      :name: extensions-of-printing
      :class: top

   Camlp5 provides extensions kits to pretty print programs in revised
   syntax and normal syntax. Some other extensions kits also allow to
   rebuild the parsers, or the EXTEND statements in their initial
   syntax. The pretty print system is itself extensible, by adding new
   rules. We present here how it works in the Camlp5 sources.

   The pretty print system of Camlp5 uses the library modules
   `Pretty <pretty.html>`__, an original system to format output) and
   `Extfun <extfun.html>`__, another original system of extensible
   functions.

   This chapter is designed for programmers that want to understand how
   the pretty printing of OCaml programs work in Camlp5, want to adapt,
   modify or debug it, or want to add their own pretty printing
   extensions.

   .. container::
      :name: tableofcontents

   .. rubric:: Introduction
      :name: introduction

   The files doing the pretty printings are located in Camlp5 sources in
   the directory "etc". Peruse them if you are interested in creating
   new ones. The main ones are:

   -  "etc/pr_r.ml": pretty print in revised syntax.
   -  "etc/pr_o.ml": pretty print in normal syntax.
   -  "etc/pr_rp.ml": rebuilding parsers in their original revised
      syntax.
   -  "etc/pr_op.ml": rebuilding parsers in their original normal
      syntax.
   -  "etc/pr_extend.ml": rebuilding EXTEND in its original syntax.

   We present here how this system works inside these files. First, the
   general principles. Second, more details of the implementation.

   .. rubric:: Principles
      :name: principles

   .. rubric:: Using module Pretty
      :name: using-module-pretty

   All functions in OCaml pretty printing take a parameter named "the
   printing context" (variable ``pc``). It is a record holding :

   -  The current indendation : ``pc.ind``
   -  What should be printed before, in the same line : ``pc.bef``
   -  What should be printed after, in the same line : ``pc.aft``
   -  The dangling token, useful in normal syntax to know whether
      parentheses are necessary : ``pc.dang``

   A typical pretty printing function calls the function
   ``horiz_vertic`` of the library module `Pretty <pretty.html>`__. This
   function takes two functions as parameter:

   -  The way to print the data in one only line (*horizontal* printing)
   -  The way to print the data in two or more lines (*vertical*
      printing)

   Both functions catenate the strings by using the function ``sprintf``
   of the library module ``Pretty`` which controls whether the printed
   data holds in the line or not. They generally call, recursively,
   other pretty printing functions with the same behaviour.

   Let us see an example (fictitious) of printing an OCaml application.
   Let us suppose we have an application expression "``e1 e2``" to
   pretty print where ``e1`` and ``e2`` are sub-expressions. If both
   expressions and their application holds on one only line, we want to
   see:

   ::

        e1 e2

   On the other hand, if they do not hold on one only line, we want to
   see ``e2`` in another line with, say, an indendation of 2 spaces:

   ::

        e1
          e2

   Here is a possible implementation. The function has been named
   ``expr_app`` and can call the function ``expr`` to print the
   sub-expressions ``e1`` and ``e2``:

   ::

        value expr_app pc e1 e2 =
          horiz_vertic
            (fun () ->
               let s1 = expr {(pc) with aft = ""} e1 in
               let s2 = expr {(pc) with bef = ""} e2 in
               sprintf "%s %s" s1 s2)
            (fun () ->
               let s1 = expr {(pc) with aft = ""} e1 in
               let s2 =
                 expr
                   {(pc) with
                      ind = pc.ind + 2;
                      bef = tab (pc.ind + 2)}
                   e2
               in
               sprintf "%s\n%s" s1 s2)
        ;

   The first function is the *horizontal* printing. It ends with a
   ``sprintf`` separating the printing of ``e1`` and ``e2`` by a space.
   The possible "before part" (``pc.bef``) and "after part" (``pc.aft``)
   are transmitted in the calls of the sub-functions.

   The second function is the *vertical* printing. It ends with a
   ``sprintf`` separating the printing of ``e1`` and ``e2`` by a
   newline. The second line starts with an indendation, using the
   "before part" (``pc.bef``) of the second call to ``expr``.

   The pretty printing library function ``Pretty.horiz_vertic`` calls
   the first (*horizontal*) function, and if it fails (either because
   ``s1`` or ``s2`` are too long or hold newlines, or because the final
   string produced by ``sprintf`` is too long), calls the second
   (*vertical*) function.

   Notice that the parameter ``pc`` contains a field ``pc.bef`` (what
   should be printed before in the same line), which in both cases is
   transmitted to the printing of ``e1`` (since the syntax
   ``{(pc) with aft =   ""}`` is a record with ``pc.bef`` kept). Same
   for the field ``pc.aft`` transmitted to the printing of ``e2``.

   .. rubric:: Using EXTEND_PRINTER statement
      :name: using-extend_printer-statement

   This system is combined to the `extensible
   printers <printers.html>`__ to allow the extensibility of the pretty
   printing.

   The code above actually looks like:

   ::

        EXTEND_PRINTER
          pr_expr:
            [ [ <:expr< $e1$ $e2$ >> ->
                  horiz_vertic
                    (fun () ->
                       let s1 = curr {(pc) with aft = ""} e1 in
                       let s2 = next {(pc) with bef = ""} e2 in
                       sprintf "%s %s" s1 s2)
                    (fun () ->
                       let s1 = curr {(pc) with aft = ""} e1 in
                       let s2 =
                         next
                           {(pc) with
                              ind = pc.ind + 2;
                              bef = tab (pc.ind + 2)}
                           e2
                       in
                       sprintf "%s\n%s" s1 s2) ] ]
          ;
        END;

   The variable "``pc``" is implicit in the semantic actions of the
   syntax "``EXTEND_PRINTER``", as well as two other variables:
   "``curr``" and "``next``".

   These parameters, "``curr``" and "``next``", correspond to the pretty
   printing of, respectively, the current level and the next level.
   Since the application in OCaml is left associative, the first
   sub-expression is printed at the same (current) level and the second
   one is printed at the next level. We also see a call to ``next`` in
   the last (2nd) case of the function to treat the other cases in the
   next level.

   .. rubric:: Dangling else, bar, semicolon
      :name: dangling-else-bar-semicolon

   In normal syntax, there are cases where it is necessary to enclose
   expressions between parentheses (or between begin and end, which is
   equivalent in that syntax). Three tokens may cause problems: the
   "``else``", the vertical bar "``|``" and the semicolon "``;``". Here
   are examples where the presence of these tokens constrains the
   previous expression to be parenthesized. In these three examples,
   removing the begin..end enclosers would change the meaning of the
   expression because the dangling token would be included in that
   expression:

   Dangling else:

   ::

        if a then begin if b then c end else d

   Dangling bar:

   ::

        function
          A ->
            begin match a with
              B -> c
            | D -> e
            end
        | F -> g

   Dangling semicolon:

   ::

        if a then b
        else begin
          let c = d in
          e
        end;
        f

   The information is transmitted by the value ``pc.dang``. In the first
   example above, while displaying the "``then``" part of the outer
   "``if``", the sub-expression is called with the value ``pc.dang`` set
   to ``"else"`` to inform the last sub-sub-expression that it is going
   to be followed by that token. When a "``if``" expression should be
   displayed without "``else``" part, and that its "``pc.dang``" is
   "else", it should be enclosed with spaces.

   This problem does not exist in revised syntax. While pretty printing
   in revised syntax, the parameter ``pc.dang`` is not necessary and
   remains the empty string.

   .. rubric:: By level
      :name: by-level

   As explained in the chapter about the `extensible
   printers <printers.html>`__ (with the EXTEND_PRINTER statement),
   printers contain levels. The global printer variable of expressions
   is named "``pr_expr``" and contain all definitions for pretty
   printing expressions, organized by levels, just like the parsing of
   expressions. The definition of "``pr_expr``" actually looks like
   this:

   ::

        EXTEND_PRINTER
          pr_expr:
            [ "top"
              [ (* code for level "top" *) ]
            | "add"
              [ (* code for level "add" *) ]
            | "mul"
              [ (* code for level "mul" *) ]
            | "apply"
              [ (* code for level "apply" *) ]
            | "simple"
              [ (* code for level "add" *) ] ]
          ;
        END;

   .. rubric:: The Prtools module
      :name: the-prtools-module

   The Prtools module is defined inside Camlp5 for pretty printing kits.
   It provides variables and functions to process comments, and
   meta-functions to process lists (horizontally, vertically,
   paragraphly).

   .. rubric:: Comments
      :name: comments

   ``value comm_bef : int -> MLast.loc -> string;``
      "``comm_bef ind loc``" get the comment from the source just before
      the given location "``loc``". This comment may be reindented using
      "``ind``". Returns the empty string if no comment found.

   ``value source : ref string;``
      The initial source string, which must be set by the pretty
      printing kit. Used by [comm_bef] above.
   ``value set_comm_min_pos : int -> unit;``
      Set the minimum position of the source where comments can be
      found, (to prevent possible duplication of comments).

   .. rubric:: Meta functions for lists
      :name: meta-functions-for-lists

   ``type pr_fun 'a = pr_context -> 'a -> string;``
      Type of printer functions.

   ``value hlist : pr_fun 'a -> pr_fun (list 'a);``
      [hlist elem pc el] returns the horizontally pretty printed string
      of a list of elements; elements are separated with spaces.
      The list is displayed in one only line. If this function is called
      in the context of the [horiz] function of the function
      [horiz_vertic] of the module Printing, and if the line overflows
      or contains newlines, the function internally fails (the exception
      is catched by [horiz_vertic] for a vertical pretty print).
   ``value hlist2 : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);``
      horizontal list with a different function from 2nd element on.
   ``value hlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);``
      horizontal list with a different function for the last element.

   ``value vlist : pr_fun 'a -> pr_fun (list 'a);``
      [vlist elem pc el] returns the vertically pretty printed string of
      a list of elements; elements are separated with newlines and
      indentations.
   ``value vlist2 : pr_fun 'a -> pr_fun 'a -> pr_fun (list    'a);``
      vertical list with different function from 2nd element on.
   ``value vlist3 : pr_fun ('a * bool) -> pr_fun ('a * bool) -> pr_fun       (list 'a);``
      vertical list with different function from 2nd element on, the
      boolean value being True for the last element of the list.
   ``value vlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list    'a);``
      vertical list with different function for the last element.

   ``value plist : pr_fun 'a -> int -> pr_fun (list ('a *    string));``
      [plist elem sh pc el] returns the pretty printed string of a list
      of elements with separators. The elements are printed horizontally
      as far as possible. When an element does not fit on the line, a
      newline is added and the element is displayed in the next line
      with an indentation of [sh]. [elem] is the function to print
      elements, [el] a list of pairs (element \* separator) (the last
      separator being ignored).
   ``value plistb : pr_fun 'a -> int -> pr_fun (list ('a *       string));``
      [plist elem sh pc el] returns the pretty printed string of the
      list of elements, like with [plist] but the value of [pc.bef]
      corresponds to an element already printed, as it were on the list.
      Therefore, if the first element of [el] does not fit in the line,
      a newline and a tabulation is added after [pc.bef].
   ``value plistl : pr_fun 'a -> pr_fun 'a -> int -> pr_fun (list       ('a * string));``
      paragraph list with a different function for the last element.

   ``value hvlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list    'a);``
      applies "``hlistl``" if the context is horizontal; else applies
      "``vlistl``".

   .. rubric:: Miscellaneous
      :name: miscellaneous

   ``value tab : int -> string;``
      [tab ind] is equivalent to [String.make ind ' ']

   ``value flatten_sequence : MLast.expr -> option (list    MLast.expr);``
      [flatten_sequence e]. If [e] is an expression representing a
      sequence, return the list of expressions of the sequence. If some
      of these expressions are already sequences, they are flattened in
      the list. If that list contains expressions of the form let..in
      sequence, this sub-sequence is also flattened with the let..in
      applying only to the first expression of the sequence. If [e] is a
      let..in sequence, it works the same way. If [e] is not a sequence
      nor a let..in sequence, return None.

   .. rubric:: Example : repeat..until
      :name: example-repeat..until

   This pretty prints the example
   `repeat..until <syntext.html#a:An-example-:-repeat..until>`__
   statement programmed in the chapter `Syntax
   extensions <syntext.html>`__ (first version generating a "``while``"
   statement).

   .. rubric:: The code
      :name: the-code

   The pattern generated by the "repeat" statement is recognized
   (sequence ending with a "``while``" whose contents is the same than
   the beginning of the sequence) by the function "is_repeat" and the
   repeat statement is pretty printed in its initial form using the
   function "horiz_vertic" of the Pretty module. File
   "``pr_repeat.ml``":

   ::

        #load "pa_extprint.cmo";
        #load "q_MLast.cmo";

        open Pcaml;
        open Pretty;
        open Prtools;

        value eq_expr_list el1 el2 =
          if List.length el1 <> List.length el2 then False
          else List.for_all2 eq_expr el1 el2
        ;

        value is_repeat el =
          match List.rev el with
          [ [<:expr< while not $e$ do { $list:el2$ } >> :: rel1] ->
              eq_expr_list (List.rev rel1) el2
          | _ -> False ]
        ;

        value semi_after pr pc = pr {(pc) with aft = sprintf "%s;" pc.aft};

        EXTEND_PRINTER
          pr_expr:
            [ [ <:expr< do { $list:el$ } >> when is_repeat el ->
                  match List.rev el with
                  [ [<:expr< while not $e$ do { $list:el$ } >> :: _] ->
                      horiz_vertic
                        (fun () ->
                           sprintf "%srepeat %s until %s%s" pc.bef
                             (hlistl (semi_after curr) curr
                                {(pc) with bef = ""; aft = ""} el)
                             (curr {(pc) with bef = ""; aft = ""} e)
                             pc.aft)
                        (fun () ->
                           let s1 = sprintf "%srepeat" (tab pc.ind) in
                           let s2 =
                             vlistl (semi_after curr) curr
                               {(pc) with
                                ind = pc.ind + 2;
                                bef = tab (pc.ind + 2);
                                aft = ""}
                               el
                           in
                           let s3 =
                             sprintf "%suntil %s" (tab pc.ind)
                               (curr {(pc) with bef = ""} e)
                           in
                           sprintf "%s\n%s\n%s" s1 s2 s3)
                  | _ -> assert False ] ] ]
          ;
        END;

   .. rubric:: Compilation
      :name: compilation

   ::

        ocamlc -pp camlp5r -I +camlp5 -c pr_repeat.ml

   .. rubric:: Testing
      :name: testing

   Getting the same files "foo.ml" and "bar.ml" of the repeat syntax
   example:

   ::

        $ cat bar.ml
        #load "./foo.cmo";
        value x = ref 42;
        repeat
          print_int x.val;
          print_endline "";
          x.val := x.val + 3
        until x.val > 70;

        $ camlp

   Without the pretty printing kit:

   ::

        $ camlp5r pr_r.cmo bar.ml
        #load "./foo.cmo";
        value x = ref 42;
        do {
          print_int x.val;
          print_endline "";
          x.val := x.val + 3;
          while not (x.val > 70) do {
            print_int x.val;
            print_endline "";
            x.val := x.val + 3
          }
        };

   With the pretty printing kit:

   ::

        $ camlp5r pr_r.cmo ./pr_repeat.cmo bar.ml -l 75
        #load "./foo.cmo";
        value x = ref 42;
        repeat
          print_int x.val;
          print_endline "";
          x.val := x.val + 3
        until x.val > 70;

   .. container:: trailer
