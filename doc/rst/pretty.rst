Pretty print
============

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Pretty print
      :name: pretty-print
      :class: top

   A pretty print system is provided in the library module Pretty. It
   allows one to pretty print data or programs. The Pretty module
   contains:

   -  The function "horiz_vertic" to specify how data must be printed.
   -  The function "sprintf" to format strings.
   -  The variable "line_length" which is a reference specifying the
      maximum lines lengths.

   .. container::
      :name: tableofcontents

   .. rubric:: Module description
      :name: module-description

   .. rubric:: horiz_vertic
      :name: horiz_vertic

   The function "horiz_vertic" takes two functions as parameters. When
   invoked, it calls its first function. If that function fails with
   some specific internal error (that the function "``sprintf``" below
   may raise), the second function is called.

   The type of "horiz_vertic" is:

   ::

        (unit -> 'a) -> (unit -> 'a) -> 'a

   .. rubric:: the horizontal function
      :name: the-horizontal-function

   The first function is said to be the "horizontal" function. It tries
   to pretty print the data on a single line. In the context of this
   function, if the strings built by the function "sprintf" (see below)
   contain newlines or have lengths greater than "line_length", the
   function fails (with a internal exception local to the module).

   .. rubric:: the vertical function
      :name: the-vertical-function

   In case of failure of the "horizontal function", the second function
   of "horiz_vertic", the "vertical" function, is called. In the context
   of that function, the "sprintf" function behaves like the normal
   "sprintf" function of the OCaml library module "Printf".

   .. rubric:: sprintf
      :name: sprintf

   The function "sprintf" works like its equivalent in the module
   "Printf" of the OCaml library, and takes the same parameters. Its
   difference is that if it is called in the context of the first
   function (the "horizontal" function) of the function "horiz_vertic"
   (above), all strings built by "sprintf" are checked for newlines or
   length greater than the maximum line length. If either occurs, the
   "sprintf" function fails and the horizontal function fails.

   If "sprintf" is not in the context of the horizontal function, it
   behaves like the usual "sprintf" function.

   .. rubric:: line_length
      :name: line_length

   The variable "line_length" is a reference holding the maximum line
   length of lines printed horizontally. Its default is 78. This can be
   changed by the user before using "horiz_vertic".

   .. rubric:: horizontally
      :name: horizontally

   The call "``horizontally ()``" returns a boolean telling whether the
   context is horizontal.

   .. rubric:: Example
      :name: example

   Suppose you want to pretty print the XML code
   ``"<li>something</li>"``. If the "something" is short, you want to
   see:

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

   Notice that the "``sprintf``" above is the one of the library Pretty.

   Notice also that, in a program displaying XML code, this "something"
   may contain other XML tags, and is therefore generally the result of
   other pretty printing functions, and the program should rather look
   like:

   ::

        horiz_vertic
          (fun () -> sprintf "<li>%s</li>" (print something))
          (fun () -> sprintf "<li>\n  %s\n</li>" (print something))

   Parts of this "something" can be printed horizontally and other
   vertically using other calls to "horiz_vertic" in the user function
   "print" above. But it is important to remark that if they are called
   in the context of the first function parameter of "horiz_vertic"
   above, only horizontal functions are accepted: the first failing
   "horizontal" function triggers the failure of the horizontal pretty
   printing.

   .. rubric:: Programming with Pretty
      :name: programming-with-pretty

   .. rubric:: Hints
      :name: hints

   Just start with a call to "horiz_vertic".

   As its first function, use "sprintf" just to concat the strings
   without putting any newlines or indentations, e.g. just using spaces
   to separate pieces of data.

   As its second function, consider how you want your data to be cut. At
   the cutting point or points, add newlines. Notice that you probably
   need to give the current indentation string as parameter of the
   called functions because they need to be taken into account in the
   called "horizontal" functions.

   In the example below, don't put the indentation in the sprintf
   function but give it as parameter of your "print" function:

   ::

        horiz_vertic
          (fun () -> sprintf "<li>%s</li>" (print "" something))
          (fun () -> sprintf "<li>\n%s\n</li>" (print "  " something))

   Now, the "print" function could look like, supposing you print other
   things with "other" of the current indentation and "things" with a
   new shifted one:

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

   .. rubric:: How to cancel a horizontal print
      :name: how-to-cancel-a-horizontal-print

   If you want to prevent a pretty printing function from being called
   in a horizontal context, constraining the pretty print to be on
   several lines in the calling function, just do:

   ::

        horiz_vertic
          (fun () -> sprintf "\n")
          (fun () -> ... (* your normal pretty print *))

   In this case, the horizontal print always fails, due to the newline
   character in the sprintf format.

   .. rubric:: Remarks
      :name: remarks

   .. rubric:: Kernel
      :name: kernel

   The module "Pretty" is intended to be basic, a "kernel" module to
   pretty print data. It presumes that the user takes care of the
   indentation. Programs using "Pretty" are not as short as the ones
   using "Format" of the OCaml library, but are more flexible. To pretty
   print with a shorter syntax like in the OCaml module "Format" (with
   the "@" convention), see statement "`pprintf <pprintf.html>`__"
   (which internally uses the module "Pretty").

   .. rubric:: Strings vs Channels
      :name: strings-vs-channels

   In "Pretty", the pretty printing is done only on strings, not on
   files. To pretty print files, just build the strings and print them
   afterwards with the usual output functions. Notice that OCaml
   allocates and frees strings quickly, and if pretty printed values are
   not huge, which is generally the case, it is not a real problem,
   memory sizes these days being more than enough for this job.

   .. rubric:: Strings or other types
      :name: strings-or-other-types

   The "horiz_vertic" function can return values of types other than
   "string". For example, if you are interested only in the result of
   horizontal context and not on the vertical one, it is perfectly
   correct to write:

   ::

        horiz_vertic
          (fun () -> Some (sprintf "I hold on a single line")
          (fun () -> None)

   .. rubric:: Why raising exceptions ?
      :name: why-raising-exceptions

   One could ask why this pretty print system raises internal
   exceptions. Why not simply write the pretty printing program like
   this:

   #. first build the data horizontally (without newlines)
   #. if the string length is lower than the maximum line length, return
      it
   #. if not, build the string by adding newlines in the specific places

   This method works but is generally very slow (exponential in time)
   because while printing horizontally, many useless strings are built.
   If, for example, the final printed data holds on 50 lines, tens of
   lines may be built uselessly again and again before the overflowing
   is corrected.

   .. container:: trailer
