Extensions of syntax
====================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Extensions of syntax
      :name: extensions-of-syntax
      :class: top

   Camlp5 allows one to extend the syntax of the OCaml language, and
   even change the entire syntax.

   It uses for that one of its parsing tools: the `extensible
   grammars <grammars.html>`__.

   To understand the whole syntax in the examples given in this chapter,
   it is good to understand this parsing tool (the extensible grammars),
   but we shall try to give some minimal explanations to allow the
   reader to follow them.

   A syntax extension is an OCaml object file (ending with ".cmo" or
   ".cma") which is loaded inside Camlp5. The source of this file uses
   calls to the specific statement EXTEND applied to entries defined in
   the Camlp5 module "``Pcaml``".

   .. container::
      :name: tableofcontents

   .. rubric:: Entries
      :name: entries

   The grammar of OCaml contains several entries, corresponding to the
   major notions of the language, which are modifiable this way, and
   even erasable. They are defined in this module "``Pcaml``".

   Most important entries:

   -  ``expr``: the expressions.
   -  ``patt``: the patterns.
   -  ``ctyp``: the types.
   -  ``str_item``: the structure items, i.e. the items between "struct"
      and "end", and the toplevel phrases in a ".ml" file.
   -  ``sig_item``: the signature items, i.e. the items between "sig"
      and "end", and the toplevel phrases in a ".mli" file.
   -  ``module_expr``: the module expressions.
   -  ``module_type``: the module types.

   Entries of object programming:

   -  ``class_expr``: the class expressions.
   -  ``class_type``: the class types.
   -  ``class_str_item``: the objects items.
   -  ``class_sig_item``: the objects types items.

   Main entries of files and interactive toplevel parsing:

   -  ``implem``: the phrases that can be found in a ".ml" file.
   -  ``interf``: the phrases that can be found in a ".mli" file.
   -  ``top_phrase``: the phrases of the interactive toplevel.
   -  ``use_file``: the phrases that can be found in a file included by
      the directive "use".

   Extra useful entries also accessible:

   -  ``let_binding``: the bindings "expression = pattern" found in the
      "let" statement.
   -  ``type_declaration``: the bindings "name = type" found in the
      "type" statement.

   .. rubric:: Syntax tree quotations
      :name: syntax-tree-quotations

   A grammar rule is a list of rule symbols followed by the semantic
   action, i.e. the result of the rule. This result is a syntax tree,
   whose type is the type of the extended entry. The description of the
   types of the syntax tree are in the Camlp5 module "``MLast``".

   There is however a simpler way to make values of these syntax tree
   types: the system quotations (see chapters about
   `quotations <quot.html>`__ and `syntax tree <ml_ast.html>`__). With
   this system, it is possible to represent syntax tree in concrete
   syntax, between specific parentheses, namely "``<<``" and "``>>``",
   or between "``<:name<``" and "``>>``".

   For example, the syntax node of the "if" statement is, normally:

   ::

        MLast.ExIfe loc e1 e2 e3

   where loc is the source location, and e1, e2, e3 are the expressions
   constituting the if statement. With quotations, it is possible to
   write it like this (which is stricly equivalent because this is
   evaluated at parse time, not execution time):

   ::

        <:expr< if $e1$ then $e2$ else $e3$ >>

   With quotations, it is possible to build pieces of program as complex
   as desired. See the chapter about `syntax trees <ml_ast.html>`__.

   .. rubric:: An example : repeat..until
      :name: an-example-repeat..until

   A classical extension is the creation of the "repeat" statement. The
   "repeat" statement is like a "while" except that the loop is executed
   at least one time and that the test is at the end of the loop and is
   inverted. The equivalent of:

   ::

        repeat x; y; z until c

   is:

   ::

        do {
          x; y; z;
          while not c do { x; y; z }
        }

   or, with a loop:

   ::

        loop () where rec loop () = do {
          x; y; z;
          if c then () else loop ()
        }

   .. rubric:: The code
      :name: the-code

   This syntax extension could be written like this (see the detail of
   syntax in the chapter about `extensible grammars <grammars.html>`__
   and the syntax tree quotations in the chapter about
   `them <ml_ast.html>`__):

   ::

        #load "pa_extend.cmo";
        #load "q_MLast.cmo";
        open Pcaml;
        EXTEND
          expr:
            [ [ "repeat"; el = LIST1 expr SEP ";"; "until"; c = expr ->
                  let el = el @ [<:expr< while not $c$ do { $list:el$ } >>] in
                  <:expr< do { $list:el$ } >> ] ]
          ;
        END;

   Alternatively, with the loop version:

   ::

        #load "pa_extend.cmo";
        #load "q_MLast.cmo";
        open Pcaml;
        EXTEND
          expr:
            [ [ "repeat"; el = LIST1 expr SEP ";"; "until"; c = expr ->
                  let el = el @ [<:expr< if $c$ then () else loop () >>] in
                  <:expr< loop () where rec loop () = do { $list:el$ } >> ] ]
          ;
        END;

   The first "``#load``" in the code (in both files) means that a syntax
   extension has been used in the file, namely the "EXTEND" statement.
   The second "``#load``" means that abstract tree
   `quotations <quot.html>`__ has been used, namely the
   "``<:expr< ... >>``".

   The quotation, found in the second version:

   ::

        <:expr< loop () where rec loop () = do { $list:el$ } >>

   is especially interesting. Written with abstract syntax tree, it
   would be:

   ::

        MLast.ExLet loc True
          [(MLast.PaLid loc "loop",
            MLast.ExFun loc [(MLast.PaUid loc "()", None, MLast.ExSeq loc el)])]
          (MLast.ExApp loc (MLast.ExLid loc "loop") (MLast.ExUid loc "()"));

   This shows the interest of writing abstract syntax tree with
   quotations: it is easier to program and to understand.

   .. rubric:: Compilation
      :name: compilation

   If the file "foo.ml" contains one of these versions, it is possible
   to compile it like this:

   ::

        ocamlc -pp camlp5r -I +camlp5 -c foo.ml

   Notice that the ocamlc option "-c" means that we are interested only
   in generating the object file "foo.cmo", not achieving the
   compilation by creating an executable. Anyway the link would not work
   because of usage of modules specific to Camlp5.

   .. rubric:: Testing
      :name: testing

   .. rubric:: In the OCaml toplevel
      :name: in-the-ocaml-toplevel

   ::

        ocaml -I +camlp5 camlp5r.cma
                Objective Caml version ...

                Camlp5 Parsing version ...

        # #load "foo.cmo";
        # value x = ref 42;
        value x : ref int = {val=42}
        # repeat
            print_int x.val; print_endline ""; x.val := x.val + 3
          until x.val > 70;
        42
        45
        48
        51
        54
        57
        60
        63
        66
        69
        - : unit = ()

   .. rubric:: In a file
      :name: in-a-file

   The code, above, used in the toplevel, can be written in a file, say
   "bar.ml":

   ::

        #load "./foo.cmo";
        value x = ref 42;
        repeat
          print_int x.val;
          print_endline "";
          x.val := x.val + 3
        until x.val > 70;

   with a subtile difference: the loaded file must be "``./foo.cmo``"
   and not just "``foo.cmo``" because Camlp5 does not have, by default,
   the current directory in its path.

   The file can be compiled like this:

   ::

        ocamlc -pp camlp5r bar.ml

   or in native code:

   ::

        ocamlopt -pp camlp5r bar.ml

   And it is possible to check the resulting program by typing:

   ::

        camlp5r pr_r.cmo bar.ml

   whose displayed result is:

   ::

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

   See also the `same
   example <opretty.html#a:Example-:-repeat--until>`__ pretty printed in
   its original syntax, using the extendable `programs
   printing <opretty.html>`__.

   .. container:: trailer
