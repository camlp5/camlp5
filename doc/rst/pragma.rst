Pragma directive
================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Pragma directive
      :name: pragma-directive
      :class: top

   The directive "``#pragma``" allows to evaluate expressions at parse
   time, useful, for example, to test syntax extensions by the statement
   EXTEND without having to compile it in a separate file.

   To use it, add the syntax extension "``pa_pragma.cmo``" in the Camlp5
   command line. It adds the ability to use this directive.

   As an example, let's add syntax for the statement 'repeat' and use it
   immediately:

   ::

        #pragma
          EXTEND
            GLOBAL: expr;
            expr: LEVEL "top"
              [ [ "repeat"; e1 = sequence; "until"; e2 = SELF ->
                    <:expr< do { $e1$; while not $e2$ do { $e1$ } } >> ] ]
            ;
            sequence:
              [ [ el = LIST1 expr_semi -> <:expr< do { $list:el$ } >> ] ]
            ;
            expr_semi:
              [ [ e = expr; ";" -> e ] ]
            ;
          END;

        let i = ref 1 in
        repeat print_int i.val; print_endline ""; incr i; until i.val = 10;

   The compilation of this example (naming it "foo.ml") can be done with
   the command:

   ::

        ocamlc -pp "camlp5r q_MLast.cmo pa_extend.cmo pa_pragma.cmo" -I +camlp5 foo.ml

   Notice that it is still experimental and probably incomplete, for the
   moment.

   .. container:: trailer
