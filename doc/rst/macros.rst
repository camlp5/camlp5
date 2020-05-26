Macros
======


.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Macros
      :name: macros
      :class: top

   Camlp5 provides a system of macros, added by the parsing kit
   "``pa_macro.cmo``". Macros are values evaluated at parsing time.

   When loaded, the parsing kit extends the syntax of the language and
   adds command options.

   .. container::
      :name: tableofcontents

   .. rubric:: Added syntax
      :name: added-syntax

   The parsing kit "``pa_macro.cmo``" extends the structure items (=
   toplevel phrases), the expressions and the patterns by the following
   grammar rules:

   ::

                 str-item ::= str-macro-def
                 sig-item ::= sig-macro-def
                     expr ::= macro-expr
                     patt ::= macro-patt
                cons-decl ::= macro-cons-decl
             rec-lab-decl ::= macro-rec-lab-decl
              match-assoc ::= macro-match-assoc
            str_macro-def ::= "DEFINE" uident
                            | "DEFINE" uident "=" expr
                            | "DEFINE" uident params "=" expr
                            | "UNDEF" uident
                            | "IFDEF" dexpr "THEN" st-or-mac else-str "END"
                            | "IFNDEF" dexpr "THEN" st-or-mac else-str "END"
                 else-str ::= "ELSIFDEF" dexpr "THEN" st-or-mac else-str
                            | "ELSIFNDEF" dexpr "THEN" st-or-mac else-str
                            | "ELSE" st-or-mac else-str
                            | <nothing>
            sig_macro-def ::= "DEFINE" uident
                            | "DEFINE" uident params "=" type
                            | "UNDEF" uident
                            | "IFDEF" dexpr "THEN" sg-or-mac else-sig "END"
                            | "IFNDEF" dexpr "THEN" sg-or-mac else-sig "END"
                 else-sig ::= "ELSIFDEF" dexpr "THEN" sg-or-mac else-sig
                            | "ELSIFNDEF" dexpr "THEN" sg-or-mac else-sig
                            | "ELSE" st-or-mac else-sig
                            | <nothing>
               macro-expr ::= "IFDEF" dexpr "THEN" expr else-expr "END"
                            | "IFNDEF" dexpr "THEN" expr else-expr "END"
                            | "__FILE__"
                            | "__LOCATION__"
                else-expr ::= "ELSIFDEF" dexpr "THEN" expr else-expr
                            | "ELSIFNDEF" dexpr "THEN" expr else-expr
                            | "ELSE" expr else-expr
               macro-patt ::= "IFDEF" dexpr "THEN" patt "ELSE" patt "END"
                            | "IFNDEF" dexpr "THEN" patt "ELSE" patt "END"
          macro-cons-decl ::= "IFDEF" dexpr "THEN" cons-decl "END"
                            | "IFDEF" dexpr "THEN" cons-decl
                              "ELSE" cons-decl "END"
                            | "IFNDEF" dexpr "THEN" cons-decl "END"
                            | "IFNDEF" dexpr "THEN" cons-decl
                              "ELSE" cons-decl "END"
       macro-rec-lab-decl ::= "IFDEF" dexpr "THEN" rec-lab-decl "END"
                            | "IFDEF" dexpr "THEN" rec-lab-decl
                              "ELSE" rec-lab-decl "END"
                            | "IFNDEF" dexpr "THEN" rec-lab-decl "END"
                            | "IFNDEF" dexpr "THEN" rec-lab-decl
                              "ELSE" rec-lab-decl "END"
        macro-match-assoc ::= "IFDEF" dexpr "THEN" match_assoc "END"
                            | "IFDEF" dexpr "THEN" match-assoc
                              "ELSE" match-assoc "END"
                            | "IFNDEF" dexpr "THEN" match-assoc "END"
                            | "IFNDEF" dexpr "THEN" match-assoc
                              "ELSE" match-assoc "END"
                st-or-mac ::= str_macro-def
                            | structure
                sg-or-mac ::= sig-macro-def
                            | signature
                   params ::= ident params
                            | ident
                    dexpr ::= dexpr "OR" dexpr
                            | dexpr "AND" dexpr
                            | "NOT" dexpr
                            | uident
                            | "(" dexpr ")"
                   uident ::= 'A'-'Z' ident
                    ident ::= ident-char*
               ident-char ::= ('a'-'a' | 'A'-'Z' | '0'-'9' | '_' | ''' |
                               misc-byte)
                misc-byte ::= '\128'-'\255'

   When a macro has been defined, as name e.g. "NAME", the expressions
   and patterns are extended this way:

   ::

              expr ::= "NAME"
                     | "NAME" "(" expr-params ")"
              patt ::= "NAME"
                     | "NAME" "(" patt-params ")"
        expr-params := expr "," expr-params
                     | expr
        patt-params := patt "," patt-params
                     | patt

   Notice that the identifiers "``DEFINE``", "``UNDEF``", "``IFDEF``",
   "``IFNDEF``", "``ELSE``", "``END``", "``OR``", "``AND``" and
   "``NOT``" are new keywords (they cannot be used as identifiers of
   constructors or modules.

   However, the identifiers "``__FILE__``" and "``__LOCATION__``" and
   the new defined macro names are not new identifiers.

   .. rubric:: Added command options
      :name: added-command-options

   The parsing kit "``pa_macro.cmo``" also add two options usable in all
   Camlp5 commands:

   ``-D uident``
      Define the uident in question like would have been a DEFINE
      (without parameter) in the code.
   ``-U uident``
      Undefine the uident in question like would have been a UNDEF in
      the code.
   ``-defined``
      Print the defined macros and exit.

   .. rubric:: Semantics
      :name: semantics

   The statement "``DEFINE``" defines a new macro with optional
   parameters and an optional value. The macro name must start with an
   uppercase letter.

   The test of a macro can be done either:

   -  in structure items
   -  in signature items
   -  in expressions
   -  in patterns
   -  in a constructor declaration
   -  in a match case

   using the statement "``IFDEF``". Its non-existence can be tested by
   "``IFNDEF``". In expressions and patterns, the "``ELSE``" part is
   required, not in structure items.

   The expression behind the "``IFDEF``" or the "``IFNDEF``" statement
   may use the operators "``OR``", "``AND``" and "``NOT``" and contain
   parentheses.

   Notice that in an "``IFDEF``" where the value is True (resp. False),
   the "``ELSE``" (resp "``THEN``") part does not need to be
   semantically correct (well typed), since it does not appear in the
   resulting syntax tree. Same for "``IFNDEF``" and for possible macros
   parameters which are not used in the associated expression.

   If a macro is defined twice, its first version is lost.

   The statement "``UNDEF``" removes a macro definition.

   When associated with a value, the "``DEFINE``" macro acts like a
   variable (or like a function call if it has parameters), except that
   the parameters are evaluated at parse time and can also be used also
   in pattern positions. Notice that this is a way to define constants
   by name in patterns. For example:

   ::

        DEFINE WW1 = 1914;
        DEFINE WW2 = 1939;
        value war_or_year =
          fun
          [ WW1 -> "world war I"
          | WW2 -> "world war II"
          | _ -> "not a war" ]
        ;

   In the definition of a macro, if the expression contains an
   evaluation, the evaluation is not done by Camlp5 but just transmitted
   as code. In this case, it does not work in pattern position. Example
   in the toplevel:

   ::

        # DEFINE PLUS(x, y) = x + y;
        # PLUS(3, 4);
        - : int = 7
        #   fun [ PLUS(3, 4) -> () ];
        Toplevel input:
        #   fun [ PLUS(3, 4) -> () ];
                  ^^^^^^^^^^
        Failure: this is not a constructor, it cannot be applied in a pattern

   On the other hand, if the expression does not contain evaluation,
   this is possible:

   ::

        # DEFINE FOO(x, y) = (x, Some y);
        # FOO(True, "bar");
        - : (bool * option string) = (True, Some "bar")
        # fun [ FOO(_, "hello") -> 0 | _ -> 1 ];
        - : ('a * option string) -> int = <fun>

   The macro "``__FILE__``" is replaced by the current compiled source
   file name. In the OCaml toplevel, its value is the empty string.

   The macro "``__LOCATION__``" is replaced by the the current location
   (two integers in number of characters from the beginning of the file,
   starting at zero) of the macro itself.

   In signatures, the macro definitions can return types which can be
   used in type definitions.

   In constructor declarations and in match cases, it is possible to
   conditionally define some cases by "``IFDEF``" or "``IFNDEF``". For
   example:

   ::

        type t =
          [ A of int
          | IFNDEF FOO THEN
              B of string
            END
          | C of bool ]
        ;

        match x with
        [ A i -> j
        | IFNDEF FOO THEN
            B s -> toto
          END
        | C b -> e ];

   .. rubric:: Predefined macros
      :name: predefined-macros

   The macro "``CAMLP5``" is always predefined.

   The macro "``OCAML_oversion``" is predefined, where "``oversion``" is
   the OCaml version the Camlp5 program has been compiled with, where
   all characters but numbers are replaced by underscores. For example,
   if using OCaml 3.09.3, the macro "``OCAML_3_09_3``" is defined.

   Moreover, for *some* Camlp5 versions (and all the versions which
   follows them), the macro "``CAMLP5_version``" is defined where
   "``version``" is the Camlp5 version where all characters but numbers
   are replaced by underscores. For example, in version 4.02, the macro
   "``CAMLP5_4_02``" had been defined and this macro have appeared in
   all versions of Camlp5 since 4.02.

   To see which macros are predefined, type:

   ::

        camlp5r pa_macro.cmo -defined

   .. container:: trailer
