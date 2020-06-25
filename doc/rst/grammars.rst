.. _extensible_grammars:

Extensible grammars
===================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Extensible grammars
      :name: extensible-grammars
      :class: top

   This chapter describes the syntax and semantics of the extensible
   grammars of Camlp5.

   The extensible grammars are the most advanced parsing tool of Camlp5.
   They apply to streams of characters using a lexer which has to be
   previously defined by the programmer. In Camlp5, the syntax of the
   OCaml language is defined with extensible grammars, which makes
   Camlp5 a bootstrapped system (it compiles its own features by
   itself).

   .. container::
      :name: tableofcontents

   .. rubric:: Getting started
      :name: getting-started

   The extensible grammars are a system to build *grammar entries* which
   can be extended dynamically. A grammar entry is an abstract value
   internally containing a stream parser. The type of a grammar entry is
   ``"Grammar.Entry.e t"`` where ``"t"`` is the type of the values
   returned by the grammar entry.

   To start with extensible grammars, it is necessary to build a
   *grammar*, a value of type "``Grammar.g``", using the function
   "``Grammar.gcreate``":

   ::

        value g = Grammar.gcreate lexer;

   where "``lexer``" is a lexer previously defined. See the section
   explaining the interface with lexers. In a first time, it is possible
   to use a lexer of the module "``Plexer``" provided by Camlp5:

   ::

        value g = Grammar.gcreate (Plexer.gmake ());

   Each grammar entry is associated with a grammar. Only grammar entries
   of the same grammar can call each other. To create a grammar entry,
   one has to use the function "``Grammar.Entry.create``" with takes the
   grammar as first parameter and a name as second parameter. This name
   is used in case of syntax errors. For example:

   ::

        value exp = Grammar.Entry.create g "expression";

   To apply a grammar entry, the function "``Grammar.Entry.parse``" can
   be used. Its first parameter is the grammar entry, the second one a
   stream of characters:

   ::

        Grammar.Entry.parse exp (Stream.of_string "hello");

   But if you experiment this, since the entry was just created without
   any rules, you receive an error message:

   ::

        Stream.Error "entry [expression] is empty"

   To add grammar rules to the grammar entry, it is necessary to
   *extend* it, using a specific syntactic statement: "``EXTEND``".

   .. rubric:: Syntax of the EXTEND statement
      :name: syntax-of-the-extend-statement

   The "``EXTEND``" statement is added in the expressions of the OCaml
   language when the syntax extension kit "``pa_extend.cmo``" is loaded.
   Its syntax is:

   ::

          expression ::= extend
              extend ::= "EXTEND" extend-body "END"
         extend-body ::= global-opt entries
          global-opt ::= "GLOBAL" ":" entry-names ";"
                       | <nothing>
         entry-names ::= entry-name entry-names
                       | entry-name
               entry ::= entry-name ":" position-opt "[" levels "]"
        position-opt ::= "FIRST"
                       | "LAST"
                       | "BEFORE" label
                       | "AFTER" label
                       | "LIKE" string
                       | "LEVEL" label
                       | <nothing>
              levels ::= level "|" levels
                       | level
               level ::= label-opt assoc-opt "[" rules "]"
           label-opt ::= label
                       | <nothing>
           assoc-opt ::= "LEFTA"
                       | "RIGHTA"
                       | "NONA"
                       | <nothing>
               rules ::= rule "|" rules
                       | rule
                rule ::= psymbols-opt "->" expression
                       | psymbols-opt
        psymbols-opt ::= psymbols
                       | <nothing>
            psymbols ::= psymbol ";" psymbols
                       | psymbol
             psymbol ::= symbol
                       | pattern "=" symbol
              symbol ::= keyword
                       | token
                       | token string
                       | entry-name
                       | entry-name "LEVEL" label
                       | "SELF"
                       | "NEXT"
                       | "LIST0" symbol
                       | "LIST0" symbol "SEP" symbol opt-opt-sep
                       | "LIST1" symbol
                       | "LIST1" symbol "SEP" symbol opt-opt-sep
                       | "OPT" symbol
                       | "FLAG" symbol
                       | "V" symbol opt-strings
                       | "[" rules "]"
                       | "(" symbol ")"
         opt-opt-sep ::= "OPT_SEP"
                       | <nothing>
         opt-strings ::= string opt-strings
                       | <nothing>
             keyword ::= string
               token ::= uident
               label ::= string
          entry-name ::= qualid
              qualid ::= qualid "." qualid
                       | uident
                       | lident
              uident ::= 'A'-'Z' ident
              lident ::= ('a'-'z' | '_' | misc-letter) ident
               ident ::= ident-char*
          ident-char ::= ('a'-'a' | 'A'-'Z' | '0'-'9' | '_' | ''' | misc-letter)
         misc-letter ::= '\128'-'\255'

   Other statements, "``GEXTEND``", "``DELETE_RULE``",
   "``GDELETE_RULE``" are also defined by the same syntax extension kit.
   See further.

   In the description above, only "``EXTEND``" and "``END``" are new
   keywords (reserved words which cannot be used in variables,
   constructors or module names). The other strings (e.g. "``GLOBAL``",
   "``LEVEL``", "``LIST0``", "``LEFTA``", etc.) are not reserved.

   .. rubric:: Semantics of the EXTEND statement
      :name: semantics-of-the-extend-statement

   The EXTEND statement starts with the "``EXTEND``" keyword and ends
   with the "``END``" keyword.

   .. rubric:: GLOBAL indicator
      :name: global-indicator

   After the first keyword, it is possible to see the identifier
   "``GLOBAL``" followed by a colon, a list of entries names and a
   semicolon. It says that these entries correspond to visible
   (previously defined) entry variables, in the context of the EXTEND
   statement, the other ones being locally and silently defined inside.

   -  If an entry, which is extended in the EXTEND statement, is in the
      GLOBAL list, but is not defined in the context of the EXTEND
      statement, the OCaml compiler will fail with the error "unbound
      value".
   -  If there is no GLOBAL indicator, and an entry, which is extended
      in the EXTEND statement, is not defined in the contex of the
      EXTEND statement, the OCaml compiler will also fail with the error
      "unbound value".

   Example:

   ::

        value exp = Grammar.Entry.create g "exp";
        EXTEND
          GLOBAL: exp;
          exp: [ [ x = foo; y = bar ] ];
          foo: [ [ "foo" ] ];
          bar: [ [ "bar" ] ];
        END;

   The entry "exp" is an existing variable (defined by value exp = ...).
   On the other hand, the entries "foo" and "bar" have not been defined.
   Because of the GLOBAL indicator, the system define them locally.

   Without the GLOBAL indicator, the three entries would have been
   considered as global variables, therefore the OCaml compiler would
   say "unbound variable" under the first undefined entry, "foo".

   .. rubric:: Entries list
      :name: entries-list

   Then the list of entries extensions follow. An entry extension starts
   with the entry name followed by a colon. An entry may have several
   levels corresponding to several stream parsers which call the ones
   the others (see further).

   .. rubric:: Optional position
      :name: optional-position

   After the colon, it is possible to specify a where to insert the
   defined levels:

   -  The identifier "``FIRST``" (resp. "``LAST``") indicates that the
      level must be inserted before (resp. after) all possibly existing
      levels of the entry. They become their first (resp. last) levels.
   -  The identifier "``BEFORE``" (resp. "``AFTER``") followed by a
      level label (a string) indicates that the levels must be inserted
      before (resp. after) that level, if it exists. If it does not
      exist, the extend statement fails at run time.
   -  The identifier "``LIKE``" followed by a string indicates that the
      first level defined in the extend statement must be inserted in
      the first already existing level with a rule containing this
      string as keyword or token name. For example, "``LIKE "match"``"
      is the first level having "``match``" as keyword. If there is no
      level with this string, the extend statement fails at run time.
   -  The identifier "``LEVEL``" followed by a level label indicates
      that the first level defined in the extend statement must be
      inserted at the given level, extending and modifying it. The other
      levels defined in the statement are inserted after this level, and
      before the possible levels following this level. If there is no
      level with this label, the extend statement fails at run time.
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

   The level continues with an optional associativity indicator, which
   can be:

   -  LEFTA for left associativity (default),
   -  RIGHTA for right associativity,
   -  NONA for no associativity.

   .. rubric:: Rules
      :name: rules

   At last, the grammar *rule* list appear. The rules are separated by
   vertical bars, the whole list being brackets.

   A rule looks like a match case in the "``match``" statement or a
   parser case in the "``parser``" statement: a list of psymbols (see
   next paragraph) separated by semicolons, followed by a right arrow
   and an expression, the semantic action. Actually, the right arrow and
   expression are optional: in this case, it is equivalent to an
   expression which would be the unit "``()``" constructor.

   A psymbol is either a pattern, followed with the equal sign and a
   symbol, or by a symbol alone. It corresponds to a test of this
   symbol, whose value is bound to the pattern if any.

   .. rubric:: Symbols
      :name: symbols

   A symbol is an item in a grammar rule. It is either:

   -  a keyword (a string): the input must match this keyword,
   -  a token name (an identifier starting with an uppercase character),
      optionally followed by a string: the input must match this token
      (any value if no string, or that string if a string follows the
      token name), the list of the available tokens depending on the
      associated lexer (the list of tokens available with "Plexer.gmake
      ()" is: LIDENT, UIDENT, TILDEIDENT, TILDEIDENTCOLON,
      QUESTIONIDENT, INT, INT_l, INT_L, INT_n, FLOAT, CHAR, STRING,
      QUOTATION, ANTIQUOT and EOI; other lexers may propose other lists
      of tokens),
   -  an entry name, which correspond to a call to this entry,
   -  an entry name followed by the identifier "``LEVEL``" and a level
      label, which correspond to the call to this entry at that level,
   -  the identifier "``SELF``" which is a recursive call to the present
      entry, according to the associativity (i.e. it may be a call at
      the current level, to the next level, or to the top level of the
      entry): "``SELF``" is equivalent to the name of the entry itself,
   -  the identifier "``NEXT``", which is a call to the next level of
      the current entry,
   -  a left brace, followed by a list of rules separated by vertical
      bars, and a right brace: equivalent to a call to an entry, with
      these rules, inlined,
   -  a meta symbol (see further),
   -  a symbol between parentheses.

   The syntactic analysis follow the list of symbols. If it fails,
   depending on the first items of the rule (see the section about the
   kind of grammars recognized):

   -  the parsing may fail by raising the exception "``Stream.Error``"
   -  the parsing may continue with the next rule.

   .. rubric:: Meta symbols
      :name: meta-symbols

   Extra symbols exist, allowing to manipulate lists or optional
   symbols. They are:

   -  LIST0 followed by a symbol: this is a list of this symbol,
      possibly empty,
   -  LIST0 followed by a symbol, SEP and another symbol, and optional
      OPT_SEP: this is a list, possibly empty, of the first symbol
      separated by the second one, possibly ended with the separator if
      OPT_SEP is present,
   -  LIST1 followed by a symbol: this is a list of this symbol, with at
      least one element,
   -  LIST1 followed by a symbol, SEP and another symbol, and optional
      OPT_SEP: this is a list, with at least one element, of the first
      symbol separated by the second one, possibly ended with the
      separator if OPT_SEP is present,
   -  OPT followed by a symbol: equivalent to "this symbol or nothing"
      returning a value of type "``option``".
   -  FLAG followed by a symbol: equivalent to "this symbol or nothing",
      returning a boolean.

   .. rubric:: The V meta symbol
      :name: the-v-meta-symbol

   The V meta symbol is destinated to allow antiquotations while using
   the syntax tree quotation kit ```q_ast.cmo`` <q_ast.html>`__. It
   works only in strict mode. In transitional mode, it is just
   equivalent to its symbol parameter.

   .. rubric:: Antiquotation kind
      :name: antiquotation-kind

   The antiquotation kind is the optional identifier between the
   starting "``$``" (dollar) and the "``:``" (colon) in a quotation of
   syntax tree (see the chapter `syntax tree <ml_ast.html>`__).

   The optional list of strings following the "V" meta symbol and its
   symbol parameter gives the allowed antiquotations kinds.

   By default, this string list, i.e. the available antiquotation kinds,
   is:

   -  ``["flag"]`` for FLAG
   -  ``["list"]`` for LIST0 and LIST1
   -  ``["opt"]`` for OPT

   For example, the symbol:

   ::

        V (FLAG "rec")

   is like "FLAG" while normally parsing, allowing to parse the keyword
   "``rec``". While using it in quotations, also allows the parse the
   keyword "``rec``" but, moreover, the antiquotation "``$flag:..$``"
   where "``..``" is an expression or a pattern depending on the
   position of the quotation.

   There are also default antiquotations kinds for the tokens used in
   the OCaml language predefined parsers "``pa_r.cmo``" (revised syntax)
   and "``pa_o.cmo``" (normal syntax), actually all parsers using the
   provided lexer "``Plexer``" (see the chapter
   `Library <library.html>`__). They are:

   -  ``["chr"]`` for CHAR
   -  ``["flo"]`` for FLOAT
   -  ``["int"]`` for INT
   -  ``["int32"]`` for INT_l
   -  ``["int64"]`` for INT_L
   -  ``["nativeint"]`` for INT_n
   -  ``["lid"]`` for LIDENT
   -  ``["str"]`` for STRING
   -  ``["uid"]`` for UIDENT

   It is also possible to use the "V" meta symbol over non-terminals
   (grammars entries), but there is no default antiquotation kind. For
   example, while parsing a quotation, the symbol:

   ::

        V foo "bar" "oops"

   corresponds to either a call to the grammar entry "``foo``", or to
   the antiquotations "``$bar:...$``" or "``$oops:...$``".

   .. rubric:: Type
      :name: type

   The type of the value returned by a V meta symbol is:

   -  in transitional mode, the type of its symbol parameter,
   -  in strict mode, "``Ploc.vala t``", where "``t``" is its symbol
      parameter.

   In strict mode, if the symbol parameter is found, whose value is,
   say, "``x``", the result is "``Ploc.VaVal x``". If an antiquotation
   is found the result is "``Ploc.VaAnt s``" where "``s``" is some
   string containing the antiquotation text and some other internal
   information.

   .. rubric:: Rules insertion
      :name: rules-insertion

   Remember that "``EXTEND``" is a statement, not a declaration: the
   rules are added in the entries at run time. Each rule is internally
   inserted in a tree, allowing the left factorization of the rule. For
   example, with this list of rules (borrowed from the Camlp5 sources):

   ::

        "method"; "private"; "virtual"; l = label; ":"; t = poly_type
        "method"; "virtual"; "private"; l = label; ":"; t = poly_type
        "method"; "virtual"; l = label; ":"; t = poly_type
        "method"; "private"; l = label; ":"; t = poly_type; "="; e = expr
        "method"; "private"; l = label; sb = fun_binding
        "method"; l = label; ":"; t = poly_type; "="; e = expr
        "method"; l = label; sb = fun_binding

   the rules are inserted in a tree and the result looks like:

   ::

        "method"
           |-- "private"
           |       |-- "virtual"
           |       |       |-- label
           |       |             |-- ":"
           |       |                  |-- poly_type
           |       |-- label
           |             |-- ":"
           |             |    |-- poly_type
           |             |            |-- ":="
           |             |                 |-- expr
           |             |-- fun_binding
           |-- "virtual"
           |       |-- "private"
           |       |       |-- label
           |       |             |-- ":"
           |       |                  |-- poly_type
           |       |-- label
           |             |-- ":"
           |                  |-- poly_type
           |-- label
                 |-- ":"
                 |    |-- poly_type
                 |            |-- "="
                 |                 |-- expr
                 |-- fun_binding

   This tree is built as long as rules are inserted. When used, by
   applying the function "``Grammar.Entry.parse``" to the current entry,
   the input is matched with that tree, starting from the tree root,
   descending on it as long as the parsing advances.

   There is a different tree by entry level.

   .. rubric:: Semantic action
      :name: semantic-action

   The semantic action, i.e. the expression following the right arrow in
   rules, contains in its environment:

   -  the variables bound by the patterns of the symbols found in the
      rules,
   -  the specific variable "``loc``" which contain the location of the
      whole rule in the source.

   The location is an abstract type defined in the module "``Ploc``" of
   Camlp5.

   It is possible to change the name of this variable by using the
   option "``-loc``" of Camlp5. For example, compiling a file like this:

   ::

        camlp5r -loc foobar file.ml

   the variable name, for the location will be "``foobar``" instead of
   "``loc``".

   .. rubric:: The DELETE_RULE statement
      :name: the-delete_rule-statement

   The "``DELETE_RULE``" statement is also added in the expressions of
   the OCaml language when the syntax extension kit "``pa_extend.cmo``"
   is loaded. Its syntax is:

   ::

              expression ::= delete-rule
             delete-rule ::= "DELETE_RULE" delete-rule-body "END"
        delete-rule-body ::= entry-name ":" symbols
                 symbols ::= symbol symbols
                           | symbol

   See the syntax of the EXTEND statement for the meaning of the syntax
   entries not defined above.

   The entry is scanned for a rule matching the giving symbol list. When
   found, the rule is removed. If no rule is found, the exception
   "``Not_found``" is raised.

   .. rubric:: Extensions FOLD0 and FOLD1
      :name: extensions-fold0-and-fold1

   When loading "``pa_extfold.cmo``" after "``pa_extend.cmo``", the
   entry "``symbol``" of the EXTEND statement is extended with what is
   named the *fold iterators*, like this:

   ::

             symbol ::= "FOLD0" simple_expr simple_expr symbol
                      | "FOLD1" simple_expr simple_expr symbol
                      | "FOLD0" simple_expr simple_expr symbol "SEP" symbol
                      | "FOLD1" simple_expr simple_expr symbol "SEP" symbol
        simple_expr ::= expr (level "simple")

   Like their equivalent with the lists iterators: "``LIST0``",
   "``LIST1``", "``LIST0SEP``", "``LIST1SEP``", they read a sequence of
   symbols, possibly with the separators, but instead of building the
   list of these symbols, apply a fold function to each symbol, starting
   at the second "expr" (which must be a expression node) and continuing
   with the first "expr" (which must be a function taking two
   expressions and returing a new expression).

   The list iterators can be seen almost as a specific case of these
   fold iterators where the initial "expr" would be:

   ::

        <:expr< [] >>

   and the fold function would be:

   ::

        fun e1 e2 -> <:expr< [$e1$ :: $e2$ ] >>

   except that, implemented like that, they would return the list in
   reverse order.

   Actually, a program using them can be written with the lists
   iterators with the semantic action applying the function
   "``List.fold_left``" to the returned list, except that with the fold
   iterators, this operation is done as long as the symbols are read on
   the input, no intermediate list being built.

   Example, file "sum.ml":

   ::

        #load "pa_extend.cmo";
        #load "pa_extfold.cmo";
        #load "q_MLast.cmo";
        let loc = Ploc.dummy in
        EXTEND
          Pcaml.expr:
            [ [ "sum";
                e =
                  FOLD0 (fun e1 e2 -> <:expr< $e2$ + $e1$ >>) <:expr< 0 >>
                    Pcaml.expr SEP ";";
                "end" -> e ] ]
          ;
        END;

   which can be compiled like this:

   ::

        ocamlc -pp camlp5r -I +camlp5 -c sum.ml

   and tested:

   ::

        ocaml -I +camlp5 camlp5r.cma sum.cmo
                Objective Caml version ...

                Camlp5 Parsing version ...

        # sum 3;4;5 end;
      - : int = 12

   .. rubric:: Grammar machinery
      :name: grammar-machinery

   We explain here the detail of the mechanism of the parsing of an
   entry.

   .. rubric:: Start and Continue
      :name: start-and-continue

   At each entry level, the rules are separated into two trees:

   -  The tree of the rules *not* starting with the current entry name
      nor by "``SELF``".
   -  The tree of the rules starting with the current entry name or by
      the identifier "``SELF``", this symbol not being included in the
      tree.

   They determine two functions:

   -  The function named "start", analyzing the first tree.
   -  The function named "continue", taking, as parameter, a value
      previously parsed, and analyzing the second tree.

   A call to an entry, using "``Grammar.Entry.parse``" correspond to a
   call to the "start" function of the first level of the entry.

   The "start" function tries its associated tree. If it works, it calls
   the "continue" function of the same level, giving the result of
   "start" as parameter. If this "continue" function fails, this
   parameter is simply returned. If the "start" function fails, the
   "start" function of the next level is tested. If there is no more
   levels, the parsing fails.

   The "continue" function first tries the "continue" function of the
   next level. If it fails, or if it is the last level, it tries its
   associated tree, then calls itself again, giving the result as
   parameter. If its associated tree fails, it returns its extra
   parameter.

   .. rubric:: Associativity
      :name: associativity

   While testing the tree, there is a special case for rules ending with
   SELF or with the current entry name. For this last symbol, there is a
   call to the "start" function: of the current level if the level is
   right associative, or of the next level otherwise.

   There is no behaviour difference between left and non associative,
   because, in case of syntax error, the system attempts to recover the
   error by applying the "continue" function of the previous symbol (if
   this symbol is a call to an entry).

   When a SELF or the current entry name is encountered in the middle
   of the rule (i.e. if it is neither the first nor the last symbol),
   there is a call to the "start" function of the first level of the
   current entry.

   Example. Let us consider the following grammar:

   ::

        EXTEND
          expr:
            [ "minus" LEFTA
              [ x = SELF; "-"; y = SELF -> x -. y ]
            | "power" RIGHTA
              [ x = SELF; "**"; y = SELF -> x ** y ]
            | "simple"
              [ "("; x = SELF; ")" -> x
              | x = INT -> float_of_int x ] ]
          ;
        END

   The left "SELF"s of the two levels "minus" and "power" correspond to
   a call to the next level. In the level "minus", the right "SELF"
   also, and the left associativity is treated by the fact that the
   "continue" function is called (starting with the keyword "-" since
   the left "SELF" is not part of the tree). On the other hand, for the
   level "power", the right "SELF" corresponds to a call to the current
   level, i.e. the level "power" again. At end, the "SELF" between
   parentheses of the level "simple" correspond to a call to the first
   level, namely "minus" in this grammar.

   .. rubric:: Parsing algorithm
      :name: parsing-algorithm

   By default, the kind of grammar is predictive parsing grammar, i.e.
   recursive descent parsing without backtrack. But with some nuances,
   due to the improvements (error recovery and token starting rules)
   indicated in the next sections.

   However, it is possible to change the parsing algorithm, by calling
   the function "``Grammar.set_algorithm``". The possible values are:

   ``Grammar.Predictive``
      internally using `normal parsers <parsers.html>`__, with a
      predictive (recursive descent without backtracking) algorithm.
   ``Grammar.Functional``
      internally using `functional parsers <fparsers.html>`__, with a
      limited backtracking algorithm,
   ``Grammar.Backtracking``
      internally using `backtracking parsers <bparsers.html>`__, with a
      full backtracking algorithm,
   ``Grammar.DefaultAlgorithm``
      the parsing algorithm is determined by the environment variable
      "CAMLP5PARAM". If this environment variable exists and contains
      "f", the parsing algorithm is "functional"; if it it "b", the
      parsing algorithm is "backtracking". Otherwise it is "predictive".

   An interesting function, when using then backtracking algorithm, is
   "``Grammar.Entry.parse_all``" which returns all solutions of a given
   input.

   See details in the chapter `Library <library.html>`__, section
   "Grammar module".

   .. rubric:: Errors and recovery
      :name: errors-and-recovery

   In extensible grammars, the exceptions are encapsulated with the
   exception "Ploc.Exc" giving the location of the error together with
   the exception itself.

   If the parsing algorithm is "``Grammar.Predictive``", the system
   internally uses `stream parsers <parsers.html>`__. Two exceptions may
   happen: "Stream.Failure" or "Stream.Error". "Stream.Failure"
   indicates that the parsing just could not start. "Stream.Error"
   indicates that the parsing started but failed further.

   With this algorithm, when the first symbol of a rule has been
   accepted, all the symbols of the same rule must be accepted,
   otherwise the exception "Stream.Error" is raised.

   If the parsing algorithm is "``Grammar.Functional``" (resp.
   "``Grammar.Backtracking``"), the system internally uses `functional
   parsers <fparsers.html>`__ (resp `backtracking
   parsers <bparsers.html>`__. If no solution is found, the exception
   "``Stream.Error``" is raised and the location of the error is the
   location of the last unfrozen token, i.e. where the stream advanced
   the farthest.

   In extensible grammars, unlike stream parsers, before the
   "Stream.Error" exception, the system attempts to recover the error by
   the following trick: if the previous symbol of the rule was a call to
   another entry, the system calls the "continue" function of that
   entry, which may resolve the problem.

   .. rubric:: Tokens starting rules
      :name: tokens-starting-rules

   Another improvement (other than error recovery) is that when a rule
   starts with several tokens and/or keywords, all these tokens and
   keywords are tested in one time, and the possible "Stream.Error" may
   happen, only from the symbol following them on, if any.

   .. rubric:: The Grammar module
      :name: the-grammar-module

   See its `section <library.html#a:Grammar-module>`__ in the chapter
   "Library".

   .. rubric:: Interface with the lexer
      :name: interface-with-the-lexer

   To create a grammar, the function "``Grammar.gcreate``" must be
   called, with a lexer as parameter.

   A simple solution, as possible lexer, is the predefined lexer built
   by "``Plexer.gmake ()``", lexer used for the OCaml grammar of Camlp5.
   In this case, you can just put it as parameter of
   "``Grammar.gcreate``" and it is not necessary to read this section.

   The section first introduces the notion of "token patterns" which are
   the way the tokens and keywords symbols in the EXTEND statement are
   represented. Then follow the description of the type of the parameter
   of "``Grammar.gcreate``".

   .. rubric:: Token patterns
      :name: token-patterns

   A token pattern is a value of the type defined like this:

   ::

        type pattern = (string * string);

   This type represents values of the token and keywords symbols in the
   grammar rules.

   For a token symbol in the grammar rules, the first string is the
   token constructor name (starting with an uppercase character), the
   second string indicates whether the match is "any" (the empty string)
   or some specific value of the token (an non-empty string).

   For a keyword symbol, the first string is empty and the second string
   is the keyword itself.

   For example, given this grammar rule:

   ::

        "for"; i = LIDENT; "="; e1 = SELF; "to"; e2 = SELF

   the different symbols and keywords are represented by the following
   couples of strings:

   -  the keyword "for" is represented by ``("", "for")``,
   -  the keyword "=" by ``("", "=")``,
   -  the keyword "to" by ``("", "to")``),
   -  and the token symbol ``LIDENT`` by ``("LIDENT", "")``.

   The symbol ``UIDENT "Foo"`` in a rule would be represented by the
   token pattern:

   ::

        ("UIDENT", "Foo")

   Notice that the symbol "``SELF``" is a specific symbol of the EXTEND
   syntax: it does not correspond to a token pattern and is represented
   differently. A token constructor name must not belong to the specific
   symbols: SELF, NEXT, LIST0, LIST1, OPT and FLAG.

   .. rubric:: The lexer record
      :name: the-lexer-record

   The type of the parameter of the function "``Grammar.gcreate``" is
   "``lexer``", defined in the module "``Plexing``". It is a record type
   with the following fields:

   .. rubric:: ``tok_func``
      :name: tok_func

   It is the lexer itself. Its type is:

   ::

        Stream.t char -> (Stream.t (string * string) * location_function);

   The lexer takes a character stream as parameter and return a couple
   of containing: a token stream (the tokens being represented by a
   couple of strings), and a location function.

   The location function is a function taking, as parameter, a integer
   corresponding to a token number in the stream (starting from zero),
   and returning the location of this token in the source. This is
   important to get good locations in the semantic actions of the
   grammar rules.

   Notice that, despite the lexer taking a character stream as
   parameter, it is not mandatory to use the stream parsers technology
   to write the lexer. What is important is that it does the job.

   .. rubric:: ``tok_using``
      :name: tok_using

   Is a function of type:

   ::

        pattern -> unit

   The parameter of this function is the representation of a token
   symbol or a keyword symbol in grammar rules. See the section about
   token patterns.

   This function is called for each token symbol and each keyword
   encountered in the grammar rules of the EXTEND statement. Its goal is
   to allow the lexer to check that the tokens and keywords do respect
   the lexer rules. It checks that the tokens exist and are not
   mispelled. It can be also used to enter the keywords in the lexer
   keyword tables.

   Setting it as the function that does nothing is possible, but the
   check of correctness of tokens is not done.

   In case or error, the function must raise the exception
   "``Plexing.Error``" with an error message as parameter.

   .. rubric:: ``tok_removing``
      :name: tok_removing

   Is a function of type:

   ::

        pattern -> unit

   It is possibly called by the DELETE_RULE statement for tokens and
   keywords no longer used in the grammar. The grammar system maintains
   a number of usages of all tokens and keywords and calls this function
   only when this number reaches zero. This can be interesting for
   keywords: the lexer can remove them from its tables.

   .. rubric:: ``tok_match``
      :name: tok_match

   Is a function of type:

   ::

        pattern -> ((string * string) -> unit)

   The function tells how a token of the input stream is matched against
   a token pattern. Both are represented by a couple of strings.

   This function takes a token pattern as parameter and return a
   function matching a token, returning the matched string or raising
   the exception "``Stream.Failure``" if the token does not match.

   Notice that, for efficiency, it is necessary to write this function
   as a match of token patterns returning, for each case, the function
   which matches the token, *not* a function matching the token pattern
   and the token together and returning a string for each case.

   An acceptable function is provided in the module "``Plexing``" and is
   named "default_match". Its code looks like this:

   ::

        value default_match =
          fun
          [ (p_con, "") ->
              fun (con, prm) -> if con = p_con then prm else raise Stream.Failure
          | (p_con, p_prm) ->
              fun (con, prm) ->
                if con = p_con && prm = p_prm then prm else raise Stream.Failure ]
        ;

   .. rubric:: ``tok_text``
      :name: tok_text

   Is a function of type:

   ::

        pattern -> string

   Designed for error messages, it takes a token pattern as parameter
   and returns the string giving its name.

   It is possible to use the predefined function "``lexer_text``" of the
   Plexing module. This function just returns the name of the token
   pattern constructor and its parameter if any.

   For example, with this default function, the token symbol IDENT would
   be written as IDENT in error message (e.g. "IDENT expected"). The
   "text" function may decide to print it differently, e.g., as
   "identifier".

   .. rubric:: ``tok_comm``
      :name: tok_comm

   Is a mutable field of type:

   ::

        option (list location)

   It asks the lexer (the lexer function should do it) to record the
   locations of the comments in the program. Setting this field to
   "None" indicates that the lexer must not record them. Setting it to
   "Some []" indicated that the lexer must put the comments location
   list in the field, which is mutable.

   .. rubric:: Minimalist version
      :name: minimalist-version

   If a lexer have been written, named "``lexer``", here is the
   minimalist version of the value suitable as parameter to
   "``Grammar.gcreate``":

   ::

        {Plexing.tok_func = lexer;
         Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
         Plexing.tok_match = Plexing.default_match;
         Plexing.tok_text = Plexing.lexer_text;
         Plexing.tok_comm = None}

   .. rubric:: Functorial interface
      :name: functorial-interface

   The normal interface for grammars described in the previous sections
   has two drawbacks:

   -  First, the type of tokens of the lexers must be
      "``(string *       string)``"
   -  Second, since the entry type has no parameter to specify the
      grammar it is bound to, there is no static check that entries are
      compatible, i.e. belong to the same grammar. The check is done at
      run time.

   The functorial interface resolve these two problems. The functor
   takes a module as parameter where the token type has to be defined,
   together with the lexer returning streams of tokens of this type. The
   resulting module define entries compatible the ones to the other, and
   this is controlled by the OCaml type checker.

   The syntax extension must be done with the statement GEXTEND, instead
   of EXTEND, and deletion by GDELETE_RULE instead of DELETE_RULE.

   .. rubric:: The lexer type
      :name: the-lexer-type

   In the section about the interface with the lexer, we presented the
   "``Plexing.lexer``" type as a record without type parameter.
   Actually, this type is defined as:

   ::

        type lexer 'te =
          { tok_func : lexer_func 'te;
            tok_using : pattern -> unit;
            tok_removing : pattern -> unit;
            tok_match : pattern -> 'te -> string;
            tok_text : pattern -> string;
            tok_comm : mutable option (list location) }
        ;

   where the type parameter is the type of the token, which can be any
   type, different from "``(string * string)``", providing the lexer
   function (``tok_func``) returns a stream of this token type and the
   match function (``tok_match``) indicates how to match values of this
   token type against the token patterns (which remain defined as
   "``(string * string)``").

   Here is an example of an user token type and the associated match
   function:

   ::

        type mytoken =
          [ Ident of string
          | Int of int
          | Comma | Equal
          | Keyw of string  ]
        ;

        value mymatch =
          fun
          [ ("IDENT", "") ->
              fun [ Ident s -> s | _ -> raise Stream.Failure ]
          | ("INT", "") ->
              fun [ Int i -> string_of_int i | _ -> raise Stream.Failure ]
          | ("", ",") ->
              fun [ Comma -> "" | _ -> raise Stream.Failure ]
          | ("", "=") ->
              fun [ Equal -> "" | _ -> raise Stream.Failure ]
          | ("", s) ->
              fun
              [ Keyw k -> if k = s then "" else raise Stream.Failure
              | _ -> raise Stream.Failure ]
          | _ -> raise (Plexing.Error "bad token in match function") ]
        ;

   .. rubric:: The functor parameter
      :name: the-functor-parameter

   The type of the functor parameter is defined as:

   ::

        module type GLexerType =
          sig
            type te = 'x;
            value lexer : Plexing.lexer te;
          end;

   The token type must be specified (type "``te``") and the lexer also,
   with the interface for lexers, of the lexer type defined above, the
   record fields being described in the section "interface with the
   lexer", but with a general token type.

   .. rubric:: The resulting grammar module
      :name: the-resulting-grammar-module

   Once a module of type "``GLexerType``" has been built (previous
   section), it is possible to create a grammar module by applying the
   functor "``Grammar.GMake``". For example:

   ::

        module MyGram = Grammar.GMake MyLexer;

   Notice that the function "``Entry.parse``" of this resulting module
   does not take a character stream as parameter, but a value of type
   "``parsable``". This function is equivalent to the function
   "``parse_parsable``" of the non functorial interface. In short, the
   parsing of some character stream "``cs``" by some entry "``e``" of
   the example grammar above, must be done by:

   ::

        MyGram.Entry.parse e (MyGram.parsable cs)

   instead of:

   ::

        MyGram.Entry.parse e cs

   .. rubric:: GEXTEND and GDELETE_RULE
      :name: gextend-and-gdelete_rule

   The "``GEXTEND``" and "``GDELETE_RULE``" statements are also added in
   the expressions of the OCaml language when the syntax extension kit
   "``pa_extend.cmo``" is loaded. They must be used for grammars defined
   with the functorial interface. Their syntax is:

   ::

                 expression ::= gextend
                              | gdelete-rule
               gdelete-rule ::= "GDELETE_RULE" gdelete-rule-body "END"
                    gextend ::= "GEXTEND" gextend-body "END"
               gextend-body ::= grammar-module-name extend-body
          gdelete-rule-body ::= grammar-module-name delete-rule-body
        grammar-module-name ::= qualid

   See the syntax of the EXTEND statement for the meaning of the syntax
   entries not defined above.

   .. rubric:: An example: arithmetic calculator
      :name: an-example-arithmetic-calculator

   Here is a small calculator of expressions. They are given as
   parameters of the command.

   File "calc.ml":

   ::

        #load "pa_extend.cmo";

        value g = Grammar.gcreate (Plexer.gmake ());
        value e = Grammar.Entry.create g "expression";

        EXTEND
          e:
            [ [ x = e; "+"; y = e -> x + y
              | x = e; "-"; y = e -> x - y ]
            | [ x = e; "*"; y = e -> x * y
              | x = e; "/"; y = e -> x / y ]
            | [ x = INT -> int_of_string x
              | "("; x = e; ")" -> x ] ]
          ;
        END;

        open Printf;

        for i = 1 to Array.length Sys.argv - 1 do {
          let r = Grammar.Entry.parse e (Stream.of_string Sys.argv.(i)) in
          printf "%s = %d\n" Sys.argv.(i) r;
          flush stdout;
        };

   The link needs the library "gramlib.cma" provided with Camlp5:

   ::

        ocamlc -pp camlp5r -I +camlp5 gramlib.cma test/calc.ml -o calc

   Examples:

   ::

        $ ./calc '239*4649'
        239*4649 = 1111111
        $ ./calc '(47+2)/3'
        (47+2)/3 = 16

   .. container:: trailer
