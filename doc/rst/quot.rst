Quotations
==========

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Quotations
      :name: quotations
      :class: top

   Quotations are a syntax extension in Camlp5 to build expressions and
   patterns in any syntax independant from the one of OCaml. Quotations
   are *expanded*, i.e. transformed, at parse time to produce normal
   syntax trees, like the rest of the program. Quotations *expanders*
   are normal OCaml functions writable by any programmer.

   The aim of quotations is to use concrete syntax for manipulating
   abstract values. That makes programs easier to write, read, modify,
   and understand. The drawback is that quotations are linguistically
   isolated from the rest of the program, in opposition to `syntax
   extensions <syntext.html>`__, which are included in the language.

   .. container::
      :name: tableofcontents

   .. rubric:: Introduction
      :name: introduction

   A quotation is syntactically enclosed by specific quotes formed by
   less (``<``) and greater (``>``) signs. Namely:

   -  starting with either "``<<``" or "``<:ident<``" where "``ident``"
      is the quotation name,
   -  ending with "``>>``"

   Examples:

   ::

        << \x.x x >>
        <:foo< hello, world >>
        <:bar< @#$%;* >>

   The text between these particular parentheses can be any text. It may
   contain enclosing quotations and the characters "``<``", "``>``" and
   "``\``" can be escaped by "``\``". Notice that possible double-quote,
   parentheses, OCaml comments do not necessarily have to balanced
   inside them.

   As far as the lexer is concerned, a quotation is just a kind of
   string.

   .. rubric:: Quotation expander
      :name: quotation-expander

   Quotations are treated at parse time. Each quotation name is
   associated with a *quotation expander*, a function transforming the
   content of the quotation into a syntax tree. There are actually two
   expanding functions, depending on whether the quotation is in the
   context of an expression or if it is in the context of a pattern.

   If a quotation has no associated quotation expander, a parsing error
   is displayed and the compilation fails.

   The quotation expander, or, rather, expanders, are functions taking
   the quotation string as parameter and returning a syntax tree. There
   is no constraint about which parsing technology is used. It can be
   `stream parsers <parsers.html>`__, `extensible
   grammars <grammars.html>`__, string scanning, ocamllex and yacc, any.

   To build syntax trees, Camlp5 provides a way to easily build them see
   the `chapter <ml_ast.html>`__ about them: it is possible to build
   abstract syntax through concrete syntax using, precisely...
   quotations.

   .. rubric:: Defining a quotation
      :name: defining-a-quotation

   .. rubric:: By syntax tree
      :name: by-syntax-tree

   To define a quotation, it is necessary to program the quotation
   expanders and to, finally, end the source code with a call to:

   ::

        Quotation.add name (Quotation.ExAst (f_expr, f_patt));

   where "``name``" is the name of the quotation, and "``f_expr``" and
   "``f_patt``" the respective quotations expanders for expressions and
   patterns.

   After compilation of the source file (without linking, i.e. using
   option "-c" of the OCaml compiler), an object file is created (ending
   with ".cmo"), which can be used as syntax extension *kit* of Camlp5.

   .. rubric:: By string
      :name: by-string

   There is another way to program the expander: a single function which
   returns, not a syntax tree, but a string which is parsed, afterwards,
   by the system. This function takes a boolean as first parameter
   telling whether the quotation is in position of expression (True) or
   in position of a pattern (False).

   Used that way, the source file must end with:

   ::

        Quotation.add name (Quotation.ExStr f);

   where "``f``" is that quotation expander. The advantage of this
   second approach is that it is simple to understand and use. The
   drawback is that there is no way to specify different source
   locations for different parts of the quotation (what may be important
   in semantic error messages).

   .. rubric:: Default quotation
      :name: default-quotation

   It is possible to use some quotation without its name. Use for that
   the variable "``Quotation.default_quotation``". For example, ending a
   file by:

   ::

        Quotation.add "foo" (Quotation.ExAst (f_expr, f_patt));
        Quotation.default.val := "foo";

   allows to use the quotation "foo" without its name, i.e.:

   ::

        << ... >>

   instead of:

   ::

        <:foo< ... >>

   If several files set the variable "``Quotation.default``", the
   default quotation applies to the last loaded one.

   .. rubric:: Antiquotations
      :name: antiquotations

   A quotation obeys its own rules of lexing and parsing. Its result is
   a syntax tree, of type "``Pcaml.expr``" if the quotation is in the
   context of an expression, or "``Pcaml.patt``" if the quotation is in
   the context of a pattern.

   It can be interesting to insert portions of expressions or patterns
   of the enclosing context in its own quotations. For that, the syntax
   of the quotation must define a syntax for *antiquotations areas*. It
   can be, for example:

   -  A character introducing a variable: in this case the antiquotation
      can just be a variable.
   -  A couple of characters enclosing the antiquotations. For example,
      in the predefined `syntax tree quotations <ml_ast.html>`__, the
      antiquotations are enclosed with dollar ("``$``") signs.

   In quotations, the locations in the resulting syntax tree are all set
   to the location of the quotation itself (if this resulting tree
   contains locations, they are overwritten with this location).
   Consequently, if there are semantic (typing) errors, the OCaml
   compiler will underline the entire quotation.

   But in antiquotations, since they can be inserted in the resulting
   syntax tree, it is interesting to keep their initial quotations. For
   that, the nodes:

   ::

        <:expr< $anti:...$ >>
        <:patt< $anti:...$ >>

   equivalent to:

   ::

        MLast.ExAnt loc ...
        MLast.PaAnt loc ...

   are provided (see `syntax tree quotations <ml_ast.html>`__).

   Let us take an example, without this node, and with this specific
   node.

   Let us consider an elementary quotation system whose contents is just
   an antiquotation. This is just a school example, since the quotations
   brackets are not necessary, in this case. But we are going to see how
   the source code is underlined in errors messages.

   .. rubric:: Example without antiquotation node
      :name: example-without-antiquotation-node

   The code for this quotation is (file "qa.ml"):

   ::

        #load "q_MLast.cmo";
        let expr s = Grammar.Entry.parse Pcaml.expr (Stream.of_string s) in
        Quotation.add "a" (Quotation.ExAst (expr, fun []));

   The quotation expander "``expr``" just takes the string parameter
   (the contents of the quotation), and returns the result of the
   expression parser of the OCaml language.

   Compilation:

   ::

        ocamlc -pp camlp5r -I +camlp5 -c qa.ml

   Let us test it in the toplevel with a voluntary typing error:

   ::

        $ ocaml -I +camlp5 camlp5r.cma
                Objective Caml version ...

                Camlp5 Parsing version ...

        # #load "qa.cmo";
        # let x = "abc" and y = 25 in <:a< x ^ y >>;
        Characters 28-41:
          let x = "abc" and y = 25 in <:a< x ^ y >>;
                                      ^^^^^^^^^^^^^
        This expression has type int but is here used with type string

   We observe that the full quotation is underlined, although it
   concerns only the variable "``y``".

   .. rubric:: Example with antiquotation node
      :name: example-with-antiquotation-node

   Let us consider this second version (file "qb.ml"):

   ::

        #load "q_MLast.cmo";
        let expr s =
          let ast = Grammar.Entry.parse Pcaml.expr (Stream.of_string s) in
          let loc = Ploc.make 1 0 (0, String.length s) in
          <:expr< $anti:ast$ >>
        in
        Quotation.add "b" (Quotation.ExAst (expr, fun []));

   As above, the quotation expander "``expr``" takes the string
   parameter (the contents of the quotation) and applies the expression
   parser of the OCaml language. Its result, instead of being returned
   as it is, is enclosed with the antiquotation node. (The location
   built is the location of the whole string.)

   Compilation:

   ::

        ocamlc -pp camlp5r -I +camlp5 -c qb.ml

   Now the same test gives:

   ::

        $ ocaml -I +camlp5 camlp5r.cma
                Objective Caml version ...

                Camlp5 Parsing version ...

        # #load "qb.cmo";
        # let x = "abc" and y = 25 in <:b< x ^ y >>;
        Characters 37-38:
          let x = "abc" and y = 25 in <:b< x ^ y >>;
                                               ^
        This expression has type int but is here used with type string

   Notice that, now, only the variable "``y``" is underlined.

   .. rubric:: In conclusion
      :name: in-conclusion

   In the resulting tree of the quotation expander:

   -  only portions of this tree, which are sons of the expr and patt
      antiquotation nodes, have the right location they have in the
      quotation (provided the quotation expander gives it the right
      location of the antiquation in the quotation),
   -  the other nodes inherit, as location, the location of the full
      quotation.

   .. rubric:: Locations in quotations and antiquotations
      :name: locations-in-quotations-and-antiquotations

   This section explains in details the problem of locations in
   quotations and antiquotations. It is designed for programmers of
   quotation expanders.

   Locations are the difficult point in quotations and antiquotations.
   If they are not set correctly, error messages may highlight wrong
   parts of the source.

   The locations are controlled:

   -  for syntax errors: by the exception "``Ploc.Exc``", raised by the
      function "``Ploc.raise``",
   -  for typing errors, by the syntax tree nodes
      "``<:expr< $anti:...$ >>``" and "``<:meta< $anti:...$ >>``".

   If the quotation expander never uses them, all syntax and typing
   errors highlight the whole quotation.

   Remark that in `extensible grammars <grammars.html>`__, syntax errors
   are automatically enclosed by the exception "``Ploc.Exc``".
   Therefore, if the quotation is parsed by an extensible grammar entry,
   this exception can be raised.

   In the syntax tree nodes "``<:expr< $anti:...$ >>``" and
   "``<:meta< $anti:...$ >>``", the location is indicated by the
   implicit variable named "``loc``". Their usage is therefore something
   like:

   ::

        let loc = ...computation of the location... in
        <:expr< $anti:...$ >>

   .. rubric:: In the quotation
      :name: in-the-quotation

   All locations must be computed *relatively to the quotation string*.
   The quotation string is the string between "``<<``" or "``<:name<``"
   and "``>>``" (excluded), the first character of this string being at
   location zero.

   The quotation system automatically shifts all locations with the
   location of the quotation: the programmer of the quotation expander
   does not therefore need to care about where the quotation appears in
   the source.

   .. rubric:: In antiquotations
      :name: in-antiquotations

   In antiquotations, it is important to control how the antiquotation
   string is parsed. For example, if the function parsing the
   antiquotation string raises "``Ploc.Exc``", the location of this
   exception must be shifted with the location of the antiquotation in
   the quotation.

   For example, let us suppose that the source contains:

   ::

        << abc^ijk^(xyz) >>

   where the antiquotation is specified between the caret ("``^``")
   characters. The antiquotation string is "``ijk``". It can be built in
   the quotation expander by:

   ::

        <:expr< ijk >>

   If used just like this, without the "``<:expr< $anti:x$ >>``", in
   case of typing error (for example if the variable "``ijk``" is
   unbound), the OCaml error message will be:

   ::

        << abc^ijk^(xyz) >>
        ^^^^^^^^^^^^^^^^^^^
        Unbound value ijk

   To put a location to "``ijk``", since its location in the quotation
   is "``(5, 8)``" (the "``i``" being the 5th characater of the
   quotation string, starting at zero), the quotation expander can build
   it like this:

   ::

        let e = <:expr< ijk >> in
        let loc = Ploc.make_unlined (5, 8) in
        <:expr< $anti:e$ >>

   In this case, the possible typing error message will be:

   ::

        << abc^ijk^(xyz) >>
               ^^^
        Unbound value ijk

   This case is simple, since the antiquotation is just an identifier,
   and there is no parser computing it.

   If the antiquotation has to be parsed, for example if it is a
   complicated expression, there are two points to care about:

   First, the syntax error messages. If the parser of the antiquotation
   raises "``Ploc.Exc``", its location is relative to the antiquotation.
   It must therefore be shifted to correspond to a location in the
   quotation. If "``f``" is the parsing function and "``sh``" the shift
   of the *antiquotation* in the *quotation* (whose value is "``5``" in
   the example), the code must be something like:

   ::

        try f () with
        [ Ploc.Exc loc exc -> Ploc.raise (Ploc.shift sh loc) exc ]

   Second, the typing error messages. Here, the above code with
   "``<:expr< $anti:e$ >>``" can apply to the resulting tree.

   The complete code, taking the possible syntax error messages and the
   possible typing error messages into account, can be (where "``len``"
   is the antiquotation length):

   ::

        let e =
          try f () with
          [ Ploc.Exc loc exc -> Ploc.raise (Ploc.shift sh loc) exc ]
        in
        let loc = Ploc.make_unlined (sh, sh + len) in
        <:expr< $anti:e$ >>

   .. rubric:: Located errors
      :name: located-errors

   If the quotation expander raises an exception, by default, the whole
   quotation is underlined:

   ::

        $ cat foo.ml
        #load "q_MLast.cmo";
        let expr s = raise (Failure "hello") in
        Quotation.add "a" (Quotation.ExAst (expr, fun []));

        $ ocaml -I +camlp5 camlp5r.cma
                Objective Caml version ...

                Camlp5 Parsing version ...

        # #use "foo.ml";
        - : unit = ()
        # <:a< good morning >>;
        Toplevel input:
        # <:a< good morning >>;
          ^^^^^^^^^^^^^^^^^^^^
        While expanding quotation "a":
        Failure: hello

   To specify a location of the exception, use the function
   "``Ploc.raise``" instead of "``raise``". In this example, let us
   suppose that we want only the characters 5 to 7 are underlined. This
   can be done like this:

   ::

        $ cat foo.ml
        #load "q_MLast.cmo";
        let expr s = Ploc.raise (Ploc.make 1 0 (5, 7)) (Failure "hello") in
        Quotation.add "a" (Quotation.ExAst (expr, fun []));

        $ ledit ocaml -I +camlp5 camlp5r.cma
                Objective Caml version ...

                Camlp5 Parsing version ...

        # #use "foo.ml";
        - : unit = ()
        # <:a< good morning >>;
        Toplevel input:
        # <:a< good morning >>;
                   ^^
        While expanding quotation "a":
        Failure: hello

   .. rubric:: The Quotation module
      :name: the-quotation-module

   ::

      type expander =
        [ ExStr of bool -> string -> string
        | ExAst of (string -> MLast.expr * string -> MLast.patt) ]
      ;

   Is the type for quotation expander kinds:

   -  "``Quotation.ExStr exp``" corresponds to an expander "``exp``"
      returning a string which is parsed by the system to create a
      syntax tree. Its boolean parameter tells whether the quotation is
      in position of an expression (True) or in position of a pattern
      (False). Quotations expanders created this way may work for some
      particular OCaml syntax, and not for another one (e.g. may work
      when used with revised syntax and not when used with normal
      syntax, and conversely).
   -  "``Quotation.ExAst (expr_exp, patt_exp)``" corresponds to
      expanders returning syntax trees, therefore not necessitating to
      be parsed afterwards. The function "``expr_exp``" is called when
      the quotation is in position of an expression, and "``patt_exp``"
      when the quotation is in position of a pattern. Quotation
      expanders created this way are independent from the enclosing
      syntax.

   ``value add : string -> expander -> unit;``
      "``Quotation.add name exp``" adds the quotation "``name``"
      associated with the expander "``exp``".

   ``value find : string -> expander;``
      "``Quotation.find name``" returns the quotation expander of the
      given name.

   ``value default : ref string;``
      The name of the default quotation : it is possible to use this
      quotation between "``<<``" and "``>>``" without having to specify
      its name.

   ``value translate : ref (string -> string);``
      Function translating quotation names; default = identity. Used in
      the predefined quotation "``q_phony.cmo``". See below.

   Some other useful functions for quotations are defined in the module
   "``Pcaml``". See the chapter "`The Pcaml module <pcaml.html>`__",
   section "Quotation management".

   .. rubric:: Predefined quotations
      :name: predefined-quotations

   .. rubric:: q_MLast.cmo
      :name: q_mlast.cmo

   This extension kit add quotations of OCaml syntax tree, allowing to
   use concrete syntax to represent abstract syntax. See the chapter
   `Syntax tree <ml_ast.html>`__.

   .. rubric:: q_ast.cmo
      :name: q_ast.cmo

   As with the previous quotation, this extension kit add quotations of
   OCaml syntax tree, but in the current user syntax with all
   extensions, the previous one being restricted to revised syntax
   without extension. See the chapters `Syntax tree <ml_ast.html>`__ and
   `Syntax tree quotations in user syntax <q_ast.html>`__.

   .. rubric:: q_phony.cmo
      :name: q_phony.cmo

   This extension kit is designed for pretty printing and must be loaded
   after a language pretty printing kit (in normal or in revised
   syntax). It prevents the expansions of quotations, transforming them
   into variables. The pretty printing then keeps the initial (source)
   form.

   The `macros <macros.html>`__ (extension "``pa_macro.cmo``") are also
   displayed in their initial form, instead of expanded.

   .. rubric:: A full example: lambda terms
      :name: a-full-example-lambda-terms

   This example allows to represent lambda terms by a concrete syntax
   and to be able to combine them using antiquotations.

   A lambda term is defined like this:

   ::

        type term =
          [ Lam of string and term
          | App of term and term
          | Var of string ]
        ;

   Examples:

   ::

        value fst = Lam "x" (Lam "y" (Var "x"));
        value snd = Lam "x" (Lam "y" (Var "y"));
        value delta = Lam "x" (App (Var "x") (Var "x"));
        value omega = App delta delta;
        value comb_s =
          Lam "x"
            (Lamb "y"
               (Lamb "z"
                  (App (App (Var "x") (Var "y")) (App (Var "x") (Var "z")))));

   Since combinations of lambda term may be complicated, The idea is to
   represent them by quotations in concrete syntax. We want to be able
   to write the examples above like this:

   ::

        value fst = << \x.\y.x >>;
        value snd = << \x.\y.y >>;
        value delta = << \x.x x >>
        value omega = << ^delta ^delta >>;
        value comb_s = << \x.\y.\z.(x y)(x z) >>;

   which is a classic representation of lambda terms.

   Notice, in the definition of "``omega``", the use of the caret
   ("``^``") sign to specify antiquotations. Notice also the simplicity
   of the representation of the expression defining "``comb_s``".

   Here is the code of the quotation expander, term.ml. The expander
   uses the `extensible grammars <grammars.html>`__. It has its own
   lexer (using the `stream lexers <lexers.html>`__) because the lexer
   of OCaml programs ("``Plexer.gmake ()``"), cannot recognize the
   backslashes alone.

   .. rubric:: Lexer
      :name: lexer

   ::

        (* lexer *)

        #load "pa_lexer.cmo";

        value rec ident =
          lexer
          [ [ 'a'-'z' | 'A'-'Z' | '0'-'9' | '-' | '_' | '\128'-'\255' ]
            ident!
          | ]
        ;

        value empty _ = parser [: _ = Stream.empty :] -> [];

        value rec next_tok =
          lexer
          [ "\\" -> ("BSLASH", "")
          | "^" -> ("CARET", "")
          | 'a'-'z' ident! -> ("IDENT", $buf)
          | "(" -> ("", "(")
          | ")" -> ("", ")")
          | "." -> ("", ".")
          | empty -> ("EOS", "")
          | -> raise (Stream.Error "lexing error: bad character") ]
        ;

        value rec skip_spaces =
          lexer
          [ " "/ skip_spaces!
          | "\n"/ skip_spaces!
          | "\r"/ skip_spaces! | ]
        ;

        value record_loc loct i (bp, ep) = do {
          if i >= Array.length loct.val then do {
            let newt =
              Array.init (2 * Array.length loct.val + 1)
                (fun i ->
                   if i < Array.length loct.val then loct.val.(i)
                   else Ploc.dummy)
            in
            loct.val := newt;
          }
          else ();
          loct.val.(i) := Ploc.make_unlined (bp, ep)
        };

        value lex_func cs =
          let loct = ref [| |] in
          let ts =
            Stream.from
              (fun i -> do {
                 ignore (skip_spaces $empty cs : Plexing.Lexbuf.t);
                 let bp = Stream.count cs in
                 let r = next_tok $empty cs in
                 let ep = Stream.count cs in
                 record_loc loct i (bp, ep);
                 Some r
               })
          in
          let locf i =
            if i < Array.length loct.val then loct.val.(i) else Ploc.dummy
          in
          (ts, locf)
        ;

        value lam_lex =
          {Plexing.tok_func = lex_func;
           Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
           Plexing.tok_match = Plexing.default_match;
           Plexing.tok_text = Plexing.lexer_text;
           Plexing.tok_comm = None}
        ;

   .. rubric:: Parser
      :name: parser

   ::

        (* parser *)

        #load "pa_extend.cmo";
        #load "q_MLast.cmo";

        value g = Grammar.gcreate lam_lex;
        value expr_term_eos = Grammar.Entry.create g "term";
        value patt_term_eos = Grammar.Entry.create g "term";

        EXTEND
          GLOBAL: expr_term_eos patt_term_eos;
          expr_term_eos:
            [ [ x = expr_term; EOS -> x ] ]
          ;
          expr_term:
            [ [ BSLASH; i = IDENT; "."; t = SELF -> <:expr< Lam $str:i$ $t$ >> ]
            | [ x = SELF; y = SELF -> <:expr< App $x$ $y$ >> ]
            | [ i = IDENT -> <:expr< Var $str:i$ >>
              | CARET; r = expr_antiquot -> r
              | "("; t = SELF; ")" -> t ] ]
          ;
          expr_antiquot:
            [ [ i = IDENT ->
                 let r =
                   let loc = Ploc.make_unlined (0, String.length i) in
                   <:expr< $lid:i$ >>
                 in
                 <:expr< $anti:r$ >> ] ]
          ;
          patt_term_eos:
            [ [ x = patt_term; EOS -> x ] ]
          ;
          patt_term:
            [ [ BSLASH; i = IDENT; "."; t = SELF -> <:patt< Lam $str:i$ $t$ >> ]
            | [ x = SELF; y = SELF -> <:patt< App $x$ $y$ >> ]
            | [ i = IDENT -> <:patt< Var $str:i$ >>
              | CARET; r = patt_antiquot -> r
              | "("; t = SELF; ")" -> t ] ]
          ;
          patt_antiquot:
            [ [ i = IDENT ->
                 let r =
                   let loc = Ploc.make_unlined (0, String.length i) in
                   <:patt< $lid:i$ >>
                 in
                 <:patt< $anti:r$ >> ] ]
          ;
        END;

        value expand_expr s =
          Grammar.Entry.parse expr_term_eos (Stream.of_string s)
        ;
        value expand_patt s =
          Grammar.Entry.parse patt_term_eos (Stream.of_string s)
        ;

        Quotation.add "term" (Quotation.ExAst (expand_expr, expand_patt));
        Quotation.default.val := "term";

   .. rubric:: Compilation and test
      :name: compilation-and-test

   Compilation:

   ::

        ocamlc -pp camlp5r -I +camlp5 -c term.ml

   Example, in the toplevel, including a semantic error, correctly
   underlined, thanks to the antiquotation nodes:

   ::

        $ ocaml -I +camlp5 camlp5r.cma
                Objective Caml version ...

                Camlp5 Parsing version ...

        # #load "term.cmo";
        # type term =
           [ Lam of string and term
           | App of term and term
           |   Var of string ]
          ;
        type term =
          [ Lam of string and term | App of term and term | Var of string ]
        # value comb_s = << \x.\y.\z.(x y)(x z) >>;
        value comb_s : term =
          Lam "x"
           (Lam "y"
             (Lam "z" (App (App (Var "x") (Var "y")) (App (Var "x") (Var "z")))))
        # value omega = << ^delta ^delta >>;
        Characters 18-23:
          value omega = << ^delta ^delta >>;
                            ^^^^^
        Unbound value delta
        # value delta = << \x.x x >>;
        value delta : term = Lam "x" (App (Var "x") (Var "x"))
        # value omega = << ^delta ^delta >>;
        value omega : term =
          App (Lam "x" (App (Var "x") (Var "x")))
            (Lam "x" (App (Var "x") (Var "x")))

   .. container:: trailer
