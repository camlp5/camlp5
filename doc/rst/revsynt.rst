.. _revised_syntax:

The revised syntax
===================


.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: The revised syntax
      :name: the-revised-syntax
      :class: top

   The revised syntax is an alternative syntax of OCaml. It is close to
   the normal syntax. We present here only the differences between the
   two syntaxes.

   Notice that there is a simple way to know how the normal syntax is
   written in revised syntax: write the code in a file "foo.ml" in
   normal syntax and type, in a shell:

   ::

        camlp5o pr_r.cmo pr_rp.cmo foo.ml

   And, conversely, how a file "bar.ml" written in revised syntax is
   displayed in normal syntax:

   ::

        camlp5r pr_o.cmo pr_op.cmo bar.ml

   Even simpler, without creating a file:

   ::

        camlp5o pr_r.cmo pr_op.cmo -impl -
        ... type in normal syntax ...
        ... type control-D ...
        camlp5r pr_o.cmo pr_rp.cmo -impl -
        ... type in revised syntax ...
        ... type control-D ...

   .. container::
      :name: tableofcontents

   .. rubric:: Lexing
      :name: lexing

   -  The character quote (``'``) can be written without backslash:
      ======== =======
      OCaml    Revised
      ======== =======
      ``'\''`` ``'''``
      ======== =======

   .. rubric:: Modules, Structure and Signature items
      :name: modules-structure-and-signature-items

   -  Structure and signature items always end with a single semicolon
      which is required.
   -  In structures, the declaration of a value is introduced by the
      keyword "value", instead of "let":
      ========================= ========================
      OCaml                     Revised
      ========================= ========================
      ``let x = 42;;``          ``value x = 42;``
      ``let x = 42 in x + 7;;`` ``let x = 42 in x + 7;``
      ========================= ========================

   -  In signatures, the declaration of a value is also introduced by
      the keyword "value", instead of "val":
      ================= ==================
      OCaml             Revised
      ================= ==================
      ``val x : int;;`` ``value x : int;``
      ================= ==================

   -  In signatures, abstract module types are represented by a quote
      and an (any) identifier:
      ==================== ========================
      OCaml                Revised
      ==================== ========================
      ``module type MT;;`` ``module type MT = 'a;``
      ==================== ========================

   -  Functor application uses currying. Parentheses are not required
      for the parameters:
      =================================== ==============================
      OCaml                               Revised
      =================================== ==============================
      ``type t = Set.Make(M).t;;``        ``type t = (Set.Make M).t;``
      ``module M = Mod.Make (M1) (M2);;`` ``module M = Mod.Make M1 M2;``
      =================================== ==============================

   -  It is possible to group several declarations together either in an
      interface or in an implementation by enclosing them between
      "declare" and "end" (this is useful when using syntax extensions
      to generate several declarations from one). Example in an
      interface:

      ::

           declare
             type foo = [ Foo of int | Bar ];
             value f : foo -> int;
           end;

   .. rubric:: Expressions and Patterns
      :name: expressions-and-patterns

   .. rubric:: Imperative constructions
      :name: imperative-constructions

   -  The sequence is introduced by the keyword "do" followed by "{" and
      terminated by "}"; it is possible to put a semicolon after the
      last expression:
      ================== =========================
      OCaml              Revised
      ================== =========================
      ``e1; e2; e3; e4`` ``do { e1; e2; e3; e4 }``
      ================== =========================

   -  The "do" after the "while" loop and the "for" loop are followed by
      a "{" and the loop end with "}"; it is possible to put a semicolon
      after the last expression:
      ========================= =========================
      OCaml                     Revised
      ========================= =========================
      ``while e1 do``           ``while e1 do {``
      ``  e1; e2; e3``          ``  e1; e2; e3``
      ``done``                  ``}``
      ````                      ````
      ``for i = e1 to e2 do  `` ``for i = e1 to e2 do {``
      ``  e1; e2; e3``          ``  e1; e2; e3``
      ``done``                  ``}``
      ========================= =========================

   .. rubric:: Tuples and Lists
      :name: tuples-and-lists

   -  Parentheses are required in tuples:
      ===================== =======================
      OCaml                 Revised
      ===================== =======================
      ``1, "hello", World`` ``(1, "hello", World)``
      ===================== =======================

   -  Lists are always enclosed with brackets. A list is a left bracket,
      followed by a list of elements separated with semicolons,
      optionally followed by colon-colon and an element, and ended by a
      right bracket. Warning: the colon-colon is not an infix but is
      just part of the syntactic construction.
      ==================== ==================
      OCaml                Revised
      ==================== ==================
      ``x :: y``           ``[x :: y]``
      ``[x; y; z]``        ``[x; y; z]``
      ``x :: y :: z :: t`` ``[x; y; z :: t]``
      ==================== ==================

   .. rubric:: Records
      :name: records

   -  In record update, parentheses are required around the initial
      expression:
      ====================== ========================
      OCaml                  Revised
      ====================== ========================
      ``{e with field = a}`` ``{(e) with field = a}``
      ====================== ========================

   -  It is allowable to use function binding syntax in record field
      definitions:
      ======================== =================
      OCaml                    Revised
      ======================== =================
      ``{field = fun a -> e}`` ``{field a = e}``
      ======================== =================

   .. rubric:: Irrefutable patterns
      :name: irrefutable-patterns

   An *irrefutable pattern* is a pattern which is syntactically visible
   and never fails. They are used in some syntactic constructions. It is
   either:

   -  A variable,
   -  The wildcard "_",
   -  The constructor "()",
   -  A tuple with irrefutable patterns,
   -  A record with irrefutable patterns,
   -  A type constraint with an irrefutable pattern.

   Notice that this definition is only syntactic: a constructor
   belonging to a type having only one constructor is not considered as
   an irrefutable pattern (except "()").

   .. rubric:: Constructions with matching
      :name: constructions-with-matching

   -  The keyword "function" no longer exists. Only "fun" is used.
   -  The pattern matching, in constructions with "fun", "match" and
      "try" is closed with brackets: an open bracket "[" before the
      first case, and a close bracket "]" after the last case:
      ================ ================
      OCaml            Revised
      ================ ================
      ``match e with`` ``match e with``
      ``  p1 -> e1``   ``[ p1 -> e1``
      ``| p2 -> e2``   ``| p2 -> e2 ]``
      ================ ================

      If there is only one case and if the pattern is irrefutable, the
      brackets are not required. These examples work identically in
      OCaml and in revised syntax:
      ========================= =========================
      OCaml                     Revised
      ========================= =========================
      ``fun x -> x``            ``fun x -> x``
      ``fun {foo=(y, _)} -> y`` ``fun {foo=(y, _)} -> y``
      ========================= =========================

   -  It is possible to write the empty function which always raises the
      exception "Match_failure" when a parameter is applied. It is also
      possible to write and empty "match", raising "Match_failure" after
      having evaluated its expression and the empty "try", equivalent to
      its expression without try:

      ::

           fun []
           match e with []
           try e with []

   -  The patterns after "let" and "value" must be irrefutable. The
      following OCaml expression:

      ::

           let f (x::y) = ...

      must be written:

      ::

           let f = fun [ [x::y] -> ...

   -  It is possible to use a construction "where", equivalent to "let",
      but usable only when where is only one binding. The expression:

      ::

           e1 where p = e

      is equivalent to:

      ::

           let p = e in e1

   .. rubric:: Mutables and Assignment
      :name: mutables-and-assignment

   -  The statement "``<-``" is written "``:=``":
      ============ ============
      OCaml        Revised
      ============ ============
      ``x.f <- y`` ``x.f := y``
      ============ ============

   -  The "ref" type is declared as a record type with one field named
      "val", instead of "contents". The operator "!" does not exist any
      more, and references are assigned like the other mutables:
      =============== ======================
      OCaml           Revised
      =============== ======================
      ``x := !x + y`` ``x.val := x.val + y``
      =============== ======================

   .. rubric:: Miscellaneous
      :name: miscellaneous

   -  The "``else``" is required in the "``if``" statement:
      =============== =======================
      OCaml           Revised
      =============== =======================
      ``if a then b`` ``if a then b else ()``
      =============== =======================

   -  The boolean operations "``or``" and "``and``" can only be written
      with "``||``" and "``&&``":
      =============== ===============
      OCaml           Revised
      =============== ===============
      ``a or b & c``  ``a || b && c``
      ``a || b && c`` ``a || b && c``
      =============== ===============

   -  No more "``begin end``" construction. One must use parentheses.
   -  The operators as values are written with an backslash:
      ========= ========
      OCaml     Revised
      ========= ========
      ``(+)``   ``\+``
      ``(mod)`` ``\mod``
      ========= ========

   -  Nested "as" patterns require parenthesis:
      ============================== ===============================
      OCaml                          Revised
      ============================== ===============================
      ``function Some a as b, c ->`` ``fun [ ((Some a as b), c) ->``
      ``  ...``                      ``  ...``
      ============================== ===============================

      But they are not required before the right arrow:
      =========================== ========================
      OCaml                       Revised
      =========================== ========================
      ``function Some a as b ->`` ``fun [ Some a as b ->``
      ``  ...``                   ``  ...``
      =========================== ========================

   -  The operators with special characters are not automatically infix.
      To define infixes, use syntax extensions.

   .. rubric:: Types and Constructors
      :name: types-and-constructors

   -  The type constructors are before their type parameters, which are
      curryfied:
      ============================== ================================
      OCaml                          Revised
      ============================== ================================
      ``int list``                   ``list int``
      ``('a, bool) Hashtbl.t``       ``Hashtbl.t 'a bool``
      ``type 'a foo = 'a list list`` ``type foo 'a = list (list 'a)``
      ============================== ================================

   -  The abstract types are represented by an unbound type variable:
      ================= =====================
      OCaml             Revised
      ================= =====================
      ``type 'a foo;;`` ``type foo 'a = 'b;``
      ``type bar;;``    ``type bar = 'a;``
      ================= =====================

   -  Parentheses are required in tuples of types:
      ============== ================
      OCaml          Revised
      ============== ================
      ``int * bool`` ``(int * bool)``
      ============== ================

   -  In declarations of a concrete type, brackets must enclose the
      constructor declarations:
      ========================= ============================
      OCaml                     Revised
      ========================= ============================
      ``type t = A of i | B;;`` ``type t = [ A of i | B ];``
      ========================= ============================

   -  It is possible to make the empty type, without constructor:

      ::

           type foo = [];

   -  There is a syntax difference between data constructors with
      several parameters and data constructors with one parameter of
      type tuple:
      The declaration of a data constructor with several parameters is
      done by separating the types with "and". In expressions and
      patterns, these constructor parameters must be curryfied:
      =========================== ================================
      OCaml                       Revised
      =========================== ================================
      ``type t = C of t1 * t2;;`` ``type t = [ C of t1 and t2 ];``
      ``C (x, y);;``              ``C x y;``
      =========================== ================================

      The declaration of a data constructor with one parameter of type
      tuple is done by using a tuple type. In expressions and patterns,
      the parameter must not to be curryfied, since it is alone. In that
      case the syntax of constructor parameters is the same between the
      two syntaxes:
      ============================= ================================
      OCaml                         Revised
      ============================= ================================
      ``type t = D of (t1 * t2);;`` ``type t = [ D of (t1 * t2) ];``
      ``D (x, y);;``                ``D (x, y);``
      ============================= ================================

   -  The bool constructors start with an uppercase letter. The
      identifiers "true" and "false" are not keywords:
      ================= =================
      OCaml             Revised
      ================= =================
      ``true && false`` ``True && False``
      ================= =================

   -  In record types, the keyword "mutable" must appear after the
      colon:
      =============================== ==============================
      OCaml                           Revised
      =============================== ==============================
      ``type t = {mutable x : t1};;`` ``type t = {x : mutable t1};``
      =============================== ==============================

   -  Manifest types are with "==":
      =========================== ============================
      OCaml                       Revised
      =========================== ============================
      ``type 'a t = 'a option =`` ``type t 'a = option 'a ==``
      ``    None``                ``  [ None``
      ``  | Some of 'a``          ``  | Some of 'a ]``
      =========================== ============================

   -  Polymorphic types start with "``!``":
      ========================== ============================
      OCaml                      Revised
      ========================== ============================
      ``type t =``               ``type t =``
      ``  { f : 'a . 'a list }`` ``  { f : ! 'a . list 'a }``
      ========================== ============================

   .. rubric:: Streams and Parsers
      :name: streams-and-parsers

   -  The streams and the stream patterns are bracketed with "``[:``"
      and "``:]``" instead of "``[<``" and "``>]``".
   -  The stream component "terminal" is written with a back-quote
      instead of a quote:
      ======================= ==============================
      OCaml                   Revised
      ======================= ==============================
      ``[< '1; '2; s; '3 >]`` :literal:`[: `1; `2; s; `3 :]`
      ======================= ==============================

   -  The cases of parsers are bracketed with "``[``" and "``]``", as
      with "fun", "match" and "try". If there is one case, the brackets
      are not required:
      ========================== ================================
      OCaml                      Revised
      ========================== ================================
      ``parser``                 ``parser``
      ``  [< 'Foo >] -> e``      :literal:`[ [: `Foo :] -> e`
      ``| [< p = f >] -> f;;``   ``| [: p = f :] -> f ];``
      ``parser [< 'x >] -> x;;`` :literal:`parser [: `x :] -> x;`
      ========================== ================================

   -  It is possible to write the empty parser raising the exception
      "Stream.Failure" whatever parameter is applied, and the empty
      stream matching always raising "Stream.Failure":

      ::

           parser []
           match e with parser []

   -  In normal syntax, the error indicator starts with a double
      question mark, in revised syntax with a simple question mark:
      ================================
      ======================================
      OCaml                            Revised
      ================================
      ======================================
      ``parser``                       ``parser``
      ``  [< '1; '2 ?? "error" >] ->`` :literal:`  [: `1; `2 ? "error" :] ->`
      ``    ...``                      ``    ...``
      ================================
      ======================================

   -  In normal syntax, the component optimization starts with "``?!``",
      in revised syntax with "``!``":
      ======================== ==============================
      OCaml                    Revised
      ======================== ==============================
      ``parser``               ``parser``
      ``  [< '1; '2 ?! >] ->`` :literal:`  [: `1; `2 ! :] ->`
      ``    ...``              ``    ...``
      ======================== ==============================

   .. rubric:: Classes and Objects
      :name: classes-and-objects

   -  Object items end with a single semicolon which is required.
   -  Class type parameters follow the class identifier:
      ============================== ==============================
      OCaml                          Revised
      ============================== ==============================
      ``class ['a, 'b] point = ...`` ``class point ['a, 'b] = ...``
      ``class c = [int] color;;``    ``class c = color [int];``
      ============================== ==============================

   -  In the type of class with parameters, the type of the parameters
      are between brackets. Example in signature:
      ============================ =============================
      OCaml                        Revised
      ============================ =============================
      ``class c : int -> point;;`` ``class c : [int] -> point;``
      ============================ =============================

   -  The keywords "virtual" and "private" must be in this order:
      ============================== ==============================
      OCaml                          Revised
      ============================== ==============================
      ``method virtual private m :`` ``method virtual private m :``
      ``  ...``                      ``  ...``
      ``method private virtual m :`` ``method virtual private m :``
      ``  ...``                      ``  ...``
      ============================== ==============================

   -  Object variables are introduced with "value" instead of "val":
      ======================== ===========================
      OCaml                    Revised
      ======================== ===========================
      ``object val x = 3 end`` ``object value x = 3; end``
      ======================== ===========================

   -  Type constraints in objects are introduced with "type" instead of
      "constraint":
      ================================== =============================
      OCaml                              Revised
      ================================== =============================
      ``object constraint 'a = int end`` ``object type 'a = int; end``
      ================================== =============================

   .. rubric:: Labels and Variants
      :name: labels-and-variants

   -  Labels in types must start with "``~``":
      ============================= ===============================
      OCaml                         Revised
      ============================= ===============================
      ``val x : num:int -> bool;;`` ``value x : ~num:int -> bool;``
      ============================= ===============================

   -  Types whose number of variants are fixed start with "``[ =``":
      ==================================
      ====================================
      OCaml                              Revised
      ==================================
      ====================================
      :literal:`type t = [`On | `Off];;` :literal:`type t = [ = `On | `Off];`
      ==================================
      ====================================

   -  The "``[``" and the "``<``" in variant types must not be sticked:
      ======================================
      ======================================
      OCaml                                  Revised
      ======================================
      ======================================
      :literal:`type t = [< `Foo | `Bar ];;` :literal:`type t = [ < `Foo | `Bar ];`
      ======================================
      ======================================

   .. container:: trailer
