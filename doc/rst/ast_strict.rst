
Syntax tree - strict mode
=========================

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Syntax tree - strict mode
      :name: syntax-tree---strict-mode
      :class: top

   This chapter presents the Camlp5 syntax tree when Camlp5 is installed
   in *strict* mode.

   .. container::
      :name: tableofcontents

   .. rubric:: Introduction
      :name: introduction

   This syntax tree is defined in the module "``MLast``" provided by
   Camlp5. Each node corresponds to a syntactic entity of the
   corresponding type.

   For example, the syntax tree of the statement "``if``" can be
   written:

   ::

        MLast.ExIfe loc e1 e2 e3

   where "``loc``" is the location in the source, and "``e1``", "``e2``"
   and "``e3``" are respectively the expression after the "``if``", the
   one after the "``then``" and the one after the "``else``".

   If a program needs to manipulate syntax trees, it can use the nodes
   defined in the module "``MLast``". The programmer must know how the
   concrete syntax is transformed into this abstract syntax.

   A simpler solution is to use one of the quotation kits
   "``q_MLast.cmo``" or "``q_ast.cmo``". Both propose
   `quotations <quot.html>`__ which represent the abstract syntax (the
   nodes of the module "``MLast``") into concrete syntax with
   antiquotations to bind variables inside. The example above can be
   written:

   ::

        <:expr< if $e1$ then $e2$ else $e3$ >>

   This representation is very interesting when one wants to manipulate
   complicated syntax trees. Here is an example taken from the Camlp5
   sources themselves:

   ::

        <:expr<
          match try Some $f$ with [ Stream.Failure -> None ] with
          [ Some $p$ -> $e$
          | _ -> raise (Stream.Error $e2$) ]
        >>

   This example was in a position of a pattern. In abstract syntax, it
   should have been written:

   ::

        MLast.ExMat _
          (MLast.ExTry _ (MLast.ExApp _ (MLast.ExUid _ (Ploc.VaVal "Some")) f)
             (Ploc.VaVal
                [(MLast.PaAcc _ (MLast.PaUid _ (Ploc.VaVal "Stream"))
                   (MLast.PaUid _ (Ploc.VaVal "Failure")),
                  Ploc.VaVal None, MLast.ExUid _ (Ploc.VaVal "None"))]))
          (Ploc.VaVal
             [(MLast.PaApp _ (MLast.PaUid _ (Ploc.VaVal "Some")) p,
               Ploc.VaVal None, e);
              (MLast.PaAny _, Ploc.VaVal None,
               MLast.ExApp _ (MLast.ExLid _ (Ploc.VaVal "raise"))
                 (MLast.ExApp _
                    (MLast.ExAcc _ (MLast.ExUid _ (Ploc.VaVal "Stream"))
                       (MLast.ExUid _ (Ploc.VaVal "Error")))
                    e2))])

   Which is less readable and much more complicated to build and update.

   Instead of thinking of "a syntax tree", the programmer can think of
   "a piece of program".

   .. rubric:: Location
      :name: location

   In all syntax tree nodes, the first parameter is the source location
   of the node.

   .. rubric:: In expressions
      :name: in-expressions

   When a quotation is in the context of an expression, the location
   parameter is "``loc``" in the node and in all its possible sub-nodes.
   Example: if we consider the quotation:

   ::

        <:sig_item< value foo : int -> bool >>

   This quotation, in a context of an expression, is equivalent to:

   ::

        MLast.SgVal loc (Ploc.VaVal "foo")
          (MLast.TyArr loc (MLast.TyLid loc (Ploc.VaVal "int"))
             (MLast.TyLid loc (Ploc.VaVal "bool")));

   The name "``loc``" is predefined. However, it is possible to change
   it, using the argument "``-loc``" of the Camlp5 shell commands.

   Consequently, if there is no variable "``loc``" defined in the
   context of the quotation, or if it is not of the good type, a
   semantic error occur in the OCaml compiler ("Unbound value loc").

   Note that in the `extensible grammars <grammars.html>`__, the
   variable "``loc``" is bound, in all semantic actions, to the location
   of the rule.

   If the created node has no location, the programmer can define a
   variable named "``loc``" equal to "``Ploc.dummy``".

   .. rubric:: In patterns
      :name: in-patterns

   When a quotation is in the context of a pattern, the location
   parameter of all nodes and possible sub-nodes is set to the wildcard
   ("``_``"). The same example above:

   ::

        <:sig_item< value foo : int -> bool >>

   is equivalent, in a pattern, to:

   ::

        MLast.SgVal _ (Ploc.VaVal "foo")
          (MLast.TyArr _ (MLast.TyLid _ (Ploc.VaVal "int"))
             (MLast.TyLid _ (Ploc.VaVal "bool")))

   However, it is possible to generate a binding of the variable
   "``loc``" on the top node by writing a "colon" before the "less" in
   the quotation. The same example:

   ::

        <:sig_item:< value foo : int -> bool >>

   is equivalent to:

   ::

        MLast.SgVal loc (Ploc.VaVal "foo")
          (MLast.TyArr _ (MLast.TyLid _ (Ploc.VaVal "int"))
             (MLast.TyLid _ (Ploc.VaVal "bool")))

   .. rubric:: Antiquotations
      :name: antiquotations

   The expressions or patterns between dollar ($) characters are called
   *antiquotations*. In opposition to quotations which has its own
   syntax rules, the antiquotation is an area in the syntax of the
   enclosing context (expression or pattern). See the chapter about
   `quotations <quot.html>`__.

   If a quotation is in the context of an expression, the antiquotation
   must be an expression. It could be any expression, including function
   calls. Examples:

   ::

        value f e el = <:expr< [$e$ :: $loop False el$] >>;
        value patt_list p pl = <:patt< ( $list:[p::pl]$) >>;

   If a quotation is in the context of an pattern, the antiquotation is
   a pattern. Any pattern is possible, including the wildcard character
   ("``_``"). Examples:

   ::

         fun [ <:expr< $lid:op$ $_$ $_$ >> -> op ]
         match p with [ <:patt< $_$ | $_$ >> -> Some p ]

   .. rubric:: Two kinds of antiquotations
      :name: two-kinds-of-antiquotations

   .. rubric:: Preliminary remark
      :name: preliminary-remark

   In strict mode, we remark that most constructors defined of the
   module "``MLast``" are of type "``Ploc.vala``". This type is defined
   like this:

   ::

        type vala 'a =
          [ VaAnt of string
          | VaVal of 'a ]
        ;

   The type argument is the real type of the node. For example, a value
   of type "``bool``" in transitional mode is frequently represented by
   a value of type "``Ploc.vala bool``".

   The first case of the type "``vala``" corresponds to an antiquotation
   in the concrete syntax. The second case to a normal syntax situation,
   without antiquotation.

   Example: in the "let" statement, the fact that it is "rec" or not is
   represented by a boolean. This boolean is, in the syntax tree,
   encapsulated with the type "``Ploc.vala``". The syntax tree of the
   two following lines:

   ::

        let x = y in z
        let rec x = y in z

   start with, respectively:

   ::

        MLast.ExLet loc (Ploc.VaVal False)
          ... (* and so on *)

   and:

   ::

        MLast.ExLet loc (Ploc.VaVal True)
          ... (* and so on *)

   The case "``Ploc.VaAnt s``" is internally used by the parsers and by
   the quotation kit "``q_ast.cmo``" to record antiquotation strings
   representing the expression or the patterns having this value. For
   example, in this "let" statement:

   ::

        MLast.ExLet loc (Ploc.VaAnt s)
          ... (* and so on *)

   The contents of this "``s``" is internally handled. For information,
   it contains the antiquotation string (kind included) together with
   representation of the location of the antiquotation in the quotation.
   See the next section.

   .. rubric:: Antiquoting
      :name: antiquoting

   To antiquotate the fact that the "let" is with or without rec (a flag
   of type boolean), there are two ways.

   .. rubric:: direct antiquoting
      :name: direct-antiquoting

   The first way, hidding the type "``Ploc.val``", can be written with
   the antiquotation kind "flag":

   ::

        <:expr< let $flag:rf$ x = y in z >>

   This corresponds to the syntax tree:

   ::

        MLast.ExLet loc (Ploc.VaVal rf)
           ... (* and so on *)

   And, therefore, the type of the variable "``rf``" is simply
   "``bool``".

   .. rubric:: general antiquoting
      :name: general-antiquoting

   The second way, introducing variables of type "``Ploc.vala``" can be
   written a kind prefixed by "``_``", namely here "``_flag``":

   ::

        <:expr< let $_flag:rf$ x = y in z >>

   In that case, it corresponds to the syntax tree:

   ::

        MLast.ExLet loc rf
           ... (* and so on *)

   And, therefore, the type of the variable "``rf``" is now
   "``Ploc.vala bool``".

   .. rubric:: Remarks
      :name: remarks

   The first form of antiquotation ensures the compatibility with
   previous versions of Camlp5. The syntax tree is *not* the same, but
   the bound variables keep the same type.

   All antiquotations kinds have these two forms: one with some name
   (e.g. "flag") and one with the same name prefixed by "a" (e.g.
   "aflag").

   .. rubric:: Nodes and Quotations
      :name: nodes-and-quotations

   This section describes all nodes defined in the module "MLast" of
   Camlp5 and how to write them with quotations. Notice that, inside
   quotations, one is not restricted to these elementary cases, but any
   complex value can be used, resulting on possibly complex combined
   nodes.

   The quotation forms are described here in `revised
   syntax <revsynt.html>`__ (like the rest of this document). In
   reality, it depends on which quotation kit is loaded:

   -  If "``q_MLast.cmo``" is used, the revised syntax is mandatory: the
      quotations must be in that syntax without any extension.
   -  If "``q_ast.cmo``" is used, the quotation syntax *must* be in the
      current user syntax with all extensions added to compile the file.

   Last remark: in the following tables, the variables names give
   information of their types. The details can be found in the
   distributed source file "``mLast.mli``".

   -  ``e``, ``e1``, ``e2``, ``e3``: expr
   -  ``p``, ``p1``, ``p2``, ``p3``: patt
   -  ``t``, ``t1``, ``t2``, ``e3``: ctyp
   -  ``s``: string
   -  ``b``: bool
   -  ``me``, ``me1``, ``me2``: module_expr
   -  ``mt``, ``mt1``, ``mt2``: module_type
   -  ``le``: list expr
   -  ``lp``: list patt
   -  ``lt``: list ctyp
   -  ``ls``: list string
   -  ``lse``: list (string \* expr)
   -  ``lpe``: list (patt \* expr)
   -  ``lpp``: list (patt \* patt)
   -  ``lpoee``: list (patt \* option expr \* expr)
   -  ``op``: option patt
   -  ``lcstri``: list class_str_item
   -  ``lcsigi``: list class_sig_item

   .. rubric:: expr
      :name: expr

   Expressions of the language.

   - access
      ``<:expr< $e1$ . $e2$ >>``
      ``MLast.ExAcc loc e1 e2``

   - antiquotation `(1) <#expr_1>`__
      ``<:expr< $anti:e$ >>``
      ``MLast.ExAnt loc e``

   - application
      ``<:expr< $e1$ $e2$ >>``
      ``MLast.ExApp loc e1 e2``

   - array element
      ``<:expr< $e1$ .( $e2$ ) >>``
      ``MLast.ExAre loc e1 e2``

   - array
      ``<:expr< [| $list:le$ |] >>``
      ``MLast.ExArr loc (Ploc.VaVal le)``
      ``<:expr< [| $_list:le$ |] >>``
      ``MLast.ExArr loc le``

   - assert
      ``<:expr< assert $e$ >>``
      ``MLast.ExAsr loc e``

   - assignment
      ``<:expr< $e1$ := $e2$ >>``
      ``MLast.ExAss loc e1 e2``

   - big array element
      ``<:expr< $e$ .{ $list:le$ } >>``
      ``MLast.ExBae loc e (Ploc.VaVal le)``
      ``<:expr< $e$ .{ $_list:le$ } >>``
      ``MLast.ExBae loc e le``

   - character constant
      ``<:expr< $chr:s$ >>``
      ``MLast.ExChr loc (Ploc.VaVal s)``
      ``<:expr< $_chr:s$ >>``
      ``MLast.ExChr loc s``

   - coercion
      ``<:expr< ($e$ :> $t2$) >>``
      ``MLast.ExCoe loc e None t2``
      ``<:expr< ($e$ : $t1$ :> $t2$) >>``
      ``MLast.ExCoe loc e (Some t1) t2``

   - float constant
      ``<:expr< $flo:s$ >>``
      ``MLast.ExFlo loc (Ploc.VaVal s)``
      ``<:expr< $_flo:s$ >>``
      ``MLast.ExFlo loc s``

   - for (increasing)
      ``<:expr< for $lid:s$ = $e1$ to $e2$ do { $list:le$ } >>``
      ``MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal True) (Ploc.VaVal le)``
      ``<:expr< for $lid:s$ = $e1$ to $e2$ do { $_list:le$ } >>``
      ``MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal True) le``

   - for (decreasing)
      ``<:expr< for $lid:s$ = $e1$ downto $e2$ do { $list:le$ } >>``
      ``MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal False) (Ploc.VaVal le)``
      ``<:expr< for $lid:s$ = $e1$ downto $e2$ do { $_list:le$ } >>``
      ``MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal False) le``

   - for
      ``<:expr< for $lid:s$ = $e1$ $to:b$ $e2$ do { $list:le$ } >>``
      ``MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal b) (Ploc.VaVal le)``
      ``<:expr< for $lid:s$ = $e1$ $to:b$ $e2$ do { $_list:le$ } >>``
      ``MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal b) le``
      ``<:expr< for $lid:s$ = $e1$ $_to:b$ $e2$ do { $list:le$ } >>``
      ``MLast.ExFor loc (Ploc.VaVal s) e1 e2 b (Ploc.VaVal le)``
      ``<:expr< for $lid:s$ = $e1$ $_to:b$ $e2$ do { $_list:le$ } >>``
      ``MLast.ExFor loc (Ploc.VaVal s) e1 e2 b le``
      ``<:expr< for $_lid:s$ = $e1$ to $e2$ do { $list:le$ } >>``
      ``MLast.ExFor loc s e1 e2 (Ploc.VaVal True) (Ploc.VaVal le)``
      ``<:expr< for $_lid:s$ = $e1$ to $e2$ do { $_list:le$ } >>``
      ``MLast.ExFor loc s e1 e2 (Ploc.VaVal True) le``
      ``<:expr< for $_lid:s$ = $e1$ downto $e2$ do { $list:le$ } >>``
      ``MLast.ExFor loc s e1 e2 (Ploc.VaVal False) (Ploc.VaVal le)``
      ``<:expr< for $_lid:s$ = $e1$ downto $e2$ do { $_list:le$ } >>``
      ``MLast.ExFor loc s e1 e2 (Ploc.VaVal False) le``
      ``<:expr< for $_lid:s$ = $e1$ $to:b$ $e2$ do { $list:le$ } >>``
      ``MLast.ExFor loc s e1 e2 (Ploc.VaVal b) (Ploc.VaVal le)``
      ``<:expr< for $_lid:s$ = $e1$ $to:b$ $e2$ do { $_list:le$ } >>``
      ``MLast.ExFor loc s e1 e2 (Ploc.VaVal b) le``
      ``<:expr< for $_lid:s$ = $e1$ $_to:b$ $e2$ do { $list:le$ } >>``
      ``MLast.ExFor loc s e1 e2 b (Ploc.VaVal le)``
      ``<:expr< for $_lid:s$ = $e1$ $_to:b$ $e2$ do { $_list:le$ } >>``
      ``MLast.ExFor loc s e1 e2 b le``

   - function
      ``<:expr< fun [ $list:lpee$ ] >>``
      ``MLast.ExFun loc (Ploc.VaVal lpee)``
      ``<:expr< fun [ $_list:lpee$ ] >>``
      ``MLast.ExFun loc lpee``

   - if
      ``<:expr< if $e1$ then $e2$ else $e3$ >>``
      ``MLast.ExIfe loc e1 e2 e3``

   - integer constant
      ``<:expr< $int:s1$ >>``
      ``MLast.ExInt loc (Ploc.VaVal s1) ""``
      ``<:expr< $_int:s1$ >>``
      ``MLast.ExInt loc s1 ""``

   - integer 32 bits
      ``<:expr< $int32:s1$ >>``
      ``MLast.ExInt loc (Ploc.VaVal s1) "l"``
      ``<:expr< $_int32:s1$ >>``
      ``MLast.ExInt loc s1 "l"``

   - integer 64 bits
      ``<:expr< $int64:s1$ >>``
      ``MLast.ExInt loc (Ploc.VaVal s1) "L"``
      ``<:expr< $_int64:s1$ >>``
      ``MLast.ExInt loc s1 "L"``

   - native integer
      ``<:expr< $nativeint:s1$ >>``
      ``MLast.ExInt loc (Ploc.VaVal s1) "n"``
      ``<:expr< $_nativeint:s1$ >>``
      ``MLast.ExInt loc s1 "n"``

   - label
      ``<:expr< ~{$p$} >>``
      ``MLast.ExLab loc p (Ploc.VaVal None)``
      ``<:expr< ~{$p$ = $e$} >>``
      ``MLast.ExLab loc p (Ploc.VaVal (Some e))``
      ``<:expr< ~{$p$ $opt:oe$} >>``
      ``MLast.ExLab loc p (Ploc.VaVal oe)``
      ``<:expr< ~{$p$ $_opt:oe$} >>``
      ``MLast.ExLab loc p oe``

   - lazy
      ``<:expr< lazy $e$ >>``
      ``MLast.ExLaz loc e``

   - let rec
      ``<:expr< let rec $list:lpe$ in $e$ >>``
      ``MLast.ExLet loc (Ploc.VaVal True) (Ploc.VaVal lpe) e``
      ``<:expr< let rec $_list:lpe$ in $e$ >>``
      ``MLast.ExLet loc (Ploc.VaVal True) lpe e``

   - let not rec
      ``<:expr< let $list:lpe$ in $e$ >>``
      ``MLast.ExLet loc (Ploc.VaVal False) (Ploc.VaVal lpe) e``
      ``<:expr< let $_list:lpe$ in $e$ >>``
      ``MLast.ExLet loc (Ploc.VaVal False) lpe e``

   - let
      ``<:expr< let $flag:b$ $list:lpe$ in $e$ >>``
      ``MLast.ExLet loc (Ploc.VaVal b) (Ploc.VaVal lpe) e``
      ``<:expr< let $flag:b$ $_list:lpe$ in $e$ >>``
      ``MLast.ExLet loc (Ploc.VaVal b) lpe e``
      ``<:expr< let $_flag:b$ $list:lpe$ in $e$ >>``
      ``MLast.ExLet loc b (Ploc.VaVal lpe) e``
      ``<:expr< let $_flag:b$ $_list:lpe$ in $e$ >>``
      ``MLast.ExLet loc b lpe e``

   - lowercase identifier
      ``<:expr< $lid:s$ >>``
      ``MLast.ExLid loc (Ploc.VaVal s)``
      ``<:expr< $_lid:s$ >>``
      ``MLast.ExLid loc s``

   - let module
      ``<:expr< let module $uid:s$ = $me$ in $e$ >>``
      ``MLast.ExLmd loc (Ploc.VaVal s) me e``
      ``<:expr< let module $_uid:s$ = $me$ in $e$ >>``
      ``MLast.ExLmd loc s me e``

   - match
      ``<:expr< match $e$ with [ $list:lpee$ ] >>``
      ``MLast.ExMat loc e (Ploc.VaVal lpee)``
      ``<:expr< match $e$ with [ $_list:lpee$ ] >>``
      ``MLast.ExMat loc e lpee``

   - new
      ``<:expr< new $list:ls$ >>``
      ``MLast.ExNew loc (Ploc.VaVal ls)``
      ``<:expr< new $_list:ls$ >>``
      ``MLast.ExNew loc ls``

   - object expression
      ``<:expr< object $list:lcsi$ end >>``
      ``MLast.ExObj loc (Ploc.VaVal None) (Ploc.VaVal lcsi)``
      ``<:expr< object $_list:lcsi$ end >>``
      ``MLast.ExObj loc (Ploc.VaVal None) lcsi``
      ``<:expr< object ($p$) $list:lcsi$ end >>``
      ``MLast.ExObj loc (Ploc.VaVal (Some p)) (Ploc.VaVal lcsi)``
      ``<:expr< object ($p$) $_list:lcsi$ end >>``
      ``MLast.ExObj loc (Ploc.VaVal (Some p)) lcsi``
      ``<:expr< object $opt:op$ $list:lcsi$ end >>``
      ``MLast.ExObj loc (Ploc.VaVal op) (Ploc.VaVal lcsi)``
      ``<:expr< object $opt:op$ $_list:lcsi$ end >>``
      ``MLast.ExObj loc (Ploc.VaVal op) lcsi``
      ``<:expr< object $_opt:op$ $list:lcsi$ end >>``
      ``MLast.ExObj loc op (Ploc.VaVal lcsi)``
      ``<:expr< object $_opt:op$ $_list:lcsi$ end >>``
      ``MLast.ExObj loc op lcsi``

   - option label
      ``<:expr< ?{$p$} >>``
      ``MLast.ExOlb loc p (Ploc.VaVal None)``
      ``<:expr< ?{$p$ = $e$} >>``
      ``MLast.ExOlb loc p (Ploc.VaVal (Some e))``
      ``<:expr< ?{$p$ $opt:oe$} >>``
      ``MLast.ExOlb loc p (Ploc.VaVal oe)``
      ``<:expr< ?{$p$ $_opt:oe$} >>``
      ``MLast.ExOlb loc p oe``

   - override
      ``<:expr< {< $list:lse$ >} >>``
      ``MLast.ExOvr loc (Ploc.VaVal lse)``
      ``<:expr< {< $_list:lse$ >} >>``
      ``MLast.ExOvr loc lse``

   - module packing
      ``<:expr< (module $me$) >>``
      ``MLast.ExPck loc me None``
      ``<:expr< (module $me$ : $mt$) >>``
      ``MLast.ExPck loc me (Some mt)``

   - record
      ``<:expr< {$list:lpe$} >>``
      ``MLast.ExRec loc (Ploc.VaVal lpe) None``
      ``<:expr< {($e$) with $list:lpe$} >>``
      ``MLast.ExRec loc (Ploc.VaVal lpe) (Some e)``
      ``<:expr< {$_list:lpe$} >>``
      ``MLast.ExRec loc lpe None``
      ``<:expr< {($e$) with $_list:lpe$} >>``
      ``MLast.ExRec loc lpe (Some e)``

   - sequence
      ``<:expr< do { $list:le$ } >>``
      ``MLast.ExSeq loc (Ploc.VaVal le)``
      ``<:expr< do { $_list:le$ } >>``
      ``MLast.ExSeq loc le``

   - method call
      ``<:expr< $e$ # $s$ >>``
      ``MLast.ExSnd loc e (Ploc.VaVal s)``
      ``<:expr< $e$ # $_:s$ >>``
      ``MLast.ExSnd loc e s``

   - string element
      ``<:expr< $e1$ .[ $e2$ ] >>``
      ``MLast.ExSte loc e1 e2``

   - string
      ``<:expr< $str:s$ >>``
      ``MLast.ExStr loc (Ploc.VaVal s)``
      ``<:expr< $_str:s$ >>``
      ``MLast.ExStr loc s``

   - try
      ``<:expr< try $e$ with [ $list:lpee$ ] >>``
      ``MLast.ExTry loc e (Ploc.VaVal lpee)``
      ``<:expr< try $e$ with [ $_list:lpee$ ] >>``
      ``MLast.ExTry loc e lpee``

   - t-uple
      ``<:expr< ($list:le$) >>``
      ``MLast.ExTup loc (Ploc.VaVal le)``
      ``<:expr< ($_list:le$) >>``
      ``MLast.ExTup loc le``

   - type constraint
      ``<:expr< ($e$ : $t$) >>``
      ``MLast.ExTyc loc e t``

   - uppercase identifier
      ``<:expr< $uid:s$ >>``
      ``MLast.ExUid loc (Ploc.VaVal s)``
      ``<:expr< $_uid:s$ >>``
      ``MLast.ExUid loc s``

   - variant
      :literal:`<:expr< ` $s$ >>`
      ``MLast.ExVrn loc (Ploc.VaVal s)``
      :literal:`<:expr< ` $_:s$ >>`
      ``MLast.ExVrn loc s``

   - while
      ``<:expr< while $e$ do { $list:le$ } >>``
      ``MLast.ExWhi loc e (Ploc.VaVal le)``
      ``<:expr< while $e$ do { $_list:le$ } >>``
      ``MLast.ExWhi loc e le``

   - extra node `(2) <#expr_2>`__
      ``... no representation ...``
      ``MLast.ExXtr loc s oe``

   .. container::
      :name: expr_1

      (1)
      Node used in the quotation expanders to tells at conversion to
      OCaml compiler syntax tree time, that all locations of the
      sub-tree is correcty located in the quotation. By default, in
      quotations, the locations of all generated nodes are the location
      of the whole quotation. This node allows to make an exception to
      this rule, since we know that the antiquotation belongs to the
      universe of the enclosing program. See the chapter about
      `quotations <quot.html>`__ and, in particular, its section about
      antiquotations.

   .. container::
      :name: expr_2

      (2)
      Extra node internally used by the quotation kit "``q_ast.cmo``" to
      build antiquotations of expressions.

   .. rubric:: patt
      :name: patt

   Patterns of the language.

   - access
      ``<:patt< $p1$ . $p2$ >>``
      ``MLast.PaAcc loc p1 p2``

   - alias
      ``<:patt< ($p1$ as $p2$) >>``
      ``MLast.PaAli loc p1 p2``

   - antiquotation `(1) <#patt_1>`__
      ``<:patt< $anti:p$ >>``
      ``MLast.PaAnt loc p``

   - wildcard
      ``<:patt< _ >>``
      ``MLast.PaAny loc``

   - application
      ``<:patt< $p1$ $p2$ >>``
      ``MLast.PaApp loc p1 p2``

   - array
      ``<:patt< [| $list:lp$ |] >>``
      ``MLast.PaArr loc (Ploc.VaVal lp)``
      ``<:patt< [| $_list:lp$ |] >>``
      ``MLast.PaArr loc lp``

   - character
      ``<:patt< $chr:s$ >>``
      ``MLast.PaChr loc (Ploc.VaVal s)``
      ``<:patt< $_chr:s$ >>``
      ``MLast.PaChr loc s``

   - float
      ``<:patt< $flo:s$ >>``
      ``MLast.PaFlo loc (Ploc.VaVal s)``
      ``<:patt< $_flo:s$ >>``
      ``MLast.PaFlo loc s``

   - integer constant
      ``<:patt< $int:s1$ >>``
      ``MLast.PaInt loc (Ploc.VaVal s1) ""``
      ``<:patt< $_int:s1$ >>``
      ``MLast.PaInt loc s1 ""``

   - integer 32 bits
      ``<:patt< $int32:s1$ >>``
      ``MLast.PaInt loc (Ploc.VaVal s1) "l"``
      ``<:patt< $_int32:s1$ >>``
      ``MLast.PaInt loc s1 "l"``

   - integer 64 bits
      ``<:patt< $int64:s1$ >>``
      ``MLast.PaInt loc (Ploc.VaVal s1) "L"``
      ``<:patt< $_int64:s1$ >>``
      ``MLast.PaInt loc s1 "L"``

   - native integer
      ``<:patt< $nativeint:s1$ >>``
      ``MLast.PaInt loc (Ploc.VaVal s1) "n"``
      ``<:patt< $_nativeint:s1$ >>``
      ``MLast.PaInt loc s1 "n"``

   - label
      ``<:patt< ~{$p1$} >>``
      ``MLast.PaLab loc p1 (Ploc.VaVal None)``
      ``<:patt< ~{$p1$ = $p2$} >>``
      ``MLast.PaLab loc p1 (Ploc.VaVal (Some p2))``
      ``<:patt< ~{$p1$ $opt:op2$} >>``
      ``MLast.PaLab loc p1 (Ploc.VaVal op2)``
      ``<:patt< ~{$p1$ $_opt:op2$} >>``
      ``MLast.PaLab loc p1 op2``

   - lazy
      ``<:patt< lazy $p$ >>``
      ``MLast.PaLaz loc p``

   - lowercase identifier
      ``<:patt< $lid:s$ >>``
      ``MLast.PaLid loc (Ploc.VaVal s)``
      ``<:patt< $_lid:s$ >>``
      ``MLast.PaLid loc s``

   - new type
      ``<:patt< (type $lid:s$) >>``
      ``MLast.PaNty loc (Ploc.VaVal s)``
      ``<:patt< (type $_lid:s$) >>``
      ``MLast.PaNty loc s``

   - option label
      ``<:patt< ?{$p$} >>``
      ``MLast.PaOlb loc p (Ploc.VaVal None)``
      ``<:patt< ?{$p$ = $e$} >>``
      ``MLast.PaOlb loc p (Ploc.VaVal (Some e))``
      ``<:patt< ?{$p$ $opt:oe$} >>``
      ``MLast.PaOlb loc p (Ploc.VaVal oe)``
      ``<:patt< ?{$p$ $_opt:oe$} >>``
      ``MLast.PaOlb loc p oe``

   - or
      ``<:patt< $p1$ | $p2$ >>``
      ``MLast.PaOrp loc p1 p2``

   - record
      ``<:patt< { $list:lpp$ } >>``
      ``MLast.PaRec loc (Ploc.VaVal lpp)``
      ``<:patt< { $_list:lpp$ } >>``
      ``MLast.PaRec loc lpp``

   - range
      ``<:patt< $p1$ .. $p2$ >>``
      ``MLast.PaRng loc p1 p2``

   - string
      ``<:patt< $str:s$ >>``
      ``MLast.PaStr loc (Ploc.VaVal s)``
      ``<:patt< $_str:s$ >>``
      ``MLast.PaStr loc s``

   - t-uple
      ``<:patt< ($list:lp$) >>``
      ``MLast.PaTup loc (Ploc.VaVal lp)``
      ``<:patt< ($_list:lp$) >>``
      ``MLast.PaTup loc lp``

   - type constraint
      ``<:patt< ($p$ : $t$) >>``
      ``MLast.PaTyc loc p t``

   - type pattern
      ``<:patt< # $list:ls$ >>``
      ``MLast.PaTyp loc (Ploc.VaVal ls)``
      ``<:patt< # $_list:ls$ >>``
      ``MLast.PaTyp loc ls``

   - uppercase identifier
      ``<:patt< $uid:s$ >>``
      ``MLast.PaUid loc (Ploc.VaVal s)``
      ``<:patt< $_uid:s$ >>``
      ``MLast.PaUid loc s``

   - module unpacking
      ``<:patt< (module $uid:s$) >>``
      ``MLast.PaUnp loc (Ploc.VaVal s) None``
      ``<:patt< (module $uid:s$ : $mt$) >>``
      ``MLast.PaUnp loc (Ploc.VaVal s) (Some mt)``
      ``<:patt< (module $_uid:s$) >>``
      ``MLast.PaUnp loc s None``
      ``<:patt< (module $_uid:s$ : $mt$) >>``
      ``MLast.PaUnp loc s (Some mt)``

   - variant
      :literal:`<:patt< ` $s$ >>`
      ``MLast.PaVrn loc (Ploc.VaVal s)``
      :literal:`<:patt< ` $_:s$ >>`
      ``MLast.PaVrn loc s``

   - extra node `(2) <#patt_2>`__
      ``... no representation ...``
      ``MLast.PaXtr loc s op``

   .. container::
      :name: patt_1

      (1) Node used to specify an antiquotation area, like for the
      equivalent node in expressions. See above.

   .. container::
      :name: patt_2

      (2) Extra node internally used by the quotation kit
      "``q_ast.cmo``" to build antiquotations of patterns.

   .. rubric:: ctyp
      :name: ctyp

   Type expressions of the language.

   - access
      ``<:ctyp< $t1$ . $t2$ >>``
      ``MLast.TyAcc loc t1 t2``

   - alias
      ``<:ctyp< $t1$ as $t2$ >>``
      ``MLast.TyAli loc t1 t2``

   - wildcard
      ``<:ctyp< _ >>``
      ``MLast.TyAny loc``

   - application
      ``<:ctyp< $t1$ $t2$ >>``
      ``MLast.TyApp loc t1 t2``

   - arrow
      ``<:ctyp< $t1$ -> $t2$ >>``
      ``MLast.TyArr loc t1 t2``

   - class
      ``<:ctyp< # $list:ls$ >>``
      ``MLast.TyCls loc (Ploc.VaVal ls)``
      ``<:ctyp< # $_list:ls$ >>``
      ``MLast.TyCls loc ls``

   - label
      ``<:ctyp< ~$s$: $t$ >>``
      ``MLast.TyLab loc (Ploc.VaVal s) t``
      ``<:ctyp< ~$_:s$: $t$ >>``
      ``MLast.TyLab loc s t``

   - lowercase identifier
      ``<:ctyp< $lid:s$ >>``
      ``MLast.TyLid loc (Ploc.VaVal s)``
      ``<:ctyp< $_lid:s$ >>``
      ``MLast.TyLid loc s``

   - manifest
      ``<:ctyp< $t1$ == private $t2$ >>``
      ``MLast.TyMan loc t1 (Ploc.VaVal True) t2``
      ``<:ctyp< $t1$ == $t2$ >>``
      ``MLast.TyMan loc t1 (Ploc.VaVal False) t2``
      ``<:ctyp< $t1$ == $priv:b$ $t2$ >>``
      ``MLast.TyMan loc t1 (Ploc.VaVal b) t2``
      ``<:ctyp< $t1$ == $_priv:b$ $t2$ >>``
      ``MLast.TyMan loc t1 b t2``

   - object
      ``<:ctyp< < $list:lst$ .. > >>``
      ``MLast.TyObj loc (Ploc.VaVal lst) (Ploc.VaVal True)``
      ``<:ctyp< < $list:lst$ > >>``
      ``MLast.TyObj loc (Ploc.VaVal lst) (Ploc.VaVal False)``
      ``<:ctyp< < $list:lst$ $flag:b$ > >>``
      ``MLast.TyObj loc (Ploc.VaVal lst) (Ploc.VaVal b)``
      ``<:ctyp< < $list:lst$ $_flag:b$ > >>``
      ``MLast.TyObj loc (Ploc.VaVal lst) b``
      ``<:ctyp< < $_list:lst$ .. > >>``
      ``MLast.TyObj loc lst (Ploc.VaVal True)``
      ``<:ctyp< < $_list:lst$ > >>``
      ``MLast.TyObj loc lst (Ploc.VaVal False)``
      ``<:ctyp< < $_list:lst$ $flag:b$ > >>``
      ``MLast.TyObj loc lst (Ploc.VaVal b)``
      ``<:ctyp< < $_list:lst$ $_flag:b$ > >>``
      ``MLast.TyObj loc lst b``

   - option label
      ``<:ctyp< ?$s$: $t$ >>``
      ``MLast.TyOlb loc (Ploc.VaVal s) t``
      ``<:ctyp< ?$_:s$: $t$ >>``
      ``MLast.TyOlb loc s t``

   - package
      ``<:ctyp< (module $mt$) >>``
      ``MLast.TyPck loc mt``

   - polymorph
      ``<:ctyp< ! $list:ls$ . $t$ >>``
      ``MLast.TyPol loc (Ploc.VaVal ls) t``
      ``<:ctyp< ! $_list:ls$ . $t$ >>``
      ``MLast.TyPol loc ls t``

   - variable
      ``<:ctyp< '$s$ >>``
      ``MLast.TyQuo loc (Ploc.VaVal s)``
      ``<:ctyp< '$_:s$ >>``
      ``MLast.TyQuo loc s``

   - record
      ``<:ctyp< { $list:llsbt$ } >>``
      ``MLast.TyRec loc (Ploc.VaVal llsbt)``
      ``<:ctyp< { $_list:llsbt$ } >>``
      ``MLast.TyRec loc llsbt``

   - sum
      ``<:ctyp< [ $list:llslt$ ] >>``
      ``MLast.TySum loc (Ploc.VaVal llslt)``
      ``<:ctyp< [ $_list:llslt$ ] >>``
      ``MLast.TySum loc llslt``

   - t-uple
      ``<:ctyp< ( $list:lt$ ) >>``
      ``MLast.TyTup loc (Ploc.VaVal lt)``
      ``<:ctyp< ( $_list:lt$ ) >>``
      ``MLast.TyTup loc lt``

   - uppercase identifier
      ``<:ctyp< $uid:s$ >>``
      ``MLast.TyUid loc (Ploc.VaVal s)``
      ``<:ctyp< $_uid:s$ >>``
      ``MLast.TyUid loc s``

   - variant
      ``<:ctyp< [ = $list:lpv$ ] >>``
      ``MLast.TyVrn loc (Ploc.VaVal lpv) None``
      ``<:ctyp< [ > $list:lpv$ ] >>``
      ``MLast.TyVrn loc (Ploc.VaVal lpv) (Some None)``
      ``<:ctyp< [ < $list:lpv$ ] >>``
      ``MLast.TyVrn loc (Ploc.VaVal lpv) (Some (Some (Ploc.VaVal [])))``
      ``<:ctyp< [ < $list:lpv$ > $list:ls$ ] >>``
      ``MLast.TyVrn loc (Ploc.VaVal lpv) (Some (Some (Ploc.VaVal ls)))``
      ``<:ctyp< [ < $list:lpv$ > $_list:ls$ ] >>``
      ``MLast.TyVrn loc (Ploc.VaVal lpv) (Some (Some ls))``
      ``<:ctyp< [ = $_list:lpv$ ] >>``
      ``MLast.TyVrn loc lpv None``
      ``<:ctyp< [ > $_list:lpv$ ] >>``
      ``MLast.TyVrn loc lpv (Some None)``
      ``<:ctyp< [ < $_list:lpv$ ] >>``
      ``MLast.TyVrn loc lpv (Some (Some (Ploc.VaVal [])))``
      ``<:ctyp< [ < $_list:lpv$ > $list:ls$ ] >>``
      ``MLast.TyVrn loc lpv (Some (Some (Ploc.VaVal ls)))``
      ``<:ctyp< [ < $_list:lpv$ > $_list:ls$ ] >>``
      ``MLast.TyVrn loc lpv (Some (Some ls))``

   - extra node `(1) <#ctyp_1>`__
      ``... no representation ...``
      ``MLast.TyXtr loc s ot``

   .. container::
      :name: ctyp_1

      (1) Extra node internally used by the quotation kit
      "``q_ast.cmo``" to build antiquotations of types.

   .. rubric:: modules...
      :name: modules...

   .. rubric:: str_item
      :name: str_item

   Structure items, i.e. phrases in a ".ml" file or "struct" elements.

   - class declaration
      ``<:str_item< class $list:lcice$ >>``
      ``MLast.StCls loc (Ploc.VaVal lcice)``
      ``<:str_item< class $_list:lcice$ >>``
      ``MLast.StCls loc lcice``

   - class type declaration
      ``<:str_item< class type $list:lcict$ >>``
      ``MLast.StClt loc (Ploc.VaVal lcict)``
      ``<:str_item< class type $_list:lcict$ >>``
      ``MLast.StClt loc lcict``

   - declare
      ``<:str_item< declare $list:lsi$ end >>``
      ``MLast.StDcl loc (Ploc.VaVal lsi)``
      ``<:str_item< declare $_list:lsi$ end >>``
      ``MLast.StDcl loc lsi``

   - directive
      ``<:str_item< # $lid:s$ >>``
      ``MLast.StDir loc (Ploc.VaVal s) (Ploc.VaVal None)``
      ``<:str_item< # $lid:s$ $e$ >>``
      ``MLast.StDir loc (Ploc.VaVal s) (Ploc.VaVal (Some e))``
      ``<:str_item< # $lid:s$ $opt:oe$ >>``
      ``MLast.StDir loc (Ploc.VaVal s) (Ploc.VaVal oe)``
      ``<:str_item< # $lid:s$ $_opt:oe$ >>``
      ``MLast.StDir loc (Ploc.VaVal s) oe``
      ``<:str_item< # $_lid:s$ >>``
      ``MLast.StDir loc s (Ploc.VaVal None)``
      ``<:str_item< # $_lid:s$ $e$ >>``
      ``MLast.StDir loc s (Ploc.VaVal (Some e))``
      ``<:str_item< # $_lid:s$ $opt:oe$ >>``
      ``MLast.StDir loc s (Ploc.VaVal oe)``
      ``<:str_item< # $_lid:s$ $_opt:oe$ >>``
      ``MLast.StDir loc s oe``

   - exception
      ``<:str_item< exception $uid:s$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal []) (Ploc.VaVal [])``
      ``<:str_item< exception $uid:s$ of $list:lt$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal lt) (Ploc.VaVal [])``
      ``<:str_item< exception $uid:s$ = $list:ls$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal []) (Ploc.VaVal ls)``
      ``<:str_item< exception $uid:s$ of $list:lt$ = $list:ls$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal lt) (Ploc.VaVal ls)``
      ``<:str_item< exception $uid:s$ = $_list:ls$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal []) ls``
      ``<:str_item< exception $uid:s$ of $list:lt$ = $_list:ls$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal lt) ls``
      ``<:str_item< exception $uid:s$ of $_list:lt$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) lt (Ploc.VaVal [])``
      ``<:str_item< exception $uid:s$ of $_list:lt$ = $list:ls$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) lt (Ploc.VaVal ls)``
      ``<:str_item< exception $uid:s$ of $_list:lt$ = $_list:ls$ >>``
      ``MLast.StExc loc (Ploc.VaVal s) lt ls``
      ``<:str_item< exception $_uid:s$ >>``
      ``MLast.StExc loc s (Ploc.VaVal []) (Ploc.VaVal [])``
      ``<:str_item< exception $_uid:s$ of $list:lt$ >>``
      ``MLast.StExc loc s (Ploc.VaVal lt) (Ploc.VaVal [])``
      ``<:str_item< exception $_uid:s$ = $list:ls$ >>``
      ``MLast.StExc loc s (Ploc.VaVal []) (Ploc.VaVal ls)``
      ``<:str_item< exception $_uid:s$ of $list:lt$ = $list:ls$ >>``
      ``MLast.StExc loc s (Ploc.VaVal lt) (Ploc.VaVal ls)``
      ``<:str_item< exception $_uid:s$ = $_list:ls$ >>``
      ``MLast.StExc loc s (Ploc.VaVal []) ls``
      ``<:str_item< exception $_uid:s$ of $list:lt$ = $_list:ls$ >>``
      ``MLast.StExc loc s (Ploc.VaVal lt) ls``
      ``<:str_item< exception $_uid:s$ of $_list:lt$ >>``
      ``MLast.StExc loc s lt (Ploc.VaVal [])``
      ``<:str_item< exception $_uid:s$ of $_list:lt$ = $list:ls$ >>``
      ``MLast.StExc loc s lt (Ploc.VaVal ls)``
      ``<:str_item< exception $_uid:s$ of $_list:lt$ = $_list:ls$ >>``
      ``MLast.StExc loc s lt ls``

   - expression
      ``<:str_item< $exp:e$ >>``
      ``MLast.StExp loc e``

   - external
      ``<:str_item< external $s$ : $t$ = $list:ls$ >>``
      ``MLast.StExt loc (Ploc.VaVal s) t (Ploc.VaVal ls)``
      ``<:str_item< external $s$ : $t$ = $_list:ls$ >>``
      ``MLast.StExt loc (Ploc.VaVal s) t ls``
      ``<:str_item< external $_:s$ : $t$ = $list:ls$ >>``
      ``MLast.StExt loc s t (Ploc.VaVal ls)``
      ``<:str_item< external $_:s$ : $t$ = $_list:ls$ >>``
      ``MLast.StExt loc s t ls``

   - include
      ``<:str_item< include $me$ >>``
      ``MLast.StInc loc me``

   - module rec
      ``<:str_item< module rec $list:lsme$ >>``
      ``MLast.StMod loc (Ploc.VaVal True) (Ploc.VaVal lsme)``
      ``<:str_item< module rec $_list:lsme$ >>``
      ``MLast.StMod loc (Ploc.VaVal True) lsme``

   - module non rec
      ``<:str_item< module $list:lsme$ >>``
      ``MLast.StMod loc (Ploc.VaVal False) (Ploc.VaVal lsme)``
      ``<:str_item< module $_list:lsme$ >>``
      ``MLast.StMod loc (Ploc.VaVal False) lsme``

   - module
      ``<:str_item< module $flag:b$ $list:lsme$ >>``
      ``MLast.StMod loc (Ploc.VaVal b) (Ploc.VaVal lsme)``
      ``<:str_item< module $flag:b$ $_list:lsme$ >>``
      ``MLast.StMod loc (Ploc.VaVal b) lsme``
      ``<:str_item< module $_flag:b$ $list:lsme$ >>``
      ``MLast.StMod loc b (Ploc.VaVal lsme)``
      ``<:str_item< module $_flag:b$ $_list:lsme$ >>``
      ``MLast.StMod loc b lsme``

   - module type
      ``<:str_item< module type $s$ = $mt$ >>``
      ``MLast.StMty loc (Ploc.VaVal s) mt``
      ``<:str_item< module type $_:s$ = $mt$ >>``
      ``MLast.StMty loc s mt``

   - open
      ``<:str_item< open $list:ls$ >>``
      ``MLast.StOpn loc (Ploc.VaVal ls)``
      ``<:str_item< open $_list:ls$ >>``
      ``MLast.StOpn loc ls``

   - type declaration
      ``<:str_item< type $list:ltd$ >>``
      ``MLast.StTyp loc (Ploc.VaVal ltd)``
      ``<:str_item< type $_list:ltd$ >>``
      ``MLast.StTyp loc ltd``

   - ... internal use ... `(1) <#t_str_item_1>`__
      ``<:str_item< # $str:s$ $list:lsil$ >>``
      ``MLast.StUse loc (Ploc.VaVal s) (Ploc.VaVal lsil)``
      ``<:str_item< # $str:s$ $_list:lsil$ >>``
      ``MLast.StUse loc (Ploc.VaVal s) lsil``
      ``<:str_item< # $_str:s$ $list:lsil$ >>``
      ``MLast.StUse loc s (Ploc.VaVal lsil)``
      ``<:str_item< # $_str:s$ $_list:lsil$ >>``
      ``MLast.StUse loc s lsil``

   - value rec
      ``<:str_item< value rec $list:lpe$ >>``
      ``MLast.StVal loc (Ploc.VaVal True) (Ploc.VaVal lpe)``
      ``<:str_item< value rec $_list:lpe$ >>``
      ``MLast.StVal loc (Ploc.VaVal True) lpe``

   - value non rec
      ``<:str_item< value $list:lpe$ >>``
      ``MLast.StVal loc (Ploc.VaVal False) (Ploc.VaVal lpe)``
      ``<:str_item< value $_list:lpe$ >>``
      ``MLast.StVal loc (Ploc.VaVal False) lpe``

   - value
      ``<:str_item< value $flag:b$ $list:lpe$ >>``
      ``MLast.StVal loc (Ploc.VaVal b) (Ploc.VaVal lpe)``
      ``<:str_item< value $flag:b$ $_list:lpe$ >>``
      ``MLast.StVal loc (Ploc.VaVal b) lpe``
      ``<:str_item< value $_flag:b$ $list:lpe$ >>``
      ``MLast.StVal loc b (Ploc.VaVal lpe)``
      ``<:str_item< value $_flag:b$ $_list:lpe$ >>``
      ``MLast.StVal loc b lpe``

   - extra node `(2) <#str_item_2>`__
      ``... no representation ...``
      ``MLast.StXtr loc s ot``

   .. container::
      :name: t_str_item_1

      (1)
      Node internally used to specify a different file name applying to
      the whole subtree. This is generated by the directive "use" and
      used when converting to the OCaml syntax tree which needs the file
      name in its location type.

   .. container::
      :name: str_item_2

      (2)
      Extra node internally used by the quotation kit "``q_ast.cmo``" to
      build antiquotations of structure items.

   .. rubric:: sig_item
      :name: sig_item

   Signature items, i.e. phrases in a ".mli" file or elements inside
   "sig ... end".

   - class
      ``<:sig_item< class $list:lcict$ >>``
      ``MLast.SgCls loc (Ploc.VaVal lcict)``
      ``<:sig_item< class $_list:lcict$ >>``
      ``MLast.SgCls loc lcict``

   - class type
      ``<:sig_item< class type $list:lcict$ >>``
      ``MLast.SgClt loc (Ploc.VaVal lcict)``
      ``<:sig_item< class type $_list:lcict$ >>``
      ``MLast.SgClt loc lcict``

   - declare
      ``<:sig_item< declare $list:lsi$ end >>``
      ``MLast.SgDcl loc (Ploc.VaVal lsi)``
      ``<:sig_item< declare $_list:lsi$ end >>``
      ``MLast.SgDcl loc lsi``

   - directive
      ``<:sig_item< # $lid:s$ >>``
      ``MLast.SgDir loc (Ploc.VaVal s) (Ploc.VaVal None)``
      ``<:sig_item< # $lid:s$ $e$ >>``
      ``MLast.SgDir loc (Ploc.VaVal s) (Ploc.VaVal (Some e))``
      ``<:sig_item< # $lid:s$ $opt:oe$ >>``
      ``MLast.SgDir loc (Ploc.VaVal s) (Ploc.VaVal oe)``
      ``<:sig_item< # $lid:s$ $_opt:oe$ >>``
      ``MLast.SgDir loc (Ploc.VaVal s) oe``
      ``<:sig_item< # $_lid:s$ >>``
      ``MLast.SgDir loc s (Ploc.VaVal None)``
      ``<:sig_item< # $_lid:s$ $e$ >>``
      ``MLast.SgDir loc s (Ploc.VaVal (Some e))``
      ``<:sig_item< # $_lid:s$ $opt:oe$ >>``
      ``MLast.SgDir loc s (Ploc.VaVal oe)``
      ``<:sig_item< # $_lid:s$ $_opt:oe$ >>``
      ``MLast.SgDir loc s oe``

   - exception
      ``<:sig_item< exception $s$ >>``
      ``MLast.SgExc loc (Ploc.VaVal s) (Ploc.VaVal [])``
      ``<:sig_item< exception $s$ of $list:lt$ >>``
      ``MLast.SgExc loc (Ploc.VaVal s) (Ploc.VaVal lt)``
      ``<:sig_item< exception $s$ of $_list:lt$ >>``
      ``MLast.SgExc loc (Ploc.VaVal s) lt``
      ``<:sig_item< exception $_:s$ >>``
      ``MLast.SgExc loc s (Ploc.VaVal [])``
      ``<:sig_item< exception $_:s$ of $list:lt$ >>``
      ``MLast.SgExc loc s (Ploc.VaVal lt)``
      ``<:sig_item< exception $_:s$ of $_list:lt$ >>``
      ``MLast.SgExc loc s lt``

   - external
      ``<:sig_item< external $s$ : $t$ = $list:ls$ >>``
      ``MLast.SgExt loc (Ploc.VaVal s) t (Ploc.VaVal ls)``
      ``<:sig_item< external $s$ : $t$ = $_list:ls$ >>``
      ``MLast.SgExt loc (Ploc.VaVal s) t ls``
      ``<:sig_item< external $_:s$ : $t$ = $list:ls$ >>``
      ``MLast.SgExt loc s t (Ploc.VaVal ls)``
      ``<:sig_item< external $_:s$ : $t$ = $_list:ls$ >>``
      ``MLast.SgExt loc s t ls``

   - include
      ``<:sig_item< include $mt$ >>``
      ``MLast.SgInc loc mt``

   - module rec
      ``<:sig_item< module rec $list:lsmt$ >>``
      ``MLast.SgMod loc (Ploc.VaVal True) (Ploc.VaVal lsmt)``
      ``<:sig_item< module rec $_list:lsmt$ >>``
      ``MLast.SgMod loc (Ploc.VaVal True) lsmt``

   - module non rec
      ``<:sig_item< module $list:lsmt$ >>``
      ``MLast.SgMod loc (Ploc.VaVal False) (Ploc.VaVal lsmt)``
      ``<:sig_item< module $_list:lsmt$ >>``
      ``MLast.SgMod loc (Ploc.VaVal False) lsmt``

   - module
      ``<:sig_item< module $flag:b$ $list:lsmt$ >>``
      ``MLast.SgMod loc (Ploc.VaVal b) (Ploc.VaVal lsmt)``
      ``<:sig_item< module $flag:b$ $_list:lsmt$ >>``
      ``MLast.SgMod loc (Ploc.VaVal b) lsmt``
      ``<:sig_item< module $_flag:b$ $list:lsmt$ >>``
      ``MLast.SgMod loc b (Ploc.VaVal lsmt)``
      ``<:sig_item< module $_flag:b$ $_list:lsmt$ >>``
      ``MLast.SgMod loc b lsmt``

   - module type
      ``<:sig_item< module type $s$ = $mt$ >>``
      ``MLast.SgMty loc (Ploc.VaVal s) mt``
      ``<:sig_item< module type $_:s$ = $mt$ >>``
      ``MLast.SgMty loc s mt``

   - open
      ``<:sig_item< open $list:ls$ >>``
      ``MLast.SgOpn loc (Ploc.VaVal ls)``
      ``<:sig_item< open $_list:ls$ >>``
      ``MLast.SgOpn loc ls``

   - type declaration
      ``<:sig_item< type $list:ltd$ >>``
      ``MLast.SgTyp loc (Ploc.VaVal ltd)``
      ``<:sig_item< type $_list:ltd$ >>``
      ``MLast.SgTyp loc ltd``

   - ... internal use ... `(1) <#t_sig_item_1>`__
      ``<:sig_item< # $str:s$ $list:lsil$ >>``
      ``MLast.SgUse loc (Ploc.VaVal s) (Ploc.VaVal lsil)``
      ``<:sig_item< # $str:s$ $_list:lsil$ >>``
      ``MLast.SgUse loc (Ploc.VaVal s) lsil``
      ``<:sig_item< # $_str:s$ $list:lsil$ >>``
      ``MLast.SgUse loc s (Ploc.VaVal lsil)``
      ``<:sig_item< # $_str:s$ $_list:lsil$ >>``
      ``MLast.SgUse loc s lsil``

   - value
      ``<:sig_item< value $s$ : $t$ >>``
      ``MLast.SgVal loc (Ploc.VaVal s) t``
      ``<:sig_item< value $_:s$ : $t$ >>``
      ``MLast.SgVal loc s t``

   - extra node `(2) <#sig_item_2>`__
      ``... no representation ...``
      ``MLast.SgXtr loc s ot``

   .. container::
      :name: t_sig_item_1

      (1) Same remark as for "``str_item``" above.

   .. container::
      :name: sig_item_2

      (2) Extra node internally used by the quotation kit
      "``q_ast.cmo``" to build antiquotations of signature items.

   .. rubric:: module_expr
      :name: module_expr

   - access
      ``<:module_expr< $me1$ . $me2$ >>``
      ``MLast.MeAcc loc me1 me2``

   - application
      ``<:module_expr< $me1$ $me2$ >>``
      ``MLast.MeApp loc me1 me2``

   - functor
      ``<:module_expr< functor ($s$ : $mt$) -> $me$ >>``
      ``MLast.MeFun loc (Ploc.VaVal s) mt me``
      ``<:module_expr< functor ($_:s$ : $mt$) -> $me$ >>``
      ``MLast.MeFun loc s mt me``

   - struct
      ``<:module_expr< struct $list:lsi$ end >>``
      ``MLast.MeStr loc (Ploc.VaVal lsi)``
      ``<:module_expr< struct $_list:lsi$ end >>``
      ``MLast.MeStr loc lsi``

   - module type constraint
      ``<:module_expr< ($me$ : $mt$) >>``
      ``MLast.MeTyc loc me mt``

   - uppercase identifier
      ``<:module_expr< $uid:s$ >>``
      ``MLast.MeUid loc (Ploc.VaVal s)``
      ``<:module_expr< $_uid:s$ >>``
      ``MLast.MeUid loc s``

   - module unpacking
      ``<:module_expr< (value $e$) >>``
      ``MLast.MeUnp loc e None``
      ``<:module_expr< (value $e$ : $mt$) >>``
      ``MLast.MeUnp loc e (Some mt)``

   - extra node `(1) <#module_expr_1>`__
      ``... no representation ...``
      ``MLast.MeXtr loc s ot``

   .. container::
      :name: module_expr_1

      (1) Extra node internally used by the quotation kit
      "``q_ast.cmo``" to build antiquotations of module expressions.

   .. rubric:: module_type
      :name: module_type

   - access
      ``<:module_type< $mt1$ . $mt2$ >>``
      ``MLast.MtAcc loc mt1 mt2``

   - application
      ``<:module_type< $mt1$ $mt2$ >>``
      ``MLast.MtApp loc mt1 mt2``

   - functor
      ``<:module_type< functor ($s$ : $mt1$) -> $mt2$ >>``
      ``MLast.MtFun loc (Ploc.VaVal s) mt1 mt2``
      ``<:module_type< functor ($_:s$ : $mt1$) -> $mt2$ >>``
      ``MLast.MtFun loc s mt1 mt2``

   - lowercase identifier
      ``<:module_type< $lid:s$ >>``
      ``MLast.MtLid loc (Ploc.VaVal s)``
      ``<:module_type< $_lid:s$ >>``
      ``MLast.MtLid loc s``

   - abstract
      ``<:module_type< ' $s$ >>``
      ``MLast.MtQuo loc (Ploc.VaVal s)``
      ``<:module_type< ' $_:s$ >>``
      ``MLast.MtQuo loc s``

   - signature
      ``<:module_type< sig $list:lsi$ end >>``
      ``MLast.MtSig loc (Ploc.VaVal lsi)``
      ``<:module_type< sig $_list:lsi$ end >>``
      ``MLast.MtSig loc lsi``

   - of module expression
      ``<:module_type< module type of $me$ >>``
      ``MLast.MtTyo loc me``

   - uppercase identifier
      ``<:module_type< $uid:s$ >>``
      ``MLast.MtUid loc (Ploc.VaVal s)``
      ``<:module_type< $_uid:s$ >>``
      ``MLast.MtUid loc s``

   - with construction
      ``<:module_type< $mt$ with $list:lwc$ >>``
      ``MLast.MtWit loc mt (Ploc.VaVal lwc)``
      ``<:module_type< $mt$ with $_list:lwc$ >>``
      ``MLast.MtWit loc mt lwc``

   - extra node `(1) <#module_type_1>`__
      ``... no representation ...``
      ``MLast.MtXtr loc s ot``

   .. container::
      :name: module_type_1

      (1) Extra node internally used by the quotation kit
      "``q_ast.cmo``" to build antiquotations of module types.

   .. rubric:: classes...
      :name: classes...

   .. rubric:: class_expr
      :name: class_expr

   - application
      ``<:class_expr< $ce$ $e$ >>``
      ``MLast.CeApp loc ce e``

   - constructor
      ``<:class_expr< [ $list:lt$ ] $list:ls$ >>``
      ``MLast.CeCon loc (Ploc.VaVal ls) (Ploc.VaVal lt)``
      ``<:class_expr< [ $_list:lt$ ] $list:ls$ >>``
      ``MLast.CeCon loc (Ploc.VaVal ls) lt``
      ``<:class_expr< [ $list:lt$ ] $_list:ls$ >>``
      ``MLast.CeCon loc ls (Ploc.VaVal lt)``
      ``<:class_expr< [ $_list:lt$ ] $_list:ls$ >>``
      ``MLast.CeCon loc ls lt``

   - function
      ``<:class_expr< fun $p$ -> $ce$ >>``
      ``MLast.CeFun loc p ce``

   - let rec
      ``<:class_expr< let rec $list:lpe$ in $ce$ >>``
      ``MLast.CeLet loc (Ploc.VaVal True) (Ploc.VaVal lpe) ce``
      ``<:class_expr< let rec $_list:lpe$ in $ce$ >>``
      ``MLast.CeLet loc (Ploc.VaVal True) lpe ce``

   - let non rec
      ``<:class_expr< let $list:lpe$ in $ce$ >>``
      ``MLast.CeLet loc (Ploc.VaVal False) (Ploc.VaVal lpe) ce``
      ``<:class_expr< let $_list:lpe$ in $ce$ >>``
      ``MLast.CeLet loc (Ploc.VaVal False) lpe ce``

   - let
      ``<:class_expr< let $flag:b$ $list:lpe$ in $ce$ >>``
      ``MLast.CeLet loc (Ploc.VaVal b) (Ploc.VaVal lpe) ce``
      ``<:class_expr< let $flag:b$ $_list:lpe$ in $ce$ >>``
      ``MLast.CeLet loc (Ploc.VaVal b) lpe ce``
      ``<:class_expr< let $_flag:b$ $list:lpe$ in $ce$ >>``
      ``MLast.CeLet loc b (Ploc.VaVal lpe) ce``
      ``<:class_expr< let $_flag:b$ $_list:lpe$ in $ce$ >>``
      ``MLast.CeLet loc b lpe ce``

   - object
      ``<:class_expr< object $list:lcsi$ end >>``
      ``MLast.CeStr loc (Ploc.VaVal None) (Ploc.VaVal lcsi)``
      ``<:class_expr< object $_list:lcsi$ end >>``
      ``MLast.CeStr loc (Ploc.VaVal None) lcsi``
      ``<:class_expr< object ($p$) $list:lcsi$ end >>``
      ``MLast.CeStr loc (Ploc.VaVal (Some p)) (Ploc.VaVal lcsi)``
      ``<:class_expr< object ($p$) $_list:lcsi$ end >>``
      ``MLast.CeStr loc (Ploc.VaVal (Some p)) lcsi``
      ``<:class_expr< object $opt:op$ $list:lcsi$ end >>``
      ``MLast.CeStr loc (Ploc.VaVal op) (Ploc.VaVal lcsi)``
      ``<:class_expr< object $opt:op$ $_list:lcsi$ end >>``
      ``MLast.CeStr loc (Ploc.VaVal op) lcsi``
      ``<:class_expr< object $_opt:op$ $list:lcsi$ end >>``
      ``MLast.CeStr loc op (Ploc.VaVal lcsi)``
      ``<:class_expr< object $_opt:op$ $_list:lcsi$ end >>``
      ``MLast.CeStr loc op lcsi``

   - class type constraint
      ``<:class_expr< ($ce$ : $ct$) >>``
      ``MLast.CeTyc loc ce ct``

   .. rubric:: class_type
      :name: class_type

   - access
      ``<:class_type< $ct1$ . $ct2$ >>``
      ``MLast.CtAcc loc ct1 ct2``

   - application
      ``<:class_type< $ct1$ $ct2$ >>``
      ``MLast.CtApp loc ct1 ct2``

   - constructor
      ``<:class_type< $ct$ [ $list:lt$ ] >>``
      ``MLast.CtCon loc ct (Ploc.VaVal lt)``
      ``<:class_type< $ct$ [ $_list:lt$ ] >>``
      ``MLast.CtCon loc ct lt``

   - arrow
      ``<:class_type< [ $t$ ] -> $ct$ >>``
      ``MLast.CtFun loc t ct``

   - identifier
      ``<:class_type< $id:s$ >>``
      ``MLast.CtIde loc (Ploc.VaVal s)``
      ``<:class_type< $_id:s$ >>``
      ``MLast.CtIde loc s``

   - object
      ``<:class_type< object $list:lcsi$ end >>``
      ``MLast.CtSig loc (Ploc.VaVal None) (Ploc.VaVal lcsi)``
      ``<:class_type< object $_list:lcsi$ end >>``
      ``MLast.CtSig loc (Ploc.VaVal None) lcsi``
      ``<:class_type< object ($t$) $list:lcsi$ end >>``
      ``MLast.CtSig loc (Ploc.VaVal (Some t)) (Ploc.VaVal lcsi)``
      ``<:class_type< object ($t$) $_list:lcsi$ end >>``
      ``MLast.CtSig loc (Ploc.VaVal (Some t)) lcsi``
      ``<:class_type< object $opt:ot$ $list:lcsi$ end >>``
      ``MLast.CtSig loc (Ploc.VaVal ot) (Ploc.VaVal lcsi)``
      ``<:class_type< object $opt:ot$ $_list:lcsi$ end >>``
      ``MLast.CtSig loc (Ploc.VaVal ot) lcsi``
      ``<:class_type< object $_opt:ot$ $list:lcsi$ end >>``
      ``MLast.CtSig loc ot (Ploc.VaVal lcsi)``
      ``<:class_type< object $_opt:ot$ $_list:lcsi$ end >>``
      ``MLast.CtSig loc ot lcsi``

   .. rubric:: class_str_item
      :name: class_str_item

   - type constraint
      ``<:class_str_item< type $t1$ = $t2$ >>``
      ``MLast.CrCtr loc t1 t2``

   - declaration list
      ``<:class_str_item< declare $list:lcsi$ end >>``
      ``MLast.CrDcl loc (Ploc.VaVal lcsi)``
      ``<:class_str_item< declare $_list:lcsi$ end >>``
      ``MLast.CrDcl loc lcsi``

   - inheritance
      ``<:class_str_item< inherit $ce$ >>``
      ``MLast.CrInh loc ce (Ploc.VaVal None)``
      ``<:class_str_item< inherit $ce$ $opt:Some s$ >>``
      ``MLast.CrInh loc ce (Ploc.VaVal (Some s))``
      ``<:class_str_item< inherit $ce$ $opt:os$ >>``
      ``MLast.CrInh loc ce (Ploc.VaVal os)``
      ``<:class_str_item< inherit $ce$ $_opt:os$ >>``
      ``MLast.CrInh loc ce os``

   - initialization
      ``<:class_str_item< initializer $e$ >>``
      ``MLast.CrIni loc e``

   - method
      ``<:class_str_item< method! private $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method! private $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method! private $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method! private $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method! private $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) s (Ploc.VaVal None) e``
      ``<:class_str_item< method! private $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method! private $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method! private $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) s ot e``
      ``<:class_str_item< method! $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method! $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method! $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method! $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method! $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) s (Ploc.VaVal None) e``
      ``<:class_str_item< method! $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method! $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method! $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) s ot e``
      ``<:class_str_item< method! $priv:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method! $priv:b2$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method! $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method! $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method! $priv:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) s (Ploc.VaVal None) e``
      ``<:class_str_item< method! $priv:b2$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method! $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method! $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) s ot e``
      ``<:class_str_item< method! $_priv:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) b2 (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method! $_priv:b2$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) b2 (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method! $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) b2 (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method! $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) b2 (Ploc.VaVal s) ot e``
      ``<:class_str_item< method! $_priv:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) b2 s (Ploc.VaVal None) e``
      ``<:class_str_item< method! $_priv:b2$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) b2 s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method! $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) b2 s (Ploc.VaVal ot) e``
      ``<:class_str_item< method! $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal True) b2 s ot e``
      ``<:class_str_item< method private $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method private $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method private $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method private $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method private $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) s (Ploc.VaVal None) e``
      ``<:class_str_item< method private $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method private $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method private $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) s ot e``
      ``<:class_str_item< method $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) s (Ploc.VaVal None) e``
      ``<:class_str_item< method $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) s ot e``
      ``<:class_str_item< method $priv:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $priv:b2$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $priv:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) s (Ploc.VaVal None) e``
      ``<:class_str_item< method $priv:b2$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) s ot e``
      ``<:class_str_item< method $_priv:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) b2 (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $_priv:b2$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) b2 (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) b2 (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) b2 (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $_priv:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) b2 s (Ploc.VaVal None) e``
      ``<:class_str_item< method $_priv:b2$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) b2 s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) b2 s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal False) b2 s ot e``
      ``<:class_str_item< method $!:b1$ private $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $!:b1$ private $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $!:b1$ private $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $!:b1$ private $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $!:b1$ private $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) s (Ploc.VaVal None) e``
      ``<:class_str_item< method $!:b1$ private $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $!:b1$ private $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $!:b1$ private $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) s ot e``
      ``<:class_str_item< method $!:b1$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $!:b1$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $!:b1$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $!:b1$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $!:b1$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) s (Ploc.VaVal None) e``
      ``<:class_str_item< method $!:b1$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $!:b1$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $!:b1$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) s ot e``
      ``<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) s (Ploc.VaVal None) e``
      ``<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) s ot e``
      ``<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) b2 s (Ploc.VaVal None) e``
      ``<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) b2 s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) b2 s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc (Ploc.VaVal b1) b2 s ot e``
      ``<:class_str_item< method $_!:b1$ private $lid:s$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $_!:b1$ private $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_!:b1$ private $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_!:b1$ private $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal True) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $_!:b1$ private $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal True) s (Ploc.VaVal None) e``
      ``<:class_str_item< method $_!:b1$ private $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal True) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_!:b1$ private $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal True) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_!:b1$ private $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal True) s ot e``
      ``<:class_str_item< method $_!:b1$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $_!:b1$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_!:b1$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_!:b1$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal False) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $_!:b1$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal False) s (Ploc.VaVal None) e``
      ``<:class_str_item< method $_!:b1$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal False) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_!:b1$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal False) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_!:b1$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal False) s ot e``
      ``<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal b2) s (Ploc.VaVal None) e``
      ``<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal b2) s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal b2) s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 (Ploc.VaVal b2) s ot e``
      ``<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrMth loc b1 b2 (Ploc.VaVal s) (Ploc.VaVal None) e``
      ``<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc b1 b2 (Ploc.VaVal s) (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 b2 (Ploc.VaVal s) (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 b2 (Ploc.VaVal s) ot e``
      ``<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrMth loc b1 b2 s (Ploc.VaVal None) e``
      ``<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ >>``
      ``MLast.CrMth loc b1 b2 s (Ploc.VaVal (Some t)) e``
      ``<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 b2 s (Ploc.VaVal ot) e``
      ``<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>``
      ``MLast.CrMth loc b1 b2 s ot e``

   - value
      ``<:class_str_item< value! mutable $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) e``
      ``<:class_str_item< value! mutable $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal True) s e``
      ``<:class_str_item< value! $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) e``
      ``<:class_str_item< value! $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal False) s e``
      ``<:class_str_item< value! $flag:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) e``
      ``<:class_str_item< value! $flag:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal b2) s e``
      ``<:class_str_item< value! $_flag:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal True) b2 (Ploc.VaVal s) e``
      ``<:class_str_item< value! $_flag:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal True) b2 s e``
      ``<:class_str_item< value mutable $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) e``
      ``<:class_str_item< value mutable $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal True) s e``
      ``<:class_str_item< value $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) e``
      ``<:class_str_item< value $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal False) s e``
      ``<:class_str_item< value $flag:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) e``
      ``<:class_str_item< value $flag:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal b2) s e``
      ``<:class_str_item< value $_flag:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal False) b2 (Ploc.VaVal s) e``
      ``<:class_str_item< value $_flag:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal False) b2 s e``
      ``<:class_str_item< value $!:b1$ mutable $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) e``
      ``<:class_str_item< value $!:b1$ mutable $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal True) s e``
      ``<:class_str_item< value $!:b1$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) e``
      ``<:class_str_item< value $!:b1$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal False) s e``
      ``<:class_str_item< value $!:b1$ $flag:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) e``
      ``<:class_str_item< value $!:b1$ $flag:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal b2) s e``
      ``<:class_str_item< value $!:b1$ $_flag:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) e``
      ``<:class_str_item< value $!:b1$ $_flag:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc (Ploc.VaVal b1) b2 s e``
      ``<:class_str_item< value $_!:b1$ mutable $lid:s$ = $e$ >>``
      ``MLast.CrVal loc b1 (Ploc.VaVal True) (Ploc.VaVal s) e``
      ``<:class_str_item< value $_!:b1$ mutable $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc b1 (Ploc.VaVal True) s e``
      ``<:class_str_item< value $_!:b1$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc b1 (Ploc.VaVal False) (Ploc.VaVal s) e``
      ``<:class_str_item< value $_!:b1$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc b1 (Ploc.VaVal False) s e``
      ``<:class_str_item< value $_!:b1$ $flag:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) e``
      ``<:class_str_item< value $_!:b1$ $flag:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc b1 (Ploc.VaVal b2) s e``
      ``<:class_str_item< value $_!:b1$ $_flag:b2$ $lid:s$ = $e$ >>``
      ``MLast.CrVal loc b1 b2 (Ploc.VaVal s) e``
      ``<:class_str_item< value $_!:b1$ $_flag:b2$ $_lid:s$ = $e$ >>``
      ``MLast.CrVal loc b1 b2 s e``

   - virtual value
      ``<:class_str_item< value virtual mutable $lid:s$ : $t$ >>``
      ``MLast.CrVav loc (Ploc.VaVal True) (Ploc.VaVal s) t``
      ``<:class_str_item< value virtual mutable $_lid:s$ : $t$ >>``
      ``MLast.CrVav loc (Ploc.VaVal True) s t``
      ``<:class_str_item< value virtual $lid:s$ : $t$ >>``
      ``MLast.CrVav loc (Ploc.VaVal False) (Ploc.VaVal s) t``
      ``<:class_str_item< value virtual $_lid:s$ : $t$ >>``
      ``MLast.CrVav loc (Ploc.VaVal False) s t``
      ``<:class_str_item< value virtual $flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CrVav loc (Ploc.VaVal b) (Ploc.VaVal s) t``
      ``<:class_str_item< value virtual $flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CrVav loc (Ploc.VaVal b) s t``
      ``<:class_str_item< value virtual $_flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CrVav loc b (Ploc.VaVal s) t``
      ``<:class_str_item< value virtual $_flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CrVav loc b s t``

   - virtual method
      ``<:class_str_item< method virtual private $lid:s$ : $t$ >>``
      ``MLast.CrVir loc (Ploc.VaVal True) (Ploc.VaVal s) t``
      ``<:class_str_item< method virtual private $_lid:s$ : $t$ >>``
      ``MLast.CrVir loc (Ploc.VaVal True) s t``
      ``<:class_str_item< method virtual $lid:s$ : $t$ >>``
      ``MLast.CrVir loc (Ploc.VaVal False) (Ploc.VaVal s) t``
      ``<:class_str_item< method virtual $_lid:s$ : $t$ >>``
      ``MLast.CrVir loc (Ploc.VaVal False) s t``
      ``<:class_str_item< method virtual $flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CrVir loc (Ploc.VaVal b) (Ploc.VaVal s) t``
      ``<:class_str_item< method virtual $flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CrVir loc (Ploc.VaVal b) s t``
      ``<:class_str_item< method virtual $_flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CrVir loc b (Ploc.VaVal s) t``
      ``<:class_str_item< method virtual $_flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CrVir loc b s t``

   .. rubric:: class_sig_item
      :name: class_sig_item

   - type constraint
      ``<:class_sig_item< type $t1$ = $t2$ >>``
      ``MLast.CgCtr loc t1 t2``

   - declare
      ``<:class_sig_item< declare $list:lcsi$ end >>``
      ``MLast.CgDcl loc (Ploc.VaVal lcsi)``
      ``<:class_sig_item< declare $_list:lcsi$ end >>``
      ``MLast.CgDcl loc lcsi``

   - inheritance
      ``<:class_sig_item< inherit $ct$ >>``
      ``MLast.CgInh loc ct``

   - method
      ``<:class_sig_item< method private $lid:s$ : $t$ >>``
      ``MLast.CgMth loc (Ploc.VaVal True) (Ploc.VaVal s) t``
      ``<:class_sig_item< method private $_lid:s$ : $t$ >>``
      ``MLast.CgMth loc (Ploc.VaVal True) s t``
      ``<:class_sig_item< method $lid:s$ : $t$ >>``
      ``MLast.CgMth loc (Ploc.VaVal False) (Ploc.VaVal s) t``
      ``<:class_sig_item< method $_lid:s$ : $t$ >>``
      ``MLast.CgMth loc (Ploc.VaVal False) s t``
      ``<:class_sig_item< method $flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CgMth loc (Ploc.VaVal b) (Ploc.VaVal s) t``
      ``<:class_sig_item< method $flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CgMth loc (Ploc.VaVal b) s t``
      ``<:class_sig_item< method $_flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CgMth loc b (Ploc.VaVal s) t``
      ``<:class_sig_item< method $_flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CgMth loc b s t``

   - value
      ``<:class_sig_item< value mutable $lid:s$ : $t$ >>``
      ``MLast.CgVal loc (Ploc.VaVal True) (Ploc.VaVal s) t``
      ``<:class_sig_item< value mutable $_lid:s$ : $t$ >>``
      ``MLast.CgVal loc (Ploc.VaVal True) s t``
      ``<:class_sig_item< value $lid:s$ : $t$ >>``
      ``MLast.CgVal loc (Ploc.VaVal False) (Ploc.VaVal s) t``
      ``<:class_sig_item< value $_lid:s$ : $t$ >>``
      ``MLast.CgVal loc (Ploc.VaVal False) s t``
      ``<:class_sig_item< value $flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CgVal loc (Ploc.VaVal b) (Ploc.VaVal s) t``
      ``<:class_sig_item< value $flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CgVal loc (Ploc.VaVal b) s t``
      ``<:class_sig_item< value $_flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CgVal loc b (Ploc.VaVal s) t``
      ``<:class_sig_item< value $_flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CgVal loc b s t``

   - virtual method
      ``<:class_sig_item< method virtual private $lid:s$ : $t$ >>``
      ``MLast.CgVir loc (Ploc.VaVal True) (Ploc.VaVal s) t``
      ``<:class_sig_item< method virtual private $_lid:s$ : $t$ >>``
      ``MLast.CgVir loc (Ploc.VaVal True) s t``
      ``<:class_sig_item< method virtual $lid:s$ : $t$ >>``
      ``MLast.CgVir loc (Ploc.VaVal False) (Ploc.VaVal s) t``
      ``<:class_sig_item< method virtual $_lid:s$ : $t$ >>``
      ``MLast.CgVir loc (Ploc.VaVal False) s t``
      ``<:class_sig_item< method virtual $flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CgVir loc (Ploc.VaVal b) (Ploc.VaVal s) t``
      ``<:class_sig_item< method virtual $flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CgVir loc (Ploc.VaVal b) s t``
      ``<:class_sig_item< method virtual $_flag:b$ $lid:s$ : $t$ >>``
      ``MLast.CgVir loc b (Ploc.VaVal s) t``
      ``<:class_sig_item< method virtual $_flag:b$ $_lid:s$ : $t$ >>``
      ``MLast.CgVir loc b s t``

   .. rubric:: other
      :name: other

   .. rubric:: type_decl
      :name: type_decl

   What is after 'type' or 'and' in a type declaration.

   The type "``type_decl``" is a record type corresponding to a type
   declaration. Its definition is:

   ::

        type type_decl =
          { tdNam : (loc * Ploc.vaval string);
            tdPrm : Ploc.vala (list type_var);
            tdPrv : Ploc.vala bool;
            tdDef : ctyp;
            tdCon : Ploc.vala (list (ctyp * ctyp)) }
        ;

   The field "``tdNam``" is the type identifier (together with its
   location in the source).

   The field "``tdPrm``" is the list of its possible parameters.

   The field "``tdPrv``" tells if the type is private or not.

   The field "``tdDef``" is the definition of the type.

   The field "``tdCon``" is the possible list of type constraints.

    
      ``<:type_decl< $tp:ls$ $list:ltv$ = private $t$ $list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $tp:ls$ $list:ltv$ = private $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $tp:ls$ $list:ltv$ = $t$ $list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $tp:ls$ $list:ltv$ = $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $tp:ls$ $list:ltv$ = $priv:b$ $t$ $list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $tp:ls$ $list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $tp:ls$ $list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $tp:ls$ $list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $tp:ls$ $_list:ltv$ = private $t$ $list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $tp:ls$ $_list:ltv$ = private $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $tp:ls$ $_list:ltv$ = $t$ $list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $tp:ls$ $_list:ltv$ = $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $tp:ls$ $_list:ltv$ = $priv:b$ $t$ $list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $tp:ls$ $_list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $_tp:ls$ $list:ltv$ = private $t$ $list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $_tp:ls$ $list:ltv$ = private $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $_tp:ls$ $list:ltv$ = $t$ $list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $_tp:ls$ $list:ltv$ = $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $_tp:ls$ $list:ltv$ = $priv:b$ $t$ $list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $_tp:ls$ $list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $_tp:ls$ $list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $_tp:ls$ $list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $_tp:ls$ $_list:ltv$ = private $t$ $list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $_tp:ls$ $_list:ltv$ = private $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $_tp:ls$ $_list:ltv$ = $t$ $list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $_tp:ls$ $_list:ltv$ = $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $_tp:ls$ $_list:ltv$ = $priv:b$ $t$ $list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $_tp:ls$ $_list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = ltt}``
      ``<:type_decl< $_tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}``
      ``<:type_decl< $_tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>``
      ``{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = ltt}``

   .. rubric:: with_constr
      :name: with_constr

   "With" possibly following a module type.

   - with module
      ``<:with_constr< module $list:ls$ = $me$ >>``
      ``MLast.WcMod loc (Ploc.VaVal ls) me``
      ``<:with_constr< module $_list:ls$ = $me$ >>``
      ``MLast.WcMod loc ls me``

   - with module substitution
      ``<:with_constr< module $list:ls$ := $me$ >>``
      ``MLast.WcMos loc (Ploc.VaVal ls) me``
      ``<:with_constr< module $_list:ls$ := $me$ >>``
      ``MLast.WcMos loc ls me``

   - with type
      ``<:with_constr< type $list:ls$ $list:ltv$ = private $t$ >>``
      ``MLast.WcTyp loc (Ploc.VaVal ls) (Ploc.VaVal ltv) (Ploc.VaVal True) t``
      ``<:with_constr< type $list:ls$ $list:ltv$ = $t$ >>``
      ``MLast.WcTyp loc (Ploc.VaVal ls) (Ploc.VaVal ltv) (Ploc.VaVal False) t``
      ``<:with_constr< type $list:ls$ $list:ltv$ = $flag:b$ $t$ >>``
      ``MLast.WcTyp loc (Ploc.VaVal ls) (Ploc.VaVal ltv) (Ploc.VaVal b) t``
      ``<:with_constr< type $list:ls$ $list:ltv$ = $_flag:b$ $t$ >>``
      ``MLast.WcTyp loc (Ploc.VaVal ls) (Ploc.VaVal ltv) b t``
      ``<:with_constr< type $list:ls$ $_list:ltv$ = private $t$ >>``
      ``MLast.WcTyp loc (Ploc.VaVal ls) ltv (Ploc.VaVal True) t``
      ``<:with_constr< type $list:ls$ $_list:ltv$ = $t$ >>``
      ``MLast.WcTyp loc (Ploc.VaVal ls) ltv (Ploc.VaVal False) t``
      ``<:with_constr< type $list:ls$ $_list:ltv$ = $flag:b$ $t$ >>``
      ``MLast.WcTyp loc (Ploc.VaVal ls) ltv (Ploc.VaVal b) t``
      ``<:with_constr< type $list:ls$ $_list:ltv$ = $_flag:b$ $t$ >>``
      ``MLast.WcTyp loc (Ploc.VaVal ls) ltv b t``
      ``<:with_constr< type $_list:ls$ $list:ltv$ = private $t$ >>``
      ``MLast.WcTyp loc ls (Ploc.VaVal ltv) (Ploc.VaVal True) t``
      ``<:with_constr< type $_list:ls$ $list:ltv$ = $t$ >>``
      ``MLast.WcTyp loc ls (Ploc.VaVal ltv) (Ploc.VaVal False) t``
      ``<:with_constr< type $_list:ls$ $list:ltv$ = $flag:b$ $t$ >>``
      ``MLast.WcTyp loc ls (Ploc.VaVal ltv) (Ploc.VaVal b) t``
      ``<:with_constr< type $_list:ls$ $list:ltv$ = $_flag:b$ $t$ >>``
      ``MLast.WcTyp loc ls (Ploc.VaVal ltv) b t``
      ``<:with_constr< type $_list:ls$ $_list:ltv$ = private $t$ >>``
      ``MLast.WcTyp loc ls ltv (Ploc.VaVal True) t``
      ``<:with_constr< type $_list:ls$ $_list:ltv$ = $t$ >>``
      ``MLast.WcTyp loc ls ltv (Ploc.VaVal False) t``
      ``<:with_constr< type $_list:ls$ $_list:ltv$ = $flag:b$ $t$ >>``
      ``MLast.WcTyp loc ls ltv (Ploc.VaVal b) t``
      ``<:with_constr< type $_list:ls$ $_list:ltv$ = $_flag:b$ $t$ >>``
      ``MLast.WcTyp loc ls ltv b t``

   - with type substitution
      ``<:with_constr< type $list:ls$ $list:ltv$ := $t$ >>``
      ``MLast.WcTys loc (Ploc.VaVal ls) (Ploc.VaVal ltv) t``
      ``<:with_constr< type $list:ls$ $_list:ltv$ := $t$ >>``
      ``MLast.WcTys loc (Ploc.VaVal ls) ltv t``
      ``<:with_constr< type $_list:ls$ $list:ltv$ := $t$ >>``
      ``MLast.WcTys loc ls (Ploc.VaVal ltv) t``
      ``<:with_constr< type $_list:ls$ $_list:ltv$ := $t$ >>``
      ``MLast.WcTys loc ls ltv t``

   .. rubric:: poly_variant
      :name: poly_variant

   Polymorphic variants.

   - constructor
      :literal:`<:poly_variant< `$s$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal True) (Ploc.VaVal [])``
      :literal:`<:poly_variant< `$s$ of & $list:lt$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal True) (Ploc.VaVal lt)``
      :literal:`<:poly_variant< `$s$ of & $_list:lt$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal True) lt``
      :literal:`<:poly_variant< `$s$ of $list:lt$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal False) (Ploc.VaVal lt)``
      :literal:`<:poly_variant< `$s$ of $_list:lt$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal False) lt``
      :literal:`<:poly_variant< `$s$ of $flag:b$ $list:lt$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal b) (Ploc.VaVal lt)``
      :literal:`<:poly_variant< `$s$ of $flag:b$ $_list:lt$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal b) lt``
      :literal:`<:poly_variant< `$s$ of $_flag:b$ $list:lt$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) b (Ploc.VaVal lt)``
      :literal:`<:poly_variant< `$s$ of $_flag:b$ $_list:lt$ >>`
      ``MLast.PvTag loc (Ploc.VaVal s) b lt``
      :literal:`<:poly_variant< `$_:s$ >>`
      ``MLast.PvTag loc s (Ploc.VaVal True) (Ploc.VaVal [])``
      :literal:`<:poly_variant< `$_:s$ of & $list:lt$ >>`
      ``MLast.PvTag loc s (Ploc.VaVal True) (Ploc.VaVal lt)``
      :literal:`<:poly_variant< `$_:s$ of & $_list:lt$ >>`
      ``MLast.PvTag loc s (Ploc.VaVal True) lt``
      :literal:`<:poly_variant< `$_:s$ of $list:lt$ >>`
      ``MLast.PvTag loc s (Ploc.VaVal False) (Ploc.VaVal lt)``
      :literal:`<:poly_variant< `$_:s$ of $_list:lt$ >>`
      ``MLast.PvTag loc s (Ploc.VaVal False) lt``
      :literal:`<:poly_variant< `$_:s$ of $flag:b$ $list:lt$ >>`
      ``MLast.PvTag loc s (Ploc.VaVal b) (Ploc.VaVal lt)``
      :literal:`<:poly_variant< `$_:s$ of $flag:b$ $_list:lt$ >>`
      ``MLast.PvTag loc s (Ploc.VaVal b) lt``
      :literal:`<:poly_variant< `$_:s$ of $_flag:b$ $list:lt$ >>`
      ``MLast.PvTag loc s b (Ploc.VaVal lt)``
      :literal:`<:poly_variant< `$_:s$ of $_flag:b$ $_list:lt$ >>`
      ``MLast.PvTag loc s b lt``

   - type
      ``<:poly_variant< $t$ >>``
      ``MLast.PvInh loc t``

   .. rubric:: Nodes without quotations
      :name: nodes-without-quotations

   Some types defined in the AST tree module "``MLast``" don't have an
   associated quotation. They are:

   -  ``type_var``
   -  ``class_infos``

   .. rubric:: type_var
      :name: type_var

   The type "``type_var``" is defined as:

   ::

        type type_var = (Ploc.vala string * (bool * bool));

   The first boolean is "``True``" if the type variable is prefixed by
   "``+``" ("plus" sign). The second boolean is "``True``" if the type
   variable is prefixed by "``-``" ("minus" sign).

   .. rubric:: class_infos
      :name: class_infos

   The type "``class_infos``" is a record type parametrized with a type
   variable. It is common to:

   -  the "class declaration" ("``class ...``" as structure item), the
      type variable being "``class_expr``",
   -  the "class description" ("``class ...``" as signature item), the
      type variable being "``class_type``",
   -  the "class type declaration" ("``class type ...``"), the type
      variable being "``class_type``".

   It is defined as:

   ::

        type class_infos 'a =
          { ciLoc : loc;
            ciVir : Ploc.vala bool;
            ciPrm : (loc * Ploc.vala (list type_var));
            ciNam : Ploc.vala string;
            ciExp : 'a }
        ;

   The field "``ciLoc``" is the location of the whole definition.

   The field "``ciVir``" tells whether the type is virtual or not.

   The field "``ciPrm``" is the list of its possible parameters.

   The field "``ciNam``" is the class identifier.

   The field "``ciExp``" is the class definition, depending of its kind.

   .. container:: trailer
