
.. raw:: html

   <style> .red {color:red} </style>
   <style> .blue {color:blue} </style>

.. role:: red
.. role:: blue

.. _ast_strict:

****************************
ML Syntax tree - strict mode
****************************

This chapter presents the Camlp5 syntax tree when Camlp5 is installed
in *strict* mode.

Introduction
============

This syntax tree is defined in the module ``MLast`` provided
by Camlp5. Each node corresponds to a syntactic entity of the
corresponding type.

For example, the syntax tree of the statement ``if`` can
be written:

::

  MLast.ExIfe loc e1 e2 e3


where ``loc`` is the location in the source, and ``e1``, ``e2`` and
``e3`` are respectively the expression after the ``if``, the one after
the ``then`` and the one after the ``else``.

If a program needs to manipulate syntax trees, it can use the nodes
defined in the module ``MLast``. The programmer must know how the
concrete syntax is transformed into this abstract syntax.

A simpler solution is to use one of the quotation kits
``q_MLast.cmo`` or ``q_ast.cmo``. Both propose
:ref:`quot` which represent the abstract
syntax (the nodes of the module ``MLast``) into concrete
syntax with antiquotations to bind variables inside. The example
above can be written:

::

  <:expr< if $e1$ then $e2$ else $e3$ >>


This representation is very interesting when one wants to
manipulate complicated syntax trees. Here is an example taken from
the Camlp5 sources themselves:

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

Instead of thinking of "a syntax tree", the programmer can think of "a
piece of program".


Location
========

In all syntax tree nodes, the first parameter is the source location
of the node.


In expressions
--------------

When a quotation is in the context of an expression, the location
parameter is ``loc`` in the node and in all its possible
sub-nodes. Example: if we consider the quotation:

::

  <:sig_item< value foo : int -> bool >>


This quotation, in a context of an expression, is equivalent to:

::

  MLast.SgVal loc (Ploc.VaVal "foo")
    (MLast.TyArr loc (MLast.TyLid loc (Ploc.VaVal "int"))
       (MLast.TyLid loc (Ploc.VaVal "bool")));


The name ``loc`` is predefined. However, it is possible to change it,
using the argument ``-loc`` of the Camlp5 shell commands.

Consequently, if there is no variable ``loc`` defined in the context
of the quotation, or if it is not of the good type, a semantic error
occur in the OCaml compiler (``Unbound value loc``).

Note that in the :ref:`grammars`, the variable ``loc`` is bound, in
all semantic actions, to the location of the rule.

If the created node has no location, the programmer can define a
variable named ``loc`` equal to ``Ploc.dummy``.


In patterns
-----------

When a quotation is in the context of a pattern, the location
parameter of all nodes and possible sub-nodes is set to the wildcard
(``_``). The same example above:

::

  <:sig_item< value foo : int -> bool >>


is equivalent, in a pattern, to:

::

  MLast.SgVal _ (Ploc.VaVal "foo")
    (MLast.TyArr _ (MLast.TyLid _ (Ploc.VaVal "int"))
       (MLast.TyLid _ (Ploc.VaVal "bool")))


However, it is possible to generate a binding of the variable
``loc`` on the top node by writing a "colon" before the
"less" in the quotation. The same example:

::

  <:sig_item:< value foo : int -> bool >>


is equivalent to:

::

  MLast.SgVal loc (Ploc.VaVal "foo")
    (MLast.TyArr _ (MLast.TyLid _ (Ploc.VaVal "int"))
       (MLast.TyLid _ (Ploc.VaVal "bool")))



Antiquotations
==============

The expressions or patterns between dollar ($) characters are
called *antiquotations*. In opposition to quotations which
has its own syntax rules, the antiquotation is an area in the syntax
of the enclosing context (expression or pattern). See the chapter
about :ref:`quot`.

If a quotation is in the context of an expression, the
antiquotation must be an expression. It could be any expression,
including function calls. Examples:

::

  value f e el = <:expr< [$e$ :: $loop False el$] >>;
  value patt_list p pl = <:patt< ( $list:[p::pl]$) >>;


If a quotation is in the context of an pattern, the antiquotation
is a pattern. Any pattern is possible, including the wildcard
character (``_``). Examples:

::

   fun [ <:expr< $lid:op$ $_$ $_$ >> -> op ]
   match p with [ <:patt< $_$ | $_$ >> -> Some p ]



Two kinds of antiquotations
===========================


Preliminary remark
------------------

In strict mode, we remark that most constructors defined of the
module ``MLast`` are of type ``Ploc.vala``. This type
is defined like this:

::

  type vala 'a =
    [ VaAnt of string
    | VaVal of 'a ]
  ;


The type argument is the real type of the node. For example, a
value of type ``bool`` in transitional mode is frequently
represented by a value of type ``Ploc.vala bool``.

The first case of the type ``vala`` corresponds to an
antiquotation in the concrete syntax. The second case to a normal
syntax situation, without antiquotation.

Example: in the "let" statement, the fact that it is "rec" or not
is represented by a boolean. This boolean is, in the syntax tree,
encapsulated with the type ``Ploc.vala``. The syntax tree of
the two following lines:

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


The case ``Ploc.VaAnt s`` is internally used by the parsers
and by the quotation kit ``q_ast.cmo`` to record
antiquotation strings representing the expression or the patterns
having this value. For example, in this "let" statement:

::

  MLast.ExLet loc (Ploc.VaAnt s)
    ... (* and so on *)


The contents of this ``s`` is internally handled. For
information, it contains the antiquotation string (kind included)
together with representation of the location of the antiquotation
in the quotation. See the next section.


Antiquoting
-----------

To antiquote the fact that the "let" is with or without rec (a flag
of type boolean), there are two ways.


direct antiquoting
^^^^^^^^^^^^^^^^^^

The first way, hiding the type ``Ploc.val``, can be
written with the antiquotation kind "flag":

::

  <:expr< let $flag:rf$ x = y in z >>


This corresponds to the syntax tree:

::

  MLast.ExLet loc (Ploc.VaVal rf)
     ... (* and so on *)


And, therefore, the type of the variable ``rf`` is simply
``bool``.


general antiquoting
^^^^^^^^^^^^^^^^^^^

The second way, introducing variables of type ``Ploc.vala``
can be written a kind prefixed by ``_``, namely here
``_flag``:

::

  <:expr< let $_flag:rf$ x = y in z >>


In that case, it corresponds to the syntax tree:

::

  MLast.ExLet loc rf
     ... (* and so on *)


And, therefore, the type of the variable ``rf`` is now
``Ploc.vala bool``.


Remarks
-------

The first form of antiquotation ensures the compatibility with
previous versions of Camlp5. The syntax tree is *not* the
same, but the bound variables keep the same type.

All antiquotations kinds have these two forms: one with some name
(e.g. "flag") and one with the same name prefixed by "a"
(e.g. "aflag").


Nodes and Quotations
====================

This section describes all nodes defined in the module "MLast" of
Camlp5 and how to write them with quotations. Notice that, inside
quotations, one is not restricted to these elementary cases, but
any complex value can be used, resulting on possibly complex combined
nodes.

The quotation forms are described here in :ref:`revsynt` (like the
rest of this document). In reality, it depends on which quotation kit
is loaded:


- If ``q_MLast.cmo`` is used, the revised syntax is mandatory: the
  quotations must be in that syntax without any extension.
- If ``q_ast.cmo`` is used, the quotation syntax *must* be in the
  current user syntax with all extensions added to compile the file.


Last remark: in the following tables, the variables names give
information of their types. The details can be found in the
distributed source file ``mLast.mli``.


-  ``e``, ``e1``, ``e2``, ``e3``: ``expr``
-  ``p``, ``p1``, ``p2``, ``p3``: ``patt``
-  ``t``, ``t1``, ``t2``, ``e3``: ``ctyp``
-  ``s``: ``string``
-  ``b``: ``bool``
-  ``me``, ``me1``, ``me2``: ``module_expr``
-  ``mt``, ``mt1``, ``mt2``: ``module_type``
-  ``le``: ``list expr``
-  ``lp``: ``list patt``
-  ``lt``: ``list ctyp``
-  ``ls``: ``list string``
-  ``lse``: ``list (string * expr)``
-  ``lpe``: ``list (patt * expr)``
-  ``lpp``: ``list (patt * patt)``
-  ``lpoee``: ``list (patt * option expr * expr)``
-  ``op``: ``option patt``
-  ``lcstri``: ``list class_str_item``
-  ``lcsigi``: ``list class_sig_item``



expr
----

Expressions of the language.

- access

  - :blue:`<:expr< $e1$ . $e2$ >>`
  - :red:`MLast.ExAcc loc e1 e2`

- antiquotation <a href="#expr_1">(1)</a>

  - :blue:`<:expr< $anti:e$ >>`
  - :red:`MLast.ExAnt loc e`

- application

  - :blue:`<:expr< $e1$ $e2$ >>`
  - :red:`MLast.ExApp loc e1 e2`

- array element

  - :blue:`<:expr< $e1$ .( $e2$ ) >>`
  - :red:`MLast.ExAre loc e1 e2`

- array

  - :blue:`<:expr< [| $list:le$ |] >>`
  - :red:`MLast.ExArr loc (Ploc.VaVal le)`
  - :blue:`<:expr< [| $_list:le$ |] >>`
  - :red:`MLast.ExArr loc le`

- assert

  - :blue:`<:expr< assert $e$ >>`
  - :red:`MLast.ExAsr loc e`

- assignment

  - :blue:`<:expr< $e1$ := $e2$ >>`
  - :red:`MLast.ExAss loc e1 e2`

- big array element

  - :blue:`<:expr< $e$ .{ $list:le$ } >>`
  - :red:`MLast.ExBae loc e (Ploc.VaVal le)`
  - :blue:`<:expr< $e$ .{ $_list:le$ } >>`
  - :red:`MLast.ExBae loc e le`

- character constant

  - :blue:`<:expr< $chr:s$ >>`
  - :red:`MLast.ExChr loc (Ploc.VaVal s)`
  - :blue:`<:expr< $_chr:s$ >>`
  - :red:`MLast.ExChr loc s`

- coercion

  - :blue:`<:expr< ($e$ :> $t2$) >>`
  - :red:`MLast.ExCoe loc e None t2`
  - :blue:`<:expr< ($e$ : $t1$ :> $t2$) >>`
  - :red:`MLast.ExCoe loc e (Some t1) t2`

- float constant

  - :blue:`<:expr< $flo:s$ >>`
  - :red:`MLast.ExFlo loc (Ploc.VaVal s)`
  - :blue:`<:expr< $_flo:s$ >>`
  - :red:`MLast.ExFlo loc s`

- for (increasing)

  - :blue:`<:expr< for $lid:s$ = $e1$ to $e2$ do { $list:le$ } >>`
  - :red:`MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal True) (Ploc.VaVal le)`
  - :blue:`<:expr< for $lid:s$ = $e1$ to $e2$ do { $_list:le$ } >>`
  - :red:`MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal True) le`

- for (decreasing)

  - :blue:`<:expr< for $lid:s$ = $e1$ downto $e2$ do { $list:le$ } >>`
  - :red:`MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal False) (Ploc.VaVal le)`
  - :blue:`<:expr< for $lid:s$ = $e1$ downto $e2$ do { $_list:le$ } >>`
  - :red:`MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal False) le`

- for

  - :blue:`<:expr< for $lid:s$ = $e1$ $to:b$ $e2$ do { $list:le$ } >>`
  - :red:`MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal b) (Ploc.VaVal le)`
  - :blue:`<:expr< for $lid:s$ = $e1$ $to:b$ $e2$ do { $_list:le$ } >>`
  - :red:`MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal b) le`
  - :blue:`<:expr< for $lid:s$ = $e1$ $_to:b$ $e2$ do { $list:le$ } >>`
  - :red:`MLast.ExFor loc (Ploc.VaVal s) e1 e2 b (Ploc.VaVal le)`
  - :blue:`<:expr< for $lid:s$ = $e1$ $_to:b$ $e2$ do { $_list:le$ } >>`
  - :red:`MLast.ExFor loc (Ploc.VaVal s) e1 e2 b le`
  - :blue:`<:expr< for $_lid:s$ = $e1$ to $e2$ do { $list:le$ } >>`
  - :red:`MLast.ExFor loc s e1 e2 (Ploc.VaVal True) (Ploc.VaVal le)`
  - :blue:`<:expr< for $_lid:s$ = $e1$ to $e2$ do { $_list:le$ } >>`
  - :red:`MLast.ExFor loc s e1 e2 (Ploc.VaVal True) le`
  - :blue:`<:expr< for $_lid:s$ = $e1$ downto $e2$ do { $list:le$ } >>`
  - :red:`MLast.ExFor loc s e1 e2 (Ploc.VaVal False) (Ploc.VaVal le)`
  - :blue:`<:expr< for $_lid:s$ = $e1$ downto $e2$ do { $_list:le$ } >>`
  - :red:`MLast.ExFor loc s e1 e2 (Ploc.VaVal False) le`
  - :blue:`<:expr< for $_lid:s$ = $e1$ $to:b$ $e2$ do { $list:le$ } >>`
  - :red:`MLast.ExFor loc s e1 e2 (Ploc.VaVal b) (Ploc.VaVal le)`
  - :blue:`<:expr< for $_lid:s$ = $e1$ $to:b$ $e2$ do { $_list:le$ } >>`
  - :red:`MLast.ExFor loc s e1 e2 (Ploc.VaVal b) le`
  - :blue:`<:expr< for $_lid:s$ = $e1$ $_to:b$ $e2$ do { $list:le$ } >>`
  - :red:`MLast.ExFor loc s e1 e2 b (Ploc.VaVal le)`
  - :blue:`<:expr< for $_lid:s$ = $e1$ $_to:b$ $e2$ do { $_list:le$ } >>`
  - :red:`MLast.ExFor loc s e1 e2 b le`

- function

  - :blue:`<:expr< fun [ $list:lpee$ ] >>`
  - :red:`MLast.ExFun loc (Ploc.VaVal lpee)`
  - :blue:`<:expr< fun [ $_list:lpee$ ] >>`
  - :red:`MLast.ExFun loc lpee`

- if

  - :blue:`<:expr< if $e1$ then $e2$ else $e3$ >>`
  - :red:`MLast.ExIfe loc e1 e2 e3`

- integer constant

  - :blue:`<:expr< $int:s1$ >>`
  - :red:`MLast.ExInt loc (Ploc.VaVal s1) ""`
  - :blue:`<:expr< $_int:s1$ >>`
  - :red:`MLast.ExInt loc s1 ""`

- integer 32 bits

  - :blue:`<:expr< $int32:s1$ >>`
  - :red:`MLast.ExInt loc (Ploc.VaVal s1) "l"`
  - :blue:`<:expr< $_int32:s1$ >>`
  - :red:`MLast.ExInt loc s1 "l"`

- integer 64 bits

  - :blue:`<:expr< $int64:s1$ >>`
  - :red:`MLast.ExInt loc (Ploc.VaVal s1) "L"`
  - :blue:`<:expr< $_int64:s1$ >>`
  - :red:`MLast.ExInt loc s1 "L"`

- native integer

  - :blue:`<:expr< $nativeint:s1$ >>`
  - :red:`MLast.ExInt loc (Ploc.VaVal s1) "n"`
  - :blue:`<:expr< $_nativeint:s1$ >>`
  - :red:`MLast.ExInt loc s1 "n"`

- label

  - :blue:`<:expr< ~{$p$} >>`
  - :red:`MLast.ExLab loc p (Ploc.VaVal None)`
  - :blue:`<:expr< ~{$p$ = $e$} >>`
  - :red:`MLast.ExLab loc p (Ploc.VaVal (Some e))`
  - :blue:`<:expr< ~{$p$ $opt:oe$} >>`
  - :red:`MLast.ExLab loc p (Ploc.VaVal oe)`
  - :blue:`<:expr< ~{$p$ $_opt:oe$} >>`
  - :red:`MLast.ExLab loc p oe`

- lazy

  - :blue:`<:expr< lazy $e$ >>`
  - :red:`MLast.ExLaz loc e`

- let rec

  - :blue:`<:expr< let rec $list:lpe$ in $e$ >>`
  - :red:`MLast.ExLet loc (Ploc.VaVal True) (Ploc.VaVal lpe) e`
  - :blue:`<:expr< let rec $_list:lpe$ in $e$ >>`
  - :red:`MLast.ExLet loc (Ploc.VaVal True) lpe e`

- let not rec

  - :blue:`<:expr< let $list:lpe$ in $e$ >>`
  - :red:`MLast.ExLet loc (Ploc.VaVal False) (Ploc.VaVal lpe) e`
  - :blue:`<:expr< let $_list:lpe$ in $e$ >>`
  - :red:`MLast.ExLet loc (Ploc.VaVal False) lpe e`

- let

  - :blue:`<:expr< let $flag:b$ $list:lpe$ in $e$ >>`
  - :red:`MLast.ExLet loc (Ploc.VaVal b) (Ploc.VaVal lpe) e`
  - :blue:`<:expr< let $flag:b$ $_list:lpe$ in $e$ >>`
  - :red:`MLast.ExLet loc (Ploc.VaVal b) lpe e`
  - :blue:`<:expr< let $_flag:b$ $list:lpe$ in $e$ >>`
  - :red:`MLast.ExLet loc b (Ploc.VaVal lpe) e`
  - :blue:`<:expr< let $_flag:b$ $_list:lpe$ in $e$ >>`
  - :red:`MLast.ExLet loc b lpe e`

- lowercase identifier

  - :blue:`<:expr< $lid:s$ >>`
  - :red:`MLast.ExLid loc (Ploc.VaVal s)`
  - :blue:`<:expr< $_lid:s$ >>`
  - :red:`MLast.ExLid loc s`

- let module

  - :blue:`<:expr< let module $uid:s$ = $me$ in $e$ >>`
  - :red:`MLast.ExLmd loc (Ploc.VaVal s) me e`
  - :blue:`<:expr< let module $_uid:s$ = $me$ in $e$ >>`
  - :red:`MLast.ExLmd loc s me e`

- match

  - :blue:`<:expr< match $e$ with [ $list:lpee$ ] >>`
  - :red:`MLast.ExMat loc e (Ploc.VaVal lpee)`
  - :blue:`<:expr< match $e$ with [ $_list:lpee$ ] >>`
  - :red:`MLast.ExMat loc e lpee`

- new

  - :blue:`<:expr< new $list:ls$ >>`
  - :red:`MLast.ExNew loc (Ploc.VaVal ls)`
  - :blue:`<:expr< new $_list:ls$ >>`
  - :red:`MLast.ExNew loc ls`

- object expression

  - :blue:`<:expr< object $list:lcsi$ end >>`
  - :red:`MLast.ExObj loc (Ploc.VaVal None) (Ploc.VaVal lcsi)`
  - :blue:`<:expr< object $_list:lcsi$ end >>`
  - :red:`MLast.ExObj loc (Ploc.VaVal None) lcsi`
  - :blue:`<:expr< object ($p$) $list:lcsi$ end >>`
  - :red:`MLast.ExObj loc (Ploc.VaVal (Some p)) (Ploc.VaVal lcsi)`
  - :blue:`<:expr< object ($p$) $_list:lcsi$ end >>`
  - :red:`MLast.ExObj loc (Ploc.VaVal (Some p)) lcsi`
  - :blue:`<:expr< object $opt:op$ $list:lcsi$ end >>`
  - :red:`MLast.ExObj loc (Ploc.VaVal op) (Ploc.VaVal lcsi)`
  - :blue:`<:expr< object $opt:op$ $_list:lcsi$ end >>`
  - :red:`MLast.ExObj loc (Ploc.VaVal op) lcsi`
  - :blue:`<:expr< object $_opt:op$ $list:lcsi$ end >>`
  - :red:`MLast.ExObj loc op (Ploc.VaVal lcsi)`
  - :blue:`<:expr< object $_opt:op$ $_list:lcsi$ end >>`
  - :red:`MLast.ExObj loc op lcsi`

- option label

  - :blue:`<:expr< ?{$p$} >>`
  - :red:`MLast.ExOlb loc p (Ploc.VaVal None)`
  - :blue:`<:expr< ?{$p$ = $e$} >>`
  - :red:`MLast.ExOlb loc p (Ploc.VaVal (Some e))`
  - :blue:`<:expr< ?{$p$ $opt:oe$} >>`
  - :red:`MLast.ExOlb loc p (Ploc.VaVal oe)`
  - :blue:`<:expr< ?{$p$ $_opt:oe$} >>`
  - :red:`MLast.ExOlb loc p oe`

- override

  - :blue:`<:expr< {< $list:lse$ >} >>`
  - :red:`MLast.ExOvr loc (Ploc.VaVal lse)`
  - :blue:`<:expr< {< $_list:lse$ >} >>`
  - :red:`MLast.ExOvr loc lse`

- module packing

  - :blue:`<:expr< (module $me$) >>`
  - :red:`MLast.ExPck loc me None`
  - :blue:`<:expr< (module $me$ : $mt$) >>`
  - :red:`MLast.ExPck loc me (Some mt)`

- record

  - :blue:`<:expr< {$list:lpe$} >>`
  - :red:`MLast.ExRec loc (Ploc.VaVal lpe) None`
  - :blue:`<:expr< {($e$) with $list:lpe$} >>`
  - :red:`MLast.ExRec loc (Ploc.VaVal lpe) (Some e)`
  - :blue:`<:expr< {$_list:lpe$} >>`
  - :red:`MLast.ExRec loc lpe None`
  - :blue:`<:expr< {($e$) with $_list:lpe$} >>`
  - :red:`MLast.ExRec loc lpe (Some e)`

- sequence

  - :blue:`<:expr< do { $list:le$ } >>`
  - :red:`MLast.ExSeq loc (Ploc.VaVal le)`
  - :blue:`<:expr< do { $_list:le$ } >>`
  - :red:`MLast.ExSeq loc le`

- method call

  - :blue:`<:expr< $e$ # $s$ >>`
  - :red:`MLast.ExSnd loc e (Ploc.VaVal s)`
  - :blue:`<:expr< $e$ # $_:s$ >>`
  - :red:`MLast.ExSnd loc e s`

- string element

  - :blue:`<:expr< $e1$ .[ $e2$ ] >>`
  - :red:`MLast.ExSte loc e1 e2`

- string

  - :blue:`<:expr< $str:s$ >>`
  - :red:`MLast.ExStr loc (Ploc.VaVal s)`
  - :blue:`<:expr< $_str:s$ >>`
  - :red:`MLast.ExStr loc s`

- try

  - :blue:`<:expr< try $e$ with [ $list:lpee$ ] >>`
  - :red:`MLast.ExTry loc e (Ploc.VaVal lpee)`
  - :blue:`<:expr< try $e$ with [ $_list:lpee$ ] >>`
  - :red:`MLast.ExTry loc e lpee`

- t-uple

  - :blue:`<:expr< ($list:le$) >>`
  - :red:`MLast.ExTup loc (Ploc.VaVal le)`
  - :blue:`<:expr< ($_list:le$) >>`
  - :red:`MLast.ExTup loc le`

- type constraint

  - :blue:`<:expr< ($e$ : $t$) >>`
  - :red:`MLast.ExTyc loc e t`

- uppercase identifier

  - :blue:`<:expr< $uid:s$ >>`
  - :red:`MLast.ExUid loc (Ploc.VaVal s)`
  - :blue:`<:expr< $_uid:s$ >>`
  - :red:`MLast.ExUid loc s`

- variant

  - :blue:`<:expr< ` $s$ >>`
  - :red:`MLast.ExVrn loc (Ploc.VaVal s)`
  - :blue:`<:expr< ` $_:s$ >>`
  - :red:`MLast.ExVrn loc s`

- while

  - :blue:`<:expr< while $e$ do { $list:le$ } >>`
  - :red:`MLast.ExWhi loc e (Ploc.VaVal le)`
  - :blue:`<:expr< while $e$ do { $_list:le$ } >>`
  - :red:`MLast.ExWhi loc e le`

- extra node <a href="#expr_2">(2)</a>

  - :blue:`... no representation ...`
  - :red:`MLast.ExXtr loc s oe`


1. Node used in the quotation expanders to tells at conversion to
OCaml compiler syntax tree time, that all locations of the
sub-tree is correcty located in the quotation. By default, in
quotations, the locations of all generated nodes are the location
of the whole quotation. This node allows to make an exception to
this rule, since we know that the antiquotation belongs to the
universe of the enclosing program. See the chapter
about :ref:`quot` and, in particular, its
section about antiquotations.

2. Extra node internally used by the quotation kit
``q_ast.cmo`` to build antiquotations of expressions.

patt
----

Patterns of the language.

- access

  - :blue:`<:patt< $p1$ . $p2$ >>`
  - :red:`MLast.PaAcc loc p1 p2`

- alias

  - :blue:`<:patt< ($p1$ as $p2$) >>`
  - :red:`MLast.PaAli loc p1 p2`

- antiquotation <a href="#patt_1">(1)</a>

  - :blue:`<:patt< $anti:p$ >>`
  - :red:`MLast.PaAnt loc p`

- wildcard

  - :blue:`<:patt< _ >>`
  - :red:`MLast.PaAny loc`

- application

  - :blue:`<:patt< $p1$ $p2$ >>`
  - :red:`MLast.PaApp loc p1 p2`

- array

  - :blue:`<:patt< [| $list:lp$ |] >>`
  - :red:`MLast.PaArr loc (Ploc.VaVal lp)`
  - :blue:`<:patt< [| $_list:lp$ |] >>`
  - :red:`MLast.PaArr loc lp`

- character

  - :blue:`<:patt< $chr:s$ >>`
  - :red:`MLast.PaChr loc (Ploc.VaVal s)`
  - :blue:`<:patt< $_chr:s$ >>`
  - :red:`MLast.PaChr loc s`

- float

  - :blue:`<:patt< $flo:s$ >>`
  - :red:`MLast.PaFlo loc (Ploc.VaVal s)`
  - :blue:`<:patt< $_flo:s$ >>`
  - :red:`MLast.PaFlo loc s`

- integer constant

  - :blue:`<:patt< $int:s1$ >>`
  - :red:`MLast.PaInt loc (Ploc.VaVal s1) ""`
  - :blue:`<:patt< $_int:s1$ >>`
  - :red:`MLast.PaInt loc s1 ""`

- integer 32 bits

  - :blue:`<:patt< $int32:s1$ >>`
  - :red:`MLast.PaInt loc (Ploc.VaVal s1) "l"`
  - :blue:`<:patt< $_int32:s1$ >>`
  - :red:`MLast.PaInt loc s1 "l"`

- integer 64 bits

  - :blue:`<:patt< $int64:s1$ >>`
  - :red:`MLast.PaInt loc (Ploc.VaVal s1) "L"`
  - :blue:`<:patt< $_int64:s1$ >>`
  - :red:`MLast.PaInt loc s1 "L"`

- native integer

  - :blue:`<:patt< $nativeint:s1$ >>`
  - :red:`MLast.PaInt loc (Ploc.VaVal s1) "n"`
  - :blue:`<:patt< $_nativeint:s1$ >>`
  - :red:`MLast.PaInt loc s1 "n"`

- label

  - :blue:`<:patt< ~{$p1$} >>`
  - :red:`MLast.PaLab loc p1 (Ploc.VaVal None)`
  - :blue:`<:patt< ~{$p1$ = $p2$} >>`
  - :red:`MLast.PaLab loc p1 (Ploc.VaVal (Some p2))`
  - :blue:`<:patt< ~{$p1$ $opt:op2$} >>`
  - :red:`MLast.PaLab loc p1 (Ploc.VaVal op2)`
  - :blue:`<:patt< ~{$p1$ $_opt:op2$} >>`
  - :red:`MLast.PaLab loc p1 op2`

- lazy

  - :blue:`<:patt< lazy $p$ >>`
  - :red:`MLast.PaLaz loc p`

- lowercase identifier

  - :blue:`<:patt< $lid:s$ >>`
  - :red:`MLast.PaLid loc (Ploc.VaVal s)`
  - :blue:`<:patt< $_lid:s$ >>`
  - :red:`MLast.PaLid loc s`

- new type

  - :blue:`<:patt< (type $lid:s$) >>`
  - :red:`MLast.PaNty loc (Ploc.VaVal s)`
  - :blue:`<:patt< (type $_lid:s$) >>`
  - :red:`MLast.PaNty loc s`

- option label

  - :blue:`<:patt< ?{$p$} >>`
  - :red:`MLast.PaOlb loc p (Ploc.VaVal None)`
  - :blue:`<:patt< ?{$p$ = $e$} >>`
  - :red:`MLast.PaOlb loc p (Ploc.VaVal (Some e))`
  - :blue:`<:patt< ?{$p$ $opt:oe$} >>`
  - :red:`MLast.PaOlb loc p (Ploc.VaVal oe)`
  - :blue:`<:patt< ?{$p$ $_opt:oe$} >>`
  - :red:`MLast.PaOlb loc p oe`

- or

  - :blue:`<:patt< $p1$ | $p2$ >>`
  - :red:`MLast.PaOrp loc p1 p2`

- record

  - :blue:`<:patt< { $list:lpp$ } >>`
  - :red:`MLast.PaRec loc (Ploc.VaVal lpp)`
  - :blue:`<:patt< { $_list:lpp$ } >>`
  - :red:`MLast.PaRec loc lpp`

- range

  - :blue:`<:patt< $p1$ .. $p2$ >>`
  - :red:`MLast.PaRng loc p1 p2`

- string

  - :blue:`<:patt< $str:s$ >>`
  - :red:`MLast.PaStr loc (Ploc.VaVal s)`
  - :blue:`<:patt< $_str:s$ >>`
  - :red:`MLast.PaStr loc s`

- t-uple

  - :blue:`<:patt< ($list:lp$) >>`
  - :red:`MLast.PaTup loc (Ploc.VaVal lp)`
  - :blue:`<:patt< ($_list:lp$) >>`
  - :red:`MLast.PaTup loc lp`

- type constraint

  - :blue:`<:patt< ($p$ : $t$) >>`
  - :red:`MLast.PaTyc loc p t`

- type pattern

  - :blue:`<:patt< # $list:ls$ >>`
  - :red:`MLast.PaTyp loc (Ploc.VaVal ls)`
  - :blue:`<:patt< # $_list:ls$ >>`
  - :red:`MLast.PaTyp loc ls`

- uppercase identifier

  - :blue:`<:patt< $uid:s$ >>`
  - :red:`MLast.PaUid loc (Ploc.VaVal s)`
  - :blue:`<:patt< $_uid:s$ >>`
  - :red:`MLast.PaUid loc s`

- module unpacking

  - :blue:`<:patt< (module $uid:s$) >>`
  - :red:`MLast.PaUnp loc (Ploc.VaVal s) None`
  - :blue:`<:patt< (module $uid:s$ : $mt$) >>`
  - :red:`MLast.PaUnp loc (Ploc.VaVal s) (Some mt)`
  - :blue:`<:patt< (module $_uid:s$) >>`
  - :red:`MLast.PaUnp loc s None`
  - :blue:`<:patt< (module $_uid:s$ : $mt$) >>`
  - :red:`MLast.PaUnp loc s (Some mt)`

- variant

  - :blue:`<:patt< ` $s$ >>`
  - :red:`MLast.PaVrn loc (Ploc.VaVal s)`
  - :blue:`<:patt< ` $_:s$ >>`
  - :red:`MLast.PaVrn loc s`

- extra node <a href="#patt_2">(2)</a>

  - :blue:`... no representation ...`
  - :red:`MLast.PaXtr loc s op`


1. Node used to specify an antiquotation area, like for the equivalent
node in expressions. See above.


2. Extra node internally used by the quotation kit ``q_ast.cmo`` to
build antiquotations of patterns.

ctyp
----

Type expressions of the language.

- access

  - :blue:`<:ctyp< $t1$ . $t2$ >>`
  - :red:`MLast.TyAcc loc t1 t2`

- alias

  - :blue:`<:ctyp< $t1$ as $t2$ >>`
  - :red:`MLast.TyAli loc t1 t2`

- wildcard

  - :blue:`<:ctyp< _ >>`
  - :red:`MLast.TyAny loc`

- application

  - :blue:`<:ctyp< $t1$ $t2$ >>`
  - :red:`MLast.TyApp loc t1 t2`

- arrow

  - :blue:`<:ctyp< $t1$ -> $t2$ >>`
  - :red:`MLast.TyArr loc t1 t2`

- class

  - :blue:`<:ctyp< # $list:ls$ >>`
  - :red:`MLast.TyCls loc (Ploc.VaVal ls)`
  - :blue:`<:ctyp< # $_list:ls$ >>`
  - :red:`MLast.TyCls loc ls`

- label

  - :blue:`<:ctyp< ~$s$: $t$ >>`
  - :red:`MLast.TyLab loc (Ploc.VaVal s) t`
  - :blue:`<:ctyp< ~$_:s$: $t$ >>`
  - :red:`MLast.TyLab loc s t`

- lowercase identifier

  - :blue:`<:ctyp< $lid:s$ >>`
  - :red:`MLast.TyLid loc (Ploc.VaVal s)`
  - :blue:`<:ctyp< $_lid:s$ >>`
  - :red:`MLast.TyLid loc s`

- manifest

  - :blue:`<:ctyp< $t1$ == private $t2$ >>`
  - :red:`MLast.TyMan loc t1 (Ploc.VaVal True) t2`
  - :blue:`<:ctyp< $t1$ == $t2$ >>`
  - :red:`MLast.TyMan loc t1 (Ploc.VaVal False) t2`
  - :blue:`<:ctyp< $t1$ == $priv:b$ $t2$ >>`
  - :red:`MLast.TyMan loc t1 (Ploc.VaVal b) t2`
  - :blue:`<:ctyp< $t1$ == $_priv:b$ $t2$ >>`
  - :red:`MLast.TyMan loc t1 b t2`

- object

  - :blue:`<:ctyp< < $list:lst$ .. > >>`
  - :red:`MLast.TyObj loc (Ploc.VaVal lst) (Ploc.VaVal True)`
  - :blue:`<:ctyp< < $list:lst$ > >>`
  - :red:`MLast.TyObj loc (Ploc.VaVal lst) (Ploc.VaVal False)`
  - :blue:`<:ctyp< < $list:lst$ $flag:b$ > >>`
  - :red:`MLast.TyObj loc (Ploc.VaVal lst) (Ploc.VaVal b)`
  - :blue:`<:ctyp< < $list:lst$ $_flag:b$ > >>`
  - :red:`MLast.TyObj loc (Ploc.VaVal lst) b`
  - :blue:`<:ctyp< < $_list:lst$ .. > >>`
  - :red:`MLast.TyObj loc lst (Ploc.VaVal True)`
  - :blue:`<:ctyp< < $_list:lst$ > >>`
  - :red:`MLast.TyObj loc lst (Ploc.VaVal False)`
  - :blue:`<:ctyp< < $_list:lst$ $flag:b$ > >>`
  - :red:`MLast.TyObj loc lst (Ploc.VaVal b)`
  - :blue:`<:ctyp< < $_list:lst$ $_flag:b$ > >>`
  - :red:`MLast.TyObj loc lst b`

- option label

  - :blue:`<:ctyp< ?$s$: $t$ >>`
  - :red:`MLast.TyOlb loc (Ploc.VaVal s) t`
  - :blue:`<:ctyp< ?$_:s$: $t$ >>`
  - :red:`MLast.TyOlb loc s t`

- package

  - :blue:`<:ctyp< (module $mt$) >>`
  - :red:`MLast.TyPck loc mt`

- polymorph

  - :blue:`<:ctyp< ! $list:ls$ . $t$ >>`
  - :red:`MLast.TyPol loc (Ploc.VaVal ls) t`
  - :blue:`<:ctyp< ! $_list:ls$ . $t$ >>`
  - :red:`MLast.TyPol loc ls t`

- variable

  - :blue:`<:ctyp< '$s$ >>`
  - :red:`MLast.TyQuo loc (Ploc.VaVal s)`
  - :blue:`<:ctyp< '$_:s$ >>`
  - :red:`MLast.TyQuo loc s`

- record

  - :blue:`<:ctyp< { $list:llsbt$ } >>`
  - :red:`MLast.TyRec loc (Ploc.VaVal llsbt)`
  - :blue:`<:ctyp< { $_list:llsbt$ } >>`
  - :red:`MLast.TyRec loc llsbt`

- sum

  - :blue:`<:ctyp< [ $list:llslt$ ] >>`
  - :red:`MLast.TySum loc (Ploc.VaVal llslt)`
  - :blue:`<:ctyp< [ $_list:llslt$ ] >>`
  - :red:`MLast.TySum loc llslt`

- t-uple

  - :blue:`<:ctyp< ( $list:lt$ ) >>`
  - :red:`MLast.TyTup loc (Ploc.VaVal lt)`
  - :blue:`<:ctyp< ( $_list:lt$ ) >>`
  - :red:`MLast.TyTup loc lt`

- uppercase identifier

  - :blue:`<:ctyp< $uid:s$ >>`
  - :red:`MLast.TyUid loc (Ploc.VaVal s)`
  - :blue:`<:ctyp< $_uid:s$ >>`
  - :red:`MLast.TyUid loc s`

- variant

  - :blue:`<:ctyp< [ = $list:lpv$ ] >>`
  - :red:`MLast.TyVrn loc (Ploc.VaVal lpv) None`
  - :blue:`<:ctyp< [ > $list:lpv$ ] >>`
  - :red:`MLast.TyVrn loc (Ploc.VaVal lpv) (Some None)`
  - :blue:`<:ctyp< [ < $list:lpv$ ] >>`
  - :red:`MLast.TyVrn loc (Ploc.VaVal lpv) (Some (Some (Ploc.VaVal [])))`
  - :blue:`<:ctyp< [ < $list:lpv$ > $list:ls$ ] >>`
  - :red:`MLast.TyVrn loc (Ploc.VaVal lpv) (Some (Some (Ploc.VaVal ls)))`
  - :blue:`<:ctyp< [ < $list:lpv$ > $_list:ls$ ] >>`
  - :red:`MLast.TyVrn loc (Ploc.VaVal lpv) (Some (Some ls))`
  - :blue:`<:ctyp< [ = $_list:lpv$ ] >>`
  - :red:`MLast.TyVrn loc lpv None`
  - :blue:`<:ctyp< [ > $_list:lpv$ ] >>`
  - :red:`MLast.TyVrn loc lpv (Some None)`
  - :blue:`<:ctyp< [ < $_list:lpv$ ] >>`
  - :red:`MLast.TyVrn loc lpv (Some (Some (Ploc.VaVal [])))`
  - :blue:`<:ctyp< [ < $_list:lpv$ > $list:ls$ ] >>`
  - :red:`MLast.TyVrn loc lpv (Some (Some (Ploc.VaVal ls)))`
  - :blue:`<:ctyp< [ < $_list:lpv$ > $_list:ls$ ] >>`
  - :red:`MLast.TyVrn loc lpv (Some (Some ls))`

- extra node <a href="#ctyp_1">(1)</a>

  - :blue:`... no representation ...`
  - :red:`MLast.TyXtr loc s ot`


1. Extra node internally used by the quotation kit ``q_ast.cmo`` to
build antiquotations of types.

modules...
----------


str_item
^^^^^^^^

Structure items, i.e. phrases in a ".ml" file or "struct"
elements.

- class declaration

  - :blue:`<:str_item< class $list:lcice$ >>`
  - :red:`MLast.StCls loc (Ploc.VaVal lcice)`
  - :blue:`<:str_item< class $_list:lcice$ >>`
  - :red:`MLast.StCls loc lcice`

- class type declaration

  - :blue:`<:str_item< class type $list:lcict$ >>`
  - :red:`MLast.StClt loc (Ploc.VaVal lcict)`
  - :blue:`<:str_item< class type $_list:lcict$ >>`
  - :red:`MLast.StClt loc lcict`

- declare

  - :blue:`<:str_item< declare $list:lsi$ end >>`
  - :red:`MLast.StDcl loc (Ploc.VaVal lsi)`
  - :blue:`<:str_item< declare $_list:lsi$ end >>`
  - :red:`MLast.StDcl loc lsi`

- directive

  - :blue:`<:str_item< # $lid:s$ >>`
  - :red:`MLast.StDir loc (Ploc.VaVal s) (Ploc.VaVal None)`
  - :blue:`<:str_item< # $lid:s$ $e$ >>`
  - :red:`MLast.StDir loc (Ploc.VaVal s) (Ploc.VaVal (Some e))`
  - :blue:`<:str_item< # $lid:s$ $opt:oe$ >>`
  - :red:`MLast.StDir loc (Ploc.VaVal s) (Ploc.VaVal oe)`
  - :blue:`<:str_item< # $lid:s$ $_opt:oe$ >>`
  - :red:`MLast.StDir loc (Ploc.VaVal s) oe`
  - :blue:`<:str_item< # $_lid:s$ >>`
  - :red:`MLast.StDir loc s (Ploc.VaVal None)`
  - :blue:`<:str_item< # $_lid:s$ $e$ >>`
  - :red:`MLast.StDir loc s (Ploc.VaVal (Some e))`
  - :blue:`<:str_item< # $_lid:s$ $opt:oe$ >>`
  - :red:`MLast.StDir loc s (Ploc.VaVal oe)`
  - :blue:`<:str_item< # $_lid:s$ $_opt:oe$ >>`
  - :red:`MLast.StDir loc s oe`

- exception

  - :blue:`<:str_item< exception $uid:s$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal []) (Ploc.VaVal [])`
  - :blue:`<:str_item< exception $uid:s$ of $list:lt$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal lt) (Ploc.VaVal [])`
  - :blue:`<:str_item< exception $uid:s$ = $list:ls$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal []) (Ploc.VaVal ls)`
  - :blue:`<:str_item< exception $uid:s$ of $list:lt$ = $list:ls$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal lt) (Ploc.VaVal ls)`
  - :blue:`<:str_item< exception $uid:s$ = $_list:ls$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal []) ls`
  - :blue:`<:str_item< exception $uid:s$ of $list:lt$ = $_list:ls$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal lt) ls`
  - :blue:`<:str_item< exception $uid:s$ of $_list:lt$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) lt (Ploc.VaVal [])`
  - :blue:`<:str_item< exception $uid:s$ of $_list:lt$ = $list:ls$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) lt (Ploc.VaVal ls)`
  - :blue:`<:str_item< exception $uid:s$ of $_list:lt$ = $_list:ls$ >>`
  - :red:`MLast.StExc loc (Ploc.VaVal s) lt ls`
  - :blue:`<:str_item< exception $_uid:s$ >>`
  - :red:`MLast.StExc loc s (Ploc.VaVal []) (Ploc.VaVal [])`
  - :blue:`<:str_item< exception $_uid:s$ of $list:lt$ >>`
  - :red:`MLast.StExc loc s (Ploc.VaVal lt) (Ploc.VaVal [])`
  - :blue:`<:str_item< exception $_uid:s$ = $list:ls$ >>`
  - :red:`MLast.StExc loc s (Ploc.VaVal []) (Ploc.VaVal ls)`
  - :blue:`<:str_item< exception $_uid:s$ of $list:lt$ = $list:ls$ >>`
  - :red:`MLast.StExc loc s (Ploc.VaVal lt) (Ploc.VaVal ls)`
  - :blue:`<:str_item< exception $_uid:s$ = $_list:ls$ >>`
  - :red:`MLast.StExc loc s (Ploc.VaVal []) ls`
  - :blue:`<:str_item< exception $_uid:s$ of $list:lt$ = $_list:ls$ >>`
  - :red:`MLast.StExc loc s (Ploc.VaVal lt) ls`
  - :blue:`<:str_item< exception $_uid:s$ of $_list:lt$ >>`
  - :red:`MLast.StExc loc s lt (Ploc.VaVal [])`
  - :blue:`<:str_item< exception $_uid:s$ of $_list:lt$ = $list:ls$ >>`
  - :red:`MLast.StExc loc s lt (Ploc.VaVal ls)`
  - :blue:`<:str_item< exception $_uid:s$ of $_list:lt$ = $_list:ls$ >>`
  - :red:`MLast.StExc loc s lt ls`

- expression

  - :blue:`<:str_item< $exp:e$ >>`
  - :red:`MLast.StExp loc e`

- external

  - :blue:`<:str_item< external $s$ : $t$ = $list:ls$ >>`
  - :red:`MLast.StExt loc (Ploc.VaVal s) t (Ploc.VaVal ls)`
  - :blue:`<:str_item< external $s$ : $t$ = $_list:ls$ >>`
  - :red:`MLast.StExt loc (Ploc.VaVal s) t ls`
  - :blue:`<:str_item< external $_:s$ : $t$ = $list:ls$ >>`
  - :red:`MLast.StExt loc s t (Ploc.VaVal ls)`
  - :blue:`<:str_item< external $_:s$ : $t$ = $_list:ls$ >>`
  - :red:`MLast.StExt loc s t ls`

- include

  - :blue:`<:str_item< include $me$ >>`
  - :red:`MLast.StInc loc me`

- module rec

  - :blue:`<:str_item< module rec $list:lsme$ >>`
  - :red:`MLast.StMod loc (Ploc.VaVal True) (Ploc.VaVal lsme)`
  - :blue:`<:str_item< module rec $_list:lsme$ >>`
  - :red:`MLast.StMod loc (Ploc.VaVal True) lsme`

- module non rec

  - :blue:`<:str_item< module $list:lsme$ >>`
  - :red:`MLast.StMod loc (Ploc.VaVal False) (Ploc.VaVal lsme)`
  - :blue:`<:str_item< module $_list:lsme$ >>`
  - :red:`MLast.StMod loc (Ploc.VaVal False) lsme`

- module

  - :blue:`<:str_item< module $flag:b$ $list:lsme$ >>`
  - :red:`MLast.StMod loc (Ploc.VaVal b) (Ploc.VaVal lsme)`
  - :blue:`<:str_item< module $flag:b$ $_list:lsme$ >>`
  - :red:`MLast.StMod loc (Ploc.VaVal b) lsme`
  - :blue:`<:str_item< module $_flag:b$ $list:lsme$ >>`
  - :red:`MLast.StMod loc b (Ploc.VaVal lsme)`
  - :blue:`<:str_item< module $_flag:b$ $_list:lsme$ >>`
  - :red:`MLast.StMod loc b lsme`

- module type

  - :blue:`<:str_item< module type $s$ = $mt$ >>`
  - :red:`MLast.StMty loc (Ploc.VaVal s) mt`
  - :blue:`<:str_item< module type $_:s$ = $mt$ >>`
  - :red:`MLast.StMty loc s mt`

- open

  - :blue:`<:str_item< open $list:ls$ >>`
  - :red:`MLast.StOpn loc (Ploc.VaVal ls)`
  - :blue:`<:str_item< open $_list:ls$ >>`
  - :red:`MLast.StOpn loc ls`

- type declaration

  - :blue:`<:str_item< type $list:ltd$ >>`
  - :red:`MLast.StTyp loc (Ploc.VaVal ltd)`
  - :blue:`<:str_item< type $_list:ltd$ >>`
  - :red:`MLast.StTyp loc ltd`

- ... internal use ... <a href="#t_str_item_1">(1)</a>

  - :blue:`<:str_item< # $str:s$ $list:lsil$ >>`
  - :red:`MLast.StUse loc (Ploc.VaVal s) (Ploc.VaVal lsil)`
  - :blue:`<:str_item< # $str:s$ $_list:lsil$ >>`
  - :red:`MLast.StUse loc (Ploc.VaVal s) lsil`
  - :blue:`<:str_item< # $_str:s$ $list:lsil$ >>`
  - :red:`MLast.StUse loc s (Ploc.VaVal lsil)`
  - :blue:`<:str_item< # $_str:s$ $_list:lsil$ >>`
  - :red:`MLast.StUse loc s lsil`

- value rec

  - :blue:`<:str_item< value rec $list:lpe$ >>`
  - :red:`MLast.StVal loc (Ploc.VaVal True) (Ploc.VaVal lpe)`
  - :blue:`<:str_item< value rec $_list:lpe$ >>`
  - :red:`MLast.StVal loc (Ploc.VaVal True) lpe`

- value non rec

  - :blue:`<:str_item< value $list:lpe$ >>`
  - :red:`MLast.StVal loc (Ploc.VaVal False) (Ploc.VaVal lpe)`
  - :blue:`<:str_item< value $_list:lpe$ >>`
  - :red:`MLast.StVal loc (Ploc.VaVal False) lpe`

- value

  - :blue:`<:str_item< value $flag:b$ $list:lpe$ >>`
  - :red:`MLast.StVal loc (Ploc.VaVal b) (Ploc.VaVal lpe)`
  - :blue:`<:str_item< value $flag:b$ $_list:lpe$ >>`
  - :red:`MLast.StVal loc (Ploc.VaVal b) lpe`
  - :blue:`<:str_item< value $_flag:b$ $list:lpe$ >>`
  - :red:`MLast.StVal loc b (Ploc.VaVal lpe)`
  - :blue:`<:str_item< value $_flag:b$ $_list:lpe$ >>`
  - :red:`MLast.StVal loc b lpe`

- extra node <a href="#str_item_2">(2)</a>

  - :blue:`... no representation ...`
  - :red:`MLast.StXtr loc s ot`


1. Node internally used to specify a different file name applying to
the whole subtree. This is generated by the directive "use" and
used when converting to the OCaml syntax tree which needs the file
name in its location type.

2. Extra node internally used by the quotation kit
``q_ast.cmo`` to build antiquotations of structure
items.


sig_item
^^^^^^^^

Signature items, i.e. phrases in a ".mli" file or elements
inside "sig ... end".

- class

  - :blue:`<:sig_item< class $list:lcict$ >>`
  - :red:`MLast.SgCls loc (Ploc.VaVal lcict)`
  - :blue:`<:sig_item< class $_list:lcict$ >>`
  - :red:`MLast.SgCls loc lcict`

- class type

  - :blue:`<:sig_item< class type $list:lcict$ >>`
  - :red:`MLast.SgClt loc (Ploc.VaVal lcict)`
  - :blue:`<:sig_item< class type $_list:lcict$ >>`
  - :red:`MLast.SgClt loc lcict`

- declare

  - :blue:`<:sig_item< declare $list:lsi$ end >>`
  - :red:`MLast.SgDcl loc (Ploc.VaVal lsi)`
  - :blue:`<:sig_item< declare $_list:lsi$ end >>`
  - :red:`MLast.SgDcl loc lsi`

- directive

  - :blue:`<:sig_item< # $lid:s$ >>`
  - :red:`MLast.SgDir loc (Ploc.VaVal s) (Ploc.VaVal None)`
  - :blue:`<:sig_item< # $lid:s$ $e$ >>`
  - :red:`MLast.SgDir loc (Ploc.VaVal s) (Ploc.VaVal (Some e))`
  - :blue:`<:sig_item< # $lid:s$ $opt:oe$ >>`
  - :red:`MLast.SgDir loc (Ploc.VaVal s) (Ploc.VaVal oe)`
  - :blue:`<:sig_item< # $lid:s$ $_opt:oe$ >>`
  - :red:`MLast.SgDir loc (Ploc.VaVal s) oe`
  - :blue:`<:sig_item< # $_lid:s$ >>`
  - :red:`MLast.SgDir loc s (Ploc.VaVal None)`
  - :blue:`<:sig_item< # $_lid:s$ $e$ >>`
  - :red:`MLast.SgDir loc s (Ploc.VaVal (Some e))`
  - :blue:`<:sig_item< # $_lid:s$ $opt:oe$ >>`
  - :red:`MLast.SgDir loc s (Ploc.VaVal oe)`
  - :blue:`<:sig_item< # $_lid:s$ $_opt:oe$ >>`
  - :red:`MLast.SgDir loc s oe`

- exception

  - :blue:`<:sig_item< exception $s$ >>`
  - :red:`MLast.SgExc loc (Ploc.VaVal s) (Ploc.VaVal [])`
  - :blue:`<:sig_item< exception $s$ of $list:lt$ >>`
  - :red:`MLast.SgExc loc (Ploc.VaVal s) (Ploc.VaVal lt)`
  - :blue:`<:sig_item< exception $s$ of $_list:lt$ >>`
  - :red:`MLast.SgExc loc (Ploc.VaVal s) lt`
  - :blue:`<:sig_item< exception $_:s$ >>`
  - :red:`MLast.SgExc loc s (Ploc.VaVal [])`
  - :blue:`<:sig_item< exception $_:s$ of $list:lt$ >>`
  - :red:`MLast.SgExc loc s (Ploc.VaVal lt)`
  - :blue:`<:sig_item< exception $_:s$ of $_list:lt$ >>`
  - :red:`MLast.SgExc loc s lt`

- external

  - :blue:`<:sig_item< external $s$ : $t$ = $list:ls$ >>`
  - :red:`MLast.SgExt loc (Ploc.VaVal s) t (Ploc.VaVal ls)`
  - :blue:`<:sig_item< external $s$ : $t$ = $_list:ls$ >>`
  - :red:`MLast.SgExt loc (Ploc.VaVal s) t ls`
  - :blue:`<:sig_item< external $_:s$ : $t$ = $list:ls$ >>`
  - :red:`MLast.SgExt loc s t (Ploc.VaVal ls)`
  - :blue:`<:sig_item< external $_:s$ : $t$ = $_list:ls$ >>`
  - :red:`MLast.SgExt loc s t ls`

- include

  - :blue:`<:sig_item< include $mt$ >>`
  - :red:`MLast.SgInc loc mt`

- module rec

  - :blue:`<:sig_item< module rec $list:lsmt$ >>`
  - :red:`MLast.SgMod loc (Ploc.VaVal True) (Ploc.VaVal lsmt)`
  - :blue:`<:sig_item< module rec $_list:lsmt$ >>`
  - :red:`MLast.SgMod loc (Ploc.VaVal True) lsmt`

- module non rec

  - :blue:`<:sig_item< module $list:lsmt$ >>`
  - :red:`MLast.SgMod loc (Ploc.VaVal False) (Ploc.VaVal lsmt)`
  - :blue:`<:sig_item< module $_list:lsmt$ >>`
  - :red:`MLast.SgMod loc (Ploc.VaVal False) lsmt`

- module

  - :blue:`<:sig_item< module $flag:b$ $list:lsmt$ >>`
  - :red:`MLast.SgMod loc (Ploc.VaVal b) (Ploc.VaVal lsmt)`
  - :blue:`<:sig_item< module $flag:b$ $_list:lsmt$ >>`
  - :red:`MLast.SgMod loc (Ploc.VaVal b) lsmt`
  - :blue:`<:sig_item< module $_flag:b$ $list:lsmt$ >>`
  - :red:`MLast.SgMod loc b (Ploc.VaVal lsmt)`
  - :blue:`<:sig_item< module $_flag:b$ $_list:lsmt$ >>`
  - :red:`MLast.SgMod loc b lsmt`

- module type

  - :blue:`<:sig_item< module type $s$ = $mt$ >>`
  - :red:`MLast.SgMty loc (Ploc.VaVal s) mt`
  - :blue:`<:sig_item< module type $_:s$ = $mt$ >>`
  - :red:`MLast.SgMty loc s mt`

- open

  - :blue:`<:sig_item< open $list:ls$ >>`
  - :red:`MLast.SgOpn loc (Ploc.VaVal ls)`
  - :blue:`<:sig_item< open $_list:ls$ >>`
  - :red:`MLast.SgOpn loc ls`

- type declaration

  - :blue:`<:sig_item< type $list:ltd$ >>`
  - :red:`MLast.SgTyp loc (Ploc.VaVal ltd)`
  - :blue:`<:sig_item< type $_list:ltd$ >>`
  - :red:`MLast.SgTyp loc ltd`

- ... internal use ... <a href="#t_sig_item_1">(1)</a>

  - :blue:`<:sig_item< # $str:s$ $list:lsil$ >>`
  - :red:`MLast.SgUse loc (Ploc.VaVal s) (Ploc.VaVal lsil)`
  - :blue:`<:sig_item< # $str:s$ $_list:lsil$ >>`
  - :red:`MLast.SgUse loc (Ploc.VaVal s) lsil`
  - :blue:`<:sig_item< # $_str:s$ $list:lsil$ >>`
  - :red:`MLast.SgUse loc s (Ploc.VaVal lsil)`
  - :blue:`<:sig_item< # $_str:s$ $_list:lsil$ >>`
  - :red:`MLast.SgUse loc s lsil`

- value

  - :blue:`<:sig_item< value $s$ : $t$ >>`
  - :red:`MLast.SgVal loc (Ploc.VaVal s) t`
  - :blue:`<:sig_item< value $_:s$ : $t$ >>`
  - :red:`MLast.SgVal loc s t`

- extra node <a href="#sig_item_2">(2)</a>

  - :blue:`... no representation ...`
  - :red:`MLast.SgXtr loc s ot`


1. Same remark as for ``str_item`` above.

2. Extra node internally used by the quotation kit ``q_ast.cmo`` to
build antiquotations of signature items.

module_expr
^^^^^^^^^^^

- access

  - :blue:`<:module_expr< $me1$ . $me2$ >>`
  - :red:`MLast.MeAcc loc me1 me2`

- application

  - :blue:`<:module_expr< $me1$ $me2$ >>`
  - :red:`MLast.MeApp loc me1 me2`

- functor

  - :blue:`<:module_expr< functor ($s$ : $mt$) -> $me$ >>`
  - :red:`MLast.MeFun loc (Ploc.VaVal s) mt me`
  - :blue:`<:module_expr< functor ($_:s$ : $mt$) -> $me$ >>`
  - :red:`MLast.MeFun loc s mt me`

- struct

  - :blue:`<:module_expr< struct $list:lsi$ end >>`
  - :red:`MLast.MeStr loc (Ploc.VaVal lsi)`
  - :blue:`<:module_expr< struct $_list:lsi$ end >>`
  - :red:`MLast.MeStr loc lsi`

- module type constraint

  - :blue:`<:module_expr< ($me$ : $mt$) >>`
  - :red:`MLast.MeTyc loc me mt`

- uppercase identifier

  - :blue:`<:module_expr< $uid:s$ >>`
  - :red:`MLast.MeUid loc (Ploc.VaVal s)`
  - :blue:`<:module_expr< $_uid:s$ >>`
  - :red:`MLast.MeUid loc s`

- module unpacking

  - :blue:`<:module_expr< (value $e$) >>`
  - :red:`MLast.MeUnp loc e None`
  - :blue:`<:module_expr< (value $e$ : $mt$) >>`
  - :red:`MLast.MeUnp loc e (Some mt)`

- extra node <a href="#module_expr_1">(1)</a>

  - :blue:`... no representation ...`
  - :red:`MLast.MeXtr loc s ot`


1. Extra node internally used by the quotation kit ``q_ast.cmo`` to
build antiquotations of module expressions.

module_type
^^^^^^^^^^^

- access

  - :blue:`<:module_type< $mt1$ . $mt2$ >>`
  - :red:`MLast.MtAcc loc mt1 mt2`

- application

  - :blue:`<:module_type< $mt1$ $mt2$ >>`
  - :red:`MLast.MtApp loc mt1 mt2`

- functor

  - :blue:`<:module_type< functor ($s$ : $mt1$) -> $mt2$ >>`
  - :red:`MLast.MtFun loc (Ploc.VaVal s) mt1 mt2`
  - :blue:`<:module_type< functor ($_:s$ : $mt1$) -> $mt2$ >>`
  - :red:`MLast.MtFun loc s mt1 mt2`

- lowercase identifier

  - :blue:`<:module_type< $lid:s$ >>`
  - :red:`MLast.MtLid loc (Ploc.VaVal s)`
  - :blue:`<:module_type< $_lid:s$ >>`
  - :red:`MLast.MtLid loc s`

- abstract

  - :blue:`<:module_type< ' $s$ >>`
  - :red:`MLast.MtQuo loc (Ploc.VaVal s)`
  - :blue:`<:module_type< ' $_:s$ >>`
  - :red:`MLast.MtQuo loc s`

- signature

  - :blue:`<:module_type< sig $list:lsi$ end >>`
  - :red:`MLast.MtSig loc (Ploc.VaVal lsi)`
  - :blue:`<:module_type< sig $_list:lsi$ end >>`
  - :red:`MLast.MtSig loc lsi`

- of module expression

  - :blue:`<:module_type< module type of $me$ >>`
  - :red:`MLast.MtTyo loc me`

- uppercase identifier

  - :blue:`<:module_type< $uid:s$ >>`
  - :red:`MLast.MtUid loc (Ploc.VaVal s)`
  - :blue:`<:module_type< $_uid:s$ >>`
  - :red:`MLast.MtUid loc s`

- with construction

  - :blue:`<:module_type< $mt$ with $list:lwc$ >>`
  - :red:`MLast.MtWit loc mt (Ploc.VaVal lwc)`
  - :blue:`<:module_type< $mt$ with $_list:lwc$ >>`
  - :red:`MLast.MtWit loc mt lwc`

- extra node <a href="#module_type_1">(1)</a>

  - :blue:`... no representation ...`
  - :red:`MLast.MtXtr loc s ot`


1. Extra node internally used by the quotation kit ``q_ast.cmo`` to
build antiquotations of module types.


classes...
----------


class_expr
^^^^^^^^^^

- application

  - :blue:`<:class_expr< $ce$ $e$ >>`
  - :red:`MLast.CeApp loc ce e`

- constructor

  - :blue:`<:class_expr< [ $list:lt$ ] $list:ls$ >>`
  - :red:`MLast.CeCon loc (Ploc.VaVal ls) (Ploc.VaVal lt)`
  - :blue:`<:class_expr< [ $_list:lt$ ] $list:ls$ >>`
  - :red:`MLast.CeCon loc (Ploc.VaVal ls) lt`
  - :blue:`<:class_expr< [ $list:lt$ ] $_list:ls$ >>`
  - :red:`MLast.CeCon loc ls (Ploc.VaVal lt)`
  - :blue:`<:class_expr< [ $_list:lt$ ] $_list:ls$ >>`
  - :red:`MLast.CeCon loc ls lt`

- function

  - :blue:`<:class_expr< fun $p$ -> $ce$ >>`
  - :red:`MLast.CeFun loc p ce`

- let rec

  - :blue:`<:class_expr< let rec $list:lpe$ in $ce$ >>`
  - :red:`MLast.CeLet loc (Ploc.VaVal True) (Ploc.VaVal lpe) ce`
  - :blue:`<:class_expr< let rec $_list:lpe$ in $ce$ >>`
  - :red:`MLast.CeLet loc (Ploc.VaVal True) lpe ce`

- let non rec

  - :blue:`<:class_expr< let $list:lpe$ in $ce$ >>`
  - :red:`MLast.CeLet loc (Ploc.VaVal False) (Ploc.VaVal lpe) ce`
  - :blue:`<:class_expr< let $_list:lpe$ in $ce$ >>`
  - :red:`MLast.CeLet loc (Ploc.VaVal False) lpe ce`

- let

  - :blue:`<:class_expr< let $flag:b$ $list:lpe$ in $ce$ >>`
  - :red:`MLast.CeLet loc (Ploc.VaVal b) (Ploc.VaVal lpe) ce`
  - :blue:`<:class_expr< let $flag:b$ $_list:lpe$ in $ce$ >>`
  - :red:`MLast.CeLet loc (Ploc.VaVal b) lpe ce`
  - :blue:`<:class_expr< let $_flag:b$ $list:lpe$ in $ce$ >>`
  - :red:`MLast.CeLet loc b (Ploc.VaVal lpe) ce`
  - :blue:`<:class_expr< let $_flag:b$ $_list:lpe$ in $ce$ >>`
  - :red:`MLast.CeLet loc b lpe ce`

- object

  - :blue:`<:class_expr< object $list:lcsi$ end >>`
  - :red:`MLast.CeStr loc (Ploc.VaVal None) (Ploc.VaVal lcsi)`
  - :blue:`<:class_expr< object $_list:lcsi$ end >>`
  - :red:`MLast.CeStr loc (Ploc.VaVal None) lcsi`
  - :blue:`<:class_expr< object ($p$) $list:lcsi$ end >>`
  - :red:`MLast.CeStr loc (Ploc.VaVal (Some p)) (Ploc.VaVal lcsi)`
  - :blue:`<:class_expr< object ($p$) $_list:lcsi$ end >>`
  - :red:`MLast.CeStr loc (Ploc.VaVal (Some p)) lcsi`
  - :blue:`<:class_expr< object $opt:op$ $list:lcsi$ end >>`
  - :red:`MLast.CeStr loc (Ploc.VaVal op) (Ploc.VaVal lcsi)`
  - :blue:`<:class_expr< object $opt:op$ $_list:lcsi$ end >>`
  - :red:`MLast.CeStr loc (Ploc.VaVal op) lcsi`
  - :blue:`<:class_expr< object $_opt:op$ $list:lcsi$ end >>`
  - :red:`MLast.CeStr loc op (Ploc.VaVal lcsi)`
  - :blue:`<:class_expr< object $_opt:op$ $_list:lcsi$ end >>`
  - :red:`MLast.CeStr loc op lcsi`

- class type constraint

  - :blue:`<:class_expr< ($ce$ : $ct$) >>`
  - :red:`MLast.CeTyc loc ce ct`



class_type
^^^^^^^^^^

- access

  - :blue:`<:class_type< $ct1$ . $ct2$ >>`
  - :red:`MLast.CtAcc loc ct1 ct2`

- application

  - :blue:`<:class_type< $ct1$ $ct2$ >>`
  - :red:`MLast.CtApp loc ct1 ct2`

- constructor

  - :blue:`<:class_type< $ct$ [ $list:lt$ ] >>`
  - :red:`MLast.CtCon loc ct (Ploc.VaVal lt)`
  - :blue:`<:class_type< $ct$ [ $_list:lt$ ] >>`
  - :red:`MLast.CtCon loc ct lt`

- arrow

  - :blue:`<:class_type< [ $t$ ] -> $ct$ >>`
  - :red:`MLast.CtFun loc t ct`

- identifier

  - :blue:`<:class_type< $id:s$ >>`
  - :red:`MLast.CtIde loc (Ploc.VaVal s)`
  - :blue:`<:class_type< $_id:s$ >>`
  - :red:`MLast.CtIde loc s`

- object

  - :blue:`<:class_type< object $list:lcsi$ end >>`
  - :red:`MLast.CtSig loc (Ploc.VaVal None) (Ploc.VaVal lcsi)`
  - :blue:`<:class_type< object $_list:lcsi$ end >>`
  - :red:`MLast.CtSig loc (Ploc.VaVal None) lcsi`
  - :blue:`<:class_type< object ($t$) $list:lcsi$ end >>`
  - :red:`MLast.CtSig loc (Ploc.VaVal (Some t)) (Ploc.VaVal lcsi)`
  - :blue:`<:class_type< object ($t$) $_list:lcsi$ end >>`
  - :red:`MLast.CtSig loc (Ploc.VaVal (Some t)) lcsi`
  - :blue:`<:class_type< object $opt:ot$ $list:lcsi$ end >>`
  - :red:`MLast.CtSig loc (Ploc.VaVal ot) (Ploc.VaVal lcsi)`
  - :blue:`<:class_type< object $opt:ot$ $_list:lcsi$ end >>`
  - :red:`MLast.CtSig loc (Ploc.VaVal ot) lcsi`
  - :blue:`<:class_type< object $_opt:ot$ $list:lcsi$ end >>`
  - :red:`MLast.CtSig loc ot (Ploc.VaVal lcsi)`
  - :blue:`<:class_type< object $_opt:ot$ $_list:lcsi$ end >>`
  - :red:`MLast.CtSig loc ot lcsi`



class_str_item
^^^^^^^^^^^^^^

- type constraint

  - :blue:`<:class_str_item< type $t1$ = $t2$ >>`
  - :red:`MLast.CrCtr loc t1 t2`

- declaration list

  - :blue:`<:class_str_item< declare $list:lcsi$ end >>`
  - :red:`MLast.CrDcl loc (Ploc.VaVal lcsi)`
  - :blue:`<:class_str_item< declare $_list:lcsi$ end >>`
  - :red:`MLast.CrDcl loc lcsi`

- inheritance

  - :blue:`<:class_str_item< inherit $ce$ >>`
  - :red:`MLast.CrInh loc ce (Ploc.VaVal None)`
  - :blue:`<:class_str_item< inherit $ce$ $opt:Some s$ >>`
  - :red:`MLast.CrInh loc ce (Ploc.VaVal (Some s))`
  - :blue:`<:class_str_item< inherit $ce$ $opt:os$ >>`
  - :red:`MLast.CrInh loc ce (Ploc.VaVal os)`
  - :blue:`<:class_str_item< inherit $ce$ $_opt:os$ >>`
  - :red:`MLast.CrInh loc ce os`

- initialization

  - :blue:`<:class_str_item< initializer $e$ >>`
  - :red:`MLast.CrIni loc e`

- method

  - :blue:`<:class_str_item< method! private $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method! private $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method! private $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method! private $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method! private $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method! private $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method! private $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method! private $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal True) s ot e`
  - :blue:`<:class_str_item< method! $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method! $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method! $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method! $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method! $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method! $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method! $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method! $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal False) s ot e`
  - :blue:`<:class_str_item< method! $priv:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method! $priv:b2$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method! $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method! $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method! $priv:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method! $priv:b2$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method! $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method! $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) (Ploc.VaVal b2) s ot e`
  - :blue:`<:class_str_item< method! $_priv:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) b2 (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method! $_priv:b2$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) b2 (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method! $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) b2 (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method! $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) b2 (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method! $_priv:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) b2 s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method! $_priv:b2$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) b2 s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method! $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) b2 s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method! $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal True) b2 s ot e`
  - :blue:`<:class_str_item< method private $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method private $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method private $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method private $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method private $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method private $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method private $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method private $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal True) s ot e`
  - :blue:`<:class_str_item< method $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal False) s ot e`
  - :blue:`<:class_str_item< method $priv:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $priv:b2$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $priv:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $priv:b2$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) (Ploc.VaVal b2) s ot e`
  - :blue:`<:class_str_item< method $_priv:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) b2 (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_priv:b2$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) b2 (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) b2 (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) b2 (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $_priv:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) b2 s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_priv:b2$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) b2 s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) b2 s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal False) b2 s ot e`
  - :blue:`<:class_str_item< method $!:b1$ private $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $!:b1$ private $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $!:b1$ private $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $!:b1$ private $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $!:b1$ private $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $!:b1$ private $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $!:b1$ private $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $!:b1$ private $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal True) s ot e`
  - :blue:`<:class_str_item< method $!:b1$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $!:b1$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $!:b1$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $!:b1$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $!:b1$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $!:b1$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $!:b1$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $!:b1$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal False) s ot e`
  - :blue:`<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) (Ploc.VaVal b2) s ot e`
  - :blue:`<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) b2 s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) b2 s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) b2 s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc (Ploc.VaVal b1) b2 s ot e`
  - :blue:`<:class_str_item< method $_!:b1$ private $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_!:b1$ private $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_!:b1$ private $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal True) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_!:b1$ private $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal True) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $_!:b1$ private $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal True) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_!:b1$ private $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal True) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_!:b1$ private $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal True) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_!:b1$ private $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal True) s ot e`
  - :blue:`<:class_str_item< method $_!:b1$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_!:b1$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_!:b1$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal False) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_!:b1$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal False) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $_!:b1$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal False) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal False) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal False) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal False) s ot e`
  - :blue:`<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal b2) s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal b2) s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal b2) s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 (Ploc.VaVal b2) s ot e`
  - :blue:`<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 b2 (Ploc.VaVal s) (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 b2 (Ploc.VaVal s) (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 b2 (Ploc.VaVal s) (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 b2 (Ploc.VaVal s) ot e`
  - :blue:`<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 b2 s (Ploc.VaVal None) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 b2 s (Ploc.VaVal (Some t)) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 b2 s (Ploc.VaVal ot) e`
  - :blue:`<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>`
  - :red:`MLast.CrMth loc b1 b2 s ot e`

- value

  - :blue:`<:class_str_item< value! mutable $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal True) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value! mutable $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal True) s e`
  - :blue:`<:class_str_item< value! $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal False) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value! $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal False) s e`
  - :blue:`<:class_str_item< value! $flag:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal b2) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value! $flag:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal True) (Ploc.VaVal b2) s e`
  - :blue:`<:class_str_item< value! $_flag:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal True) b2 (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value! $_flag:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal True) b2 s e`
  - :blue:`<:class_str_item< value mutable $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal True) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value mutable $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal True) s e`
  - :blue:`<:class_str_item< value $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal False) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal False) s e`
  - :blue:`<:class_str_item< value $flag:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal b2) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $flag:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal False) (Ploc.VaVal b2) s e`
  - :blue:`<:class_str_item< value $_flag:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal False) b2 (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $_flag:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal False) b2 s e`
  - :blue:`<:class_str_item< value $!:b1$ mutable $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal True) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $!:b1$ mutable $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal True) s e`
  - :blue:`<:class_str_item< value $!:b1$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal False) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $!:b1$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal False) s e`
  - :blue:`<:class_str_item< value $!:b1$ $flag:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal b2) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $!:b1$ $flag:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal b1) (Ploc.VaVal b2) s e`
  - :blue:`<:class_str_item< value $!:b1$ $_flag:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal b1) b2 (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $!:b1$ $_flag:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc (Ploc.VaVal b1) b2 s e`
  - :blue:`<:class_str_item< value $_!:b1$ mutable $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc b1 (Ploc.VaVal True) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $_!:b1$ mutable $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc b1 (Ploc.VaVal True) s e`
  - :blue:`<:class_str_item< value $_!:b1$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc b1 (Ploc.VaVal False) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $_!:b1$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc b1 (Ploc.VaVal False) s e`
  - :blue:`<:class_str_item< value $_!:b1$ $flag:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc b1 (Ploc.VaVal b2) (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $_!:b1$ $flag:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc b1 (Ploc.VaVal b2) s e`
  - :blue:`<:class_str_item< value $_!:b1$ $_flag:b2$ $lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc b1 b2 (Ploc.VaVal s) e`
  - :blue:`<:class_str_item< value $_!:b1$ $_flag:b2$ $_lid:s$ = $e$ >>`
  - :red:`MLast.CrVal loc b1 b2 s e`

- virtual value

  - :blue:`<:class_str_item< value virtual mutable $lid:s$ : $t$ >>`
  - :red:`MLast.CrVav loc (Ploc.VaVal True) (Ploc.VaVal s) t`
  - :blue:`<:class_str_item< value virtual mutable $_lid:s$ : $t$ >>`
  - :red:`MLast.CrVav loc (Ploc.VaVal True) s t`
  - :blue:`<:class_str_item< value virtual $lid:s$ : $t$ >>`
  - :red:`MLast.CrVav loc (Ploc.VaVal False) (Ploc.VaVal s) t`
  - :blue:`<:class_str_item< value virtual $_lid:s$ : $t$ >>`
  - :red:`MLast.CrVav loc (Ploc.VaVal False) s t`
  - :blue:`<:class_str_item< value virtual $flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CrVav loc (Ploc.VaVal b) (Ploc.VaVal s) t`
  - :blue:`<:class_str_item< value virtual $flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CrVav loc (Ploc.VaVal b) s t`
  - :blue:`<:class_str_item< value virtual $_flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CrVav loc b (Ploc.VaVal s) t`
  - :blue:`<:class_str_item< value virtual $_flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CrVav loc b s t`

- virtual method

  - :blue:`<:class_str_item< method virtual private $lid:s$ : $t$ >>`
  - :red:`MLast.CrVir loc (Ploc.VaVal True) (Ploc.VaVal s) t`
  - :blue:`<:class_str_item< method virtual private $_lid:s$ : $t$ >>`
  - :red:`MLast.CrVir loc (Ploc.VaVal True) s t`
  - :blue:`<:class_str_item< method virtual $lid:s$ : $t$ >>`
  - :red:`MLast.CrVir loc (Ploc.VaVal False) (Ploc.VaVal s) t`
  - :blue:`<:class_str_item< method virtual $_lid:s$ : $t$ >>`
  - :red:`MLast.CrVir loc (Ploc.VaVal False) s t`
  - :blue:`<:class_str_item< method virtual $flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CrVir loc (Ploc.VaVal b) (Ploc.VaVal s) t`
  - :blue:`<:class_str_item< method virtual $flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CrVir loc (Ploc.VaVal b) s t`
  - :blue:`<:class_str_item< method virtual $_flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CrVir loc b (Ploc.VaVal s) t`
  - :blue:`<:class_str_item< method virtual $_flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CrVir loc b s t`



class_sig_item
^^^^^^^^^^^^^^

- type constraint

  - :blue:`<:class_sig_item< type $t1$ = $t2$ >>`
  - :red:`MLast.CgCtr loc t1 t2`

- declare

  - :blue:`<:class_sig_item< declare $list:lcsi$ end >>`
  - :red:`MLast.CgDcl loc (Ploc.VaVal lcsi)`
  - :blue:`<:class_sig_item< declare $_list:lcsi$ end >>`
  - :red:`MLast.CgDcl loc lcsi`

- inheritance

  - :blue:`<:class_sig_item< inherit $ct$ >>`
  - :red:`MLast.CgInh loc ct`

- method

  - :blue:`<:class_sig_item< method private $lid:s$ : $t$ >>`
  - :red:`MLast.CgMth loc (Ploc.VaVal True) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< method private $_lid:s$ : $t$ >>`
  - :red:`MLast.CgMth loc (Ploc.VaVal True) s t`
  - :blue:`<:class_sig_item< method $lid:s$ : $t$ >>`
  - :red:`MLast.CgMth loc (Ploc.VaVal False) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< method $_lid:s$ : $t$ >>`
  - :red:`MLast.CgMth loc (Ploc.VaVal False) s t`
  - :blue:`<:class_sig_item< method $flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CgMth loc (Ploc.VaVal b) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< method $flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CgMth loc (Ploc.VaVal b) s t`
  - :blue:`<:class_sig_item< method $_flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CgMth loc b (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< method $_flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CgMth loc b s t`

- value

  - :blue:`<:class_sig_item< value mutable $lid:s$ : $t$ >>`
  - :red:`MLast.CgVal loc (Ploc.VaVal True) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< value mutable $_lid:s$ : $t$ >>`
  - :red:`MLast.CgVal loc (Ploc.VaVal True) s t`
  - :blue:`<:class_sig_item< value $lid:s$ : $t$ >>`
  - :red:`MLast.CgVal loc (Ploc.VaVal False) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< value $_lid:s$ : $t$ >>`
  - :red:`MLast.CgVal loc (Ploc.VaVal False) s t`
  - :blue:`<:class_sig_item< value $flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CgVal loc (Ploc.VaVal b) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< value $flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CgVal loc (Ploc.VaVal b) s t`
  - :blue:`<:class_sig_item< value $_flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CgVal loc b (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< value $_flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CgVal loc b s t`

- virtual method

  - :blue:`<:class_sig_item< method virtual private $lid:s$ : $t$ >>`
  - :red:`MLast.CgVir loc (Ploc.VaVal True) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< method virtual private $_lid:s$ : $t$ >>`
  - :red:`MLast.CgVir loc (Ploc.VaVal True) s t`
  - :blue:`<:class_sig_item< method virtual $lid:s$ : $t$ >>`
  - :red:`MLast.CgVir loc (Ploc.VaVal False) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< method virtual $_lid:s$ : $t$ >>`
  - :red:`MLast.CgVir loc (Ploc.VaVal False) s t`
  - :blue:`<:class_sig_item< method virtual $flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CgVir loc (Ploc.VaVal b) (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< method virtual $flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CgVir loc (Ploc.VaVal b) s t`
  - :blue:`<:class_sig_item< method virtual $_flag:b$ $lid:s$ : $t$ >>`
  - :red:`MLast.CgVir loc b (Ploc.VaVal s) t`
  - :blue:`<:class_sig_item< method virtual $_flag:b$ $_lid:s$ : $t$ >>`
  - :red:`MLast.CgVir loc b s t`



other
-----


type_decl
^^^^^^^^^

What is after 'type' or 'and' in a type declaration.

The type ``type_decl`` is a record type corresponding to
a type declaration. Its definition is:

::

  type type_decl =
    { tdNam : (loc * Ploc.vaval string);
      tdPrm : Ploc.vala (list type_var);
      tdPrv : Ploc.vala bool;
      tdDef : ctyp;
      tdCon : Ploc.vala (list (ctyp * ctyp)) }
  ;


The field ``tdNam`` is the type identifier (together with its
location in the source).

The field ``tdPrm`` is the list of its possible parameters.

The field ``tdPrv`` tells if the type is private or not.

The field ``tdDef`` is the definition of the type.

The field ``tdCon`` is the possible list of type constraints.

- 

  - :blue:`<:type_decl< $tp:ls$ $list:ltv$ = private $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $tp:ls$ $list:ltv$ = private $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $tp:ls$ $list:ltv$ = $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $tp:ls$ $list:ltv$ = $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $tp:ls$ $list:ltv$ = $priv:b$ $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $tp:ls$ $list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $tp:ls$ $list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $tp:ls$ $list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $tp:ls$ $_list:ltv$ = private $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $tp:ls$ $_list:ltv$ = private $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $tp:ls$ $_list:ltv$ = $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $tp:ls$ $_list:ltv$ = $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $tp:ls$ $_list:ltv$ = $priv:b$ $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $tp:ls$ $_list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = Ploc.VaVal ls; MLast.tdPrm = ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $list:ltv$ = private $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $list:ltv$ = private $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $list:ltv$ = $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $list:ltv$ = $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $list:ltv$ = $priv:b$ $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = Ploc.VaVal ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $_list:ltv$ = private $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $_list:ltv$ = private $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal True; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $_list:ltv$ = $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $_list:ltv$ = $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal False; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $_list:ltv$ = $priv:b$ $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $_list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = Ploc.VaVal b; MLast.tdDef = t; MLast.tdCon = ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = Ploc.VaVal ltt}`
  - :blue:`<:type_decl< $_tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>`
  - :red:`{MLast.tdNam = ls; MLast.tdPrm = ltv; MLast.tdPrv = b; MLast.tdDef = t; MLast.tdCon = ltt}`

with_constr
^^^^^^^^^^^

"With" possibly following a module type.

- with module

  - :blue:`<:with_constr< module $list:ls$ = $me$ >>`
  - :red:`MLast.WcMod loc (Ploc.VaVal ls) me`
  - :blue:`<:with_constr< module $_list:ls$ = $me$ >>`
  - :red:`MLast.WcMod loc ls me`

- with module substitution

  - :blue:`<:with_constr< module $list:ls$ := $me$ >>`
  - :red:`MLast.WcMos loc (Ploc.VaVal ls) me`
  - :blue:`<:with_constr< module $_list:ls$ := $me$ >>`
  - :red:`MLast.WcMos loc ls me`

- with type

  - :blue:`<:with_constr< type $list:ls$ $list:ltv$ = private $t$ >>`
  - :red:`MLast.WcTyp loc (Ploc.VaVal ls) (Ploc.VaVal ltv) (Ploc.VaVal True) t`
  - :blue:`<:with_constr< type $list:ls$ $list:ltv$ = $t$ >>`
  - :red:`MLast.WcTyp loc (Ploc.VaVal ls) (Ploc.VaVal ltv) (Ploc.VaVal False) t`
  - :blue:`<:with_constr< type $list:ls$ $list:ltv$ = $flag:b$ $t$ >>`
  - :red:`MLast.WcTyp loc (Ploc.VaVal ls) (Ploc.VaVal ltv) (Ploc.VaVal b) t`
  - :blue:`<:with_constr< type $list:ls$ $list:ltv$ = $_flag:b$ $t$ >>`
  - :red:`MLast.WcTyp loc (Ploc.VaVal ls) (Ploc.VaVal ltv) b t`
  - :blue:`<:with_constr< type $list:ls$ $_list:ltv$ = private $t$ >>`
  - :red:`MLast.WcTyp loc (Ploc.VaVal ls) ltv (Ploc.VaVal True) t`
  - :blue:`<:with_constr< type $list:ls$ $_list:ltv$ = $t$ >>`
  - :red:`MLast.WcTyp loc (Ploc.VaVal ls) ltv (Ploc.VaVal False) t`
  - :blue:`<:with_constr< type $list:ls$ $_list:ltv$ = $flag:b$ $t$ >>`
  - :red:`MLast.WcTyp loc (Ploc.VaVal ls) ltv (Ploc.VaVal b) t`
  - :blue:`<:with_constr< type $list:ls$ $_list:ltv$ = $_flag:b$ $t$ >>`
  - :red:`MLast.WcTyp loc (Ploc.VaVal ls) ltv b t`
  - :blue:`<:with_constr< type $_list:ls$ $list:ltv$ = private $t$ >>`
  - :red:`MLast.WcTyp loc ls (Ploc.VaVal ltv) (Ploc.VaVal True) t`
  - :blue:`<:with_constr< type $_list:ls$ $list:ltv$ = $t$ >>`
  - :red:`MLast.WcTyp loc ls (Ploc.VaVal ltv) (Ploc.VaVal False) t`
  - :blue:`<:with_constr< type $_list:ls$ $list:ltv$ = $flag:b$ $t$ >>`
  - :red:`MLast.WcTyp loc ls (Ploc.VaVal ltv) (Ploc.VaVal b) t`
  - :blue:`<:with_constr< type $_list:ls$ $list:ltv$ = $_flag:b$ $t$ >>`
  - :red:`MLast.WcTyp loc ls (Ploc.VaVal ltv) b t`
  - :blue:`<:with_constr< type $_list:ls$ $_list:ltv$ = private $t$ >>`
  - :red:`MLast.WcTyp loc ls ltv (Ploc.VaVal True) t`
  - :blue:`<:with_constr< type $_list:ls$ $_list:ltv$ = $t$ >>`
  - :red:`MLast.WcTyp loc ls ltv (Ploc.VaVal False) t`
  - :blue:`<:with_constr< type $_list:ls$ $_list:ltv$ = $flag:b$ $t$ >>`
  - :red:`MLast.WcTyp loc ls ltv (Ploc.VaVal b) t`
  - :blue:`<:with_constr< type $_list:ls$ $_list:ltv$ = $_flag:b$ $t$ >>`
  - :red:`MLast.WcTyp loc ls ltv b t`

- with type substitution

  - :blue:`<:with_constr< type $list:ls$ $list:ltv$ := $t$ >>`
  - :red:`MLast.WcTys loc (Ploc.VaVal ls) (Ploc.VaVal ltv) t`
  - :blue:`<:with_constr< type $list:ls$ $_list:ltv$ := $t$ >>`
  - :red:`MLast.WcTys loc (Ploc.VaVal ls) ltv t`
  - :blue:`<:with_constr< type $_list:ls$ $list:ltv$ := $t$ >>`
  - :red:`MLast.WcTys loc ls (Ploc.VaVal ltv) t`
  - :blue:`<:with_constr< type $_list:ls$ $_list:ltv$ := $t$ >>`
  - :red:`MLast.WcTys loc ls ltv t`



poly_variant
^^^^^^^^^^^^

Polymorphic variants.

- constructor

  - :blue:`<:poly_variant< `$s$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal True) (Ploc.VaVal [])`
  - :blue:`<:poly_variant< `$s$ of &amp; $list:lt$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal True) (Ploc.VaVal lt)`
  - :blue:`<:poly_variant< `$s$ of &amp; $_list:lt$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal True) lt`
  - :blue:`<:poly_variant< `$s$ of $list:lt$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal False) (Ploc.VaVal lt)`
  - :blue:`<:poly_variant< `$s$ of $_list:lt$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal False) lt`
  - :blue:`<:poly_variant< `$s$ of $flag:b$ $list:lt$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal b) (Ploc.VaVal lt)`
  - :blue:`<:poly_variant< `$s$ of $flag:b$ $_list:lt$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) (Ploc.VaVal b) lt`
  - :blue:`<:poly_variant< `$s$ of $_flag:b$ $list:lt$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) b (Ploc.VaVal lt)`
  - :blue:`<:poly_variant< `$s$ of $_flag:b$ $_list:lt$ >>`
  - :red:`MLast.PvTag loc (Ploc.VaVal s) b lt`
  - :blue:`<:poly_variant< `$_:s$ >>`
  - :red:`MLast.PvTag loc s (Ploc.VaVal True) (Ploc.VaVal [])`
  - :blue:`<:poly_variant< `$_:s$ of &amp; $list:lt$ >>`
  - :red:`MLast.PvTag loc s (Ploc.VaVal True) (Ploc.VaVal lt)`
  - :blue:`<:poly_variant< `$_:s$ of &amp; $_list:lt$ >>`
  - :red:`MLast.PvTag loc s (Ploc.VaVal True) lt`
  - :blue:`<:poly_variant< `$_:s$ of $list:lt$ >>`
  - :red:`MLast.PvTag loc s (Ploc.VaVal False) (Ploc.VaVal lt)`
  - :blue:`<:poly_variant< `$_:s$ of $_list:lt$ >>`
  - :red:`MLast.PvTag loc s (Ploc.VaVal False) lt`
  - :blue:`<:poly_variant< `$_:s$ of $flag:b$ $list:lt$ >>`
  - :red:`MLast.PvTag loc s (Ploc.VaVal b) (Ploc.VaVal lt)`
  - :blue:`<:poly_variant< `$_:s$ of $flag:b$ $_list:lt$ >>`
  - :red:`MLast.PvTag loc s (Ploc.VaVal b) lt`
  - :blue:`<:poly_variant< `$_:s$ of $_flag:b$ $list:lt$ >>`
  - :red:`MLast.PvTag loc s b (Ploc.VaVal lt)`
  - :blue:`<:poly_variant< `$_:s$ of $_flag:b$ $_list:lt$ >>`
  - :red:`MLast.PvTag loc s b lt`

- type

  - :blue:`<:poly_variant< $t$ >>`
  - :red:`MLast.PvInh loc t`



Nodes without quotations
========================

Some types defined in the AST tree module ``MLast`` don't
have an associated quotation. They are:


-  ``type_var``
-  ``class_infos``



type_var
--------

The type ``type_var`` is defined as:

::

  type type_var = (Ploc.vala string * (bool * bool));


The first boolean is ``True`` if the type variable is
prefixed by ``+`` ("plus" sign). The second boolean is
``True`` if the type variable is prefixed by ``-``
("minus" sign).


class_infos
-----------

The type ``class_infos`` is a record type parametrized with
a type variable. It is common to:


- the "class declaration" (``class ...`` as structure item), the type
  variable being ``class_expr``,
- the "class description" (``class ...`` as signature item), the type
  variable being ``class_type``,
- the "class type declaration" (``class type ...``), the type variable
  being ``class_type``.


It is defined as:

::

  type class_infos 'a =
    { ciLoc : loc;
      ciVir : Ploc.vala bool;
      ciPrm : (loc * Ploc.vala (list type_var));
      ciNam : Ploc.vala string;
      ciExp : 'a }
  ;


The field ``ciLoc`` is the location of the whole definition.

The field ``ciVir`` tells whether the type is virtual or not.

The field ``ciPrm`` is the list of its possible parameters.

The field ``ciNam`` is the class identifier.

The field ``ciExp`` is the class definition, depending of its
kind.

.. ;;; Local Variables: ***
.. ;;; mode:rst ***
.. ;;; End: ***
