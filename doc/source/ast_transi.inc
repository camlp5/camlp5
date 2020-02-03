.. _ast_transi:

**********************************
ML Syntax tree - transitional mode
**********************************

This chapter presents the Camlp5 syntax tree when Camlp5 is installed
in *transitional* mode.

Introduction
============

This syntax tree is defined in the module ``MLast`` provided
by Camlp5. Each node corresponds to a syntactic entity of the
corresponding type.

For example, the syntax tree of the statement ``if`` can
be written:

::

  MLast.ExIfe loc e1 e2 e3


where ``loc`` is the location in the source, and
``e1``, ``e2`` and ``e3`` are
respectively the expression after the ``if``, the one after
the ``then`` and the one after the ``else``.

If a program needs to manipulate syntax trees, it can use the nodes
defined in the module ``MLast``. The programmer must know how
the concrete syntax is transformed into this abstract syntax.

A simpler solution is to use one of the quotation kit
``q_MLast.cmo``. It proposes :ref:`quot` which
represent the abstract syntax (the nodes of the module ``MLast``) into
concrete syntax with antiquotations to bind variables inside. The
example above can be written:

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
    (MLast.ExTry _ (MLast.ExApp _ (MLast.ExUid _ "Some") f)
       [(MLast.PaAcc _ (MLast.PaUid _ "Stream") (MLast.PaUid _ "Failure"),
         None, MLast.ExUid _ "None")])
    [(MLast.PaApp _ (MLast.PaUid _ "Some") p, None, e);
     (MLast.PaAny _, None,
      MLast.ExApp _ (MLast.ExLid _ "raise")
        (MLast.ExApp _
           (MLast.ExAcc _ (MLast.ExUid _ "Stream") (MLast.ExUid _ "Error"))
           e2))]


Which is less readable and much more complicated to build and
update.

Instead of thinking of "a syntax tree", the programmer can think of
"a piece of program".


Location
========

In all syntax tree nodes, the first parameter is the source
location of the node.


In expressions
--------------

When a quotation is in the context of an expression, the location
parameter is ``loc`` in the node and in all its possible
sub-nodes. Example: if we consider the quotation:

::

  <:sig_item< value foo : int -> bool >>


This quotation, in a context of an expression, is equivalent
to:

::

  MLast.SgVal loc "foo"
    (MLast.TyArr loc (MLast.TyLid loc "int") (MLast.TyLid loc "bool"));


The name ``loc`` is predefined. However, it is possible to
change it, using the argument ``-loc`` of the Camlp5 shell
commands.

Consequently, if there is no variable ``loc`` defined in the
context of the quotation, or if it is not of the correct type, a
semantic error occur in the OCaml compiler ("Unbound value
loc").

Note that in the :ref:`grammars`,
the variable ``loc`` is bound, in all semantic actions, to
the location of the rule.

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

  MLast.SgVal _ "foo"
    (MLast.TyArr _ (MLast.TyLid _ "int") (MLast.TyLid _ "bool"))


However, it is possible to generate a binding of the variable
``loc`` on the top node by writing a "colon" before the
"less" in the quotation. The same example:

::

  <:sig_item:< value foo : int -> bool >>


is equivalent to:

::

  MLast.SgVal loc "foo"
    (MLast.TyArr _ (MLast.TyLid _ "int") (MLast.TyLid _ "bool"))



Antiquotations
==============

The expressions or patterns between dollar ($) characters are
called *antiquotations*. In opposition to quotations which
has its own syntax rules, the antiquotation is an area in the syntax
of the enclosing context (expression or pattern). See the chapter
about :ref:`quot`.

If a quotation is in the context of an expression, the
antiquotation must be an expression. It can be any expression,
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



Nodes and Quotations
====================

This section describes all nodes defined in the module "MLast" of
Camlp5 and how to write them with quotations. Notice that, inside
quotations, one is not restricted to these elementary cases, but
any complex value can be used, resulting on possibly complex combined
nodes.

Variables names give information of their types:


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
-  ``lpee``: ``list (patt * option expr * expr)``
-  ``op``: ``option patt``
-  ``lcsi``: ``list class_str_item``
-  ``lcsi``: ``list class_sig_item``



expr
----

Expressions of the language.

.. csv-table:: Expressions of the language
  :header: "Node",``<:expr< ... >>``,"Comment"

  ``ExAcc loc e1 e2``,``$e1$ . $e2$``,access
  ``ExAnt loc e``,``$anti:e$``, <a href="#expr_1">(1)</a>
  ``ExApp loc e1 e2``,``$e1$ $e2$``, application
  ``ExAre loc e1 e2``,``$e1$ .( $e2$ )``, array element
  ``ExArr loc le``,``[| $list:le$ |]``, array
  ``ExAsr loc e``,``assert $e$``, assert
  ``ExAss loc e1 e2``,``$e1$ := $e2$``,assignment
  ``ExBae loc e le``, ``$e$ .{ $list:le$ }``,big array element
  ``ExChr loc s``, ``$chr:s$``, character constant
  ``ExCoe loc e None t2``, ``($e$ :> $t2$)``, coercion
  ``ExCoe loc e (Some t1) t2``, ``($e$ : $t1$ :> $t2$)``, coercion
  ``ExFlo loc s``, ``$flo:s$``, float constant
  ``ExFor loc s e1 e2 True le``, ``for $lid:s$ = $e1$ to $e2$ do { $list:le$ }``, for (increasing)
  ``ExFor loc s e1 e2 False le``,  ``for $lid:s$ = $e1$ downto $e2$ do { $list:le$ }``,  for (decreasing)
  ``ExFor loc s e1 e2 b le``,  ``for $lid:s$ = $e1$ $to:b$ $e2$ do { $list:le$ }``,  for
  ``ExFun loc lpee``,  ``fun [ $list:lpee$ ]``,  function <a href="#expr_2">(2)</a>
  ``ExIfe loc e1 e2 e3``,  ``if $e1$ then $e2$ else $e3$``,  if
  ``ExInt loc s1 ""``,  ``$int:s1$``,  integer constant
  ``ExInt loc s1 "l"``,  ``$int32:s1$``,  integer 32 bits
  ``ExInt loc s1 "L"``,  ``$int64:s1$``,  integer 64 bits
  ``ExInt loc s1 "n"``,  ``$nativeint:s1$``,  native integer
  ``ExLab loc p None``,  ``~{$p$}``,  label
  ``ExLab loc p (Some e)``,  ``~{$p$ = $e$}``,  label
  ``ExLab loc p oe``,  ``~{$p$ $opt:oe$}``,  label
  ``ExLaz loc e``,  ``lazy $e$``,  lazy
  ``ExLet loc True lpe e``,  ``let rec $list:lpe$ in $e$``,  let rec
  ``ExLet loc False lpe e``,  ``let $list:lpe$ in $e$``,  let not rec
  ``ExLet loc b lpe e``,  ``let $flag:b$ $list:lpe$ in $e$``,  let
  ``ExLid loc s``,  ``$lid:s$``,  lowercase identifier
  ``ExLmd loc s me e``,  ``let module $uid:s$ = $me$ in $e$``,  let module
  ``ExMat loc e lpee``,  ``match $e$ with [ $list:lpee$ ]``,  match <a href="#expr_2">(2)</a>
  ``ExNew loc ls``,  ``new $list:ls$``,  new
  ``ExObj loc None lcsi``,  ``object $list:lcsi$ end``,  object expression
  ``ExObj loc (Some p) lcsi``,  ``object ($p$) $list:lcsi$ end``,  object expression
  ``ExObj loc op lcsi``,  ``object $opt:op$ $list:lcsi$ end``,  object expression
  ``ExOlb loc p None``,  ``?{$p$}``,  option label
  ``ExOlb loc p (Some e)``,  ``?{$p$ = $e$}``,  option label
  ``ExOlb loc p oe``,  ``?{$p$ $opt:oe$}``,  option label
  ``ExOvr loc lse``,  ``{< $list:lse$ >}``,  override
  ``ExPck loc me None``,  ``(module $me$)``,  module packing
  ``ExPck loc me (Some mt)``,  ``(module $me$ : $mt$)``,  module packing
  ``ExRec loc lpe None``,  ``{$list:lpe$}``,  record
  ``ExRec loc lpe (Some e)``,  ``{($e$) with $list:lpe$}``,  record
  ``ExSeq loc le``,  ``do { $list:le$ }``,  sequence
  ``ExSnd loc e s``,  ``$e$ # $s$``,  method call
  ``ExSte loc e1 e2``,  ``$e1$ .[ $e2$ ]``,  string element
  ``ExStr loc s``,  ``$str:s$``,  string
  ``ExTry loc e lpee``,  ``try $e$ with [ $list:lpee$ ]``,  try <a href="#expr_2">(2)</a>
  ``ExTup loc le``,  ``($list:le$)``,  t-uple
  ``ExTyc loc e t``,  ``($e$ : $t$)``,  type constraint
  ``ExUid loc s``,  ``$uid:s$``,  uppercase identifier
  ``ExVrn loc s``,  ``` $s$``,  variant
  ``ExWhi loc e le``,  ``while $e$ do { $list:le$ }``,  while

1. Node used in the quotation expanders to tells at conversion to
OCaml compiler syntax tree time, that all locations of the
sub-tree is correcty located in the quotation. By default, in
quotations, the locations of all generated nodes are the location
of the whole quotation. This node allows to make an exception to
this rule, since we know that the antiquotation belongs to the
universe of the enclosing program. See the chapter
about :ref:`quot` and, in particular, its
section about antiquotations.

2. The variable ``lpee`` found in "function", "match" and "try"
statements correspond to a list of ``(patt * option expr *
expr)`` where the ``option expr`` is the "when"
optionally following the pattern:

::

  p -> e


is represented by:

::

  (p, None, e)


and

::

  p when e1 -> e


  is represented by:

::

  (p, Some e1, e)

</div>


patt
----

Patterns of the language.

.. csv-table:: Patterns of the language
  :header: "Node",``<:patt< ... >>``,"Comment"

  ``PaAcc loc p1 p2``,  ``$p1$ . $p2$``,  access
  ``PaAli loc p1 p2``,  ``($p1$ as $p2$)``,  alias
  ``PaAnt loc p``,  ``$anti:p$``,  antiquotation <a href="#patt_1">(1)</a>
  ``PaAny loc``,  ``_``,  wildcard
  ``PaApp loc p1 p2``,  ``$p1$ $p2$``,  application
  ``PaArr loc lp``,  ``[| $list:lp$ |]``,  array
  ``PaChr loc s``,  ``$chr:s$``,  character
  ``PaFlo loc s``,  ``$flo:s$``,  float
  ``PaInt loc s1 ""``,  ``$int:s1$``,  integer constant
  ``PaInt loc s1 "l"``,  ``$int32:s1$``,  integer 32 bits
  ``PaInt loc s1 "L"``,  ``$int64:s1$``,  integer 64 bits
  ``PaInt loc s1 "n"``,  ``$nativeint:s1$``,  native integer
  ``PaLab loc p1 None``,  ``~{$p1$}``,  label
  ``PaLab loc p1 (Some p2)``,  ``~{$p1$ = $p2$}``,  label
  ``PaLab loc p1 op2``,  ``~{$p1$ $opt:op2$}``,  label
  ``PaLaz loc p``,  ``lazy $p$``,  lazy
  ``PaLid loc s``,  ``$lid:s$``,  lowercase identifier
  ``PaNty loc s``,  ``(type $lid:s$)``,  new type
  ``PaOlb loc p None``,  ``?{$p$}``,  option label
  ``PaOlb loc p (Some e)``,  ``?{$p$ = $e$}``,  option label
  ``PaOlb loc p oe``,  ``?{$p$ $opt:oe$}``,  option label
  ``PaOrp loc p1 p2``,  ``$p1$ | $p2$``,  or
  ``PaRec loc lpp``,  ``{ $list:lpp$ }``,  record
  ``PaRng loc p1 p2``,  ``$p1$ .. $p2$``,  range
  ``PaStr loc s``,  ``$str:s$``,  string
  ``PaTup loc lp``,  ``($list:lp$)``,  t-uple
  ``PaTyc loc p t``,  ``($p$ : $t$)``,  type constraint
  ``PaTyp loc ls``,  ``# $list:ls$``,  type pattern
  ``PaUid loc s``,  ``$uid:s$``,  uppercase identifier
  ``PaUnp loc s None``,  ``(module $uid:s$)``,  module unpacking
  ``PaUnp loc s (Some mt)``,  ``(module $uid:s$ : $mt$)``,  module unpacking
  ``PaVrn loc s``,  ``` $s$``,  variant

1. Node used to specify an antiquotation area, like for the equivalent
node in expressions. See above.


ctyp
----

Type expressions of the language.

.. csv-table:: Type expressions of the language
  :header: "Node",``<:ctyp< ... >>``,"Comment"

  ``TyAcc loc t1 t2``,  ``$t1$ . $t2$``,  access
  ``TyAli loc t1 t2``,  ``$t1$ as $t2$``,  alias
  ``TyAny loc``,  ``_``,  wildcard
  ``TyApp loc t1 t2``,  ``$t1$ $t2$``,  application
  ``TyArr loc t1 t2``,  ``$t1$ -> $t2$``,  arrow
  ``TyCls loc ls``,  ``# $list:ls$``,  class
  ``TyLab loc s t``,  ``~$s$: $t$``,  label
  ``TyLid loc s``,  ``$lid:s$``,  lowercase identifier
  ``TyMan loc t1 True t2``,  ``$t1$ == private $t2$``,  manifest
  ``TyMan loc t1 False t2``,  ``$t1$ == $t2$``,  manifest
  ``TyMan loc t1 b t2``,  ``$t1$ == $priv:b$ $t2$``,  manifest
  ``TyObj loc lst True``,  ``< $list:lst$ .. >``,  object
  ``TyObj loc lst False``,  ``< $list:lst$ >``,  object
  ``TyObj loc lst b``,  ``< $list:lst$ $flag:b$ >``,  object
  ``TyOlb loc s t``,  ``?$s$: $t$``,  option label
  ``TyPck loc mt``,  ``(module $mt$)``,  package
  ``TyPol loc ls t``,  ``! $list:ls$ . $t$``,  polymorph
  ``TyQuo loc s``,  ``'$s$``,  variable
  ``TyRec loc llsbt``,  ``{ $list:llsbt$ }``,  record
  ``TySum loc llslt``,  ``[ $list:llslt$ ]``,  sum
  ``TyTup loc lt``,  ``( $list:lt$ )``,  t-uple
  ``TyUid loc s``,  ``$uid:s$``,  uppercase identifier
  ``TyVrn loc lpv None``,  ``[ = $list:lpv$ ]``,  variant
  ``TyVrn loc lpv (Some None)``,  ``[ > $list:lpv$ ]``,  variant
  ``TyVrn loc lpv (Some (Some []))``,  ``[ < $list:lpv$ ]``,  variant
  ``TyVrn loc lpv (Some (Some ls))``,  ``[ < $list:lpv$ > $list:ls$ ]``,  variant

modules...
----------


str_item
^^^^^^^^

Structure items, i.e. phrases in a ``.ml`` file or ``struct``
elements.

.. csv-table:: Structure items of the language
  :header: "Node",``<:str_item< ... >>``,"Comment"

  ``StCls loc lcice``,  ``class $list:lcice$``,  class declaration
  ``StClt loc lcict``,  ``class type $list:lcict$``,  class type declaration
  ``StDcl loc lsi``,  ``declare $list:lsi$ end``,  declare
  ``StDir loc s None``,  ``# $lid:s$``,  directive
  ``StDir loc s (Some e)``,  ``# $lid:s$ $e$``,  directive
  ``StDir loc s oe``,  ``# $lid:s$ $opt:oe$``,  directive
  ``StExc loc s [] []``,  ``exception $uid:s$``,  exception
  ``StExc loc s lt []``,  ``exception $uid:s$ of $list:lt$``,  exception
  ``StExc loc s [] ls``,  ``exception $uid:s$ = $list:ls$``,  exception
  ``StExc loc s lt ls``,  ``exception $uid:s$ of $list:lt$ = $list:ls$``,  exception
  ``StExp loc e``,  ``$exp:e$``,  expression
  ``StExt loc s t ls``,  ``external $s$ : $t$ = $list:ls$``,  external
  ``StInc loc me``,  ``include $me$``,  include
  ``StMod loc True lsme``,  ``module rec $list:lsme$``,  module rec
  ``StMod loc False lsme``,  ``module $list:lsme$``,  module non rec
  ``StMod loc b lsme``,  ``module $flag:b$ $list:lsme$``,  module
  ``StMty loc s mt``,  ``module type $s$ = $mt$``,  module type
  ``StOpn loc ls``,  ``open $list:ls$``,  open
  ``StTyp loc ltd``,  ``type $list:ltd$``,  type declaration
  ``StUse loc s lsil``,  ``# $str:s$ $list:lsil$``,  ... internal use ... <a href="#t_str_item_1">(1)</a>
  ``StVal loc True lpe``,  ``value rec $list:lpe$``,  value rec
  ``StVal loc False lpe``,  ``value $list:lpe$``,  value non rec
  ``StVal loc b lpe``,  ``value $flag:b$ $list:lpe$``,  value

1. Node internally used to specify a different file name applying to
the whole subtree. This is generated by the directive "use" and
used when converting to the OCaml syntax tree which needs the file
name in its location type.

sig_item
^^^^^^^^

Signature items, i.e. phrases in a ".mli" file or elements
inside "sig ... end".

.. csv-table:: Signature items of the language
  :header: "Node",``<:sig_item< ... >>``,"Comment"

  ``SgCls loc lcict``,  ``class $list:lcict$``,  class
  ``SgClt loc lcict``,  ``class type $list:lcict$``,  class type
  ``SgDcl loc lsi``,  ``declare $list:lsi$ end``,  declare
  ``SgDir loc s None``,  ``# $lid:s$``,  directive
  ``SgDir loc s (Some e)``,  ``# $lid:s$ $e$``,  directive
  ``SgDir loc s oe``,  ``# $lid:s$ $opt:oe$``,  directive
  ``SgExc loc s []``,  ``exception $s$``,  exception
  ``SgExc loc s lt``,  ``exception $s$ of $list:lt$``,  exception
  ``SgExt loc s t ls``,  ``external $s$ : $t$ = $list:ls$``,  external
  ``SgInc loc mt``,  ``include $mt$``,  include
  ``SgMod loc True lsmt``,  ``module rec $list:lsmt$``,  module rec
  ``SgMod loc False lsmt``,  ``module $list:lsmt$``,  module non rec
  ``SgMod loc b lsmt``,  ``module $flag:b$ $list:lsmt$``,  module
  ``SgMty loc s mt``,  ``module type $s$ = $mt$``,  module type
  ``SgOpn loc ls``,  ``open $list:ls$``,  open
  ``SgTyp loc ltd``,  ``type $list:ltd$``,  type declaration
  ``SgUse loc s lsil``,  ``# $str:s$ $list:lsil$``,  ... internal use ... <a href="#t_sig_item_1">(1)</a>
  ``SgVal loc s t``,  ``value $s$ : $t$``,  value


1. Same remark as for ``str_item`` above.

module_expr
^^^^^^^^^^^

.. csv-table:: Module expressions of the language
  :header: "Node",``<:module_expr< ... >>``,"Comment"

  ``MeAcc loc me1 me2``,  ``$me1$ . $me2$``,  access
  ``MeApp loc me1 me2``,  ``$me1$ $me2$``,  application
  ``MeFun loc s mt me``,  ``functor ($s$ : $mt$) -> $me$``,  functor
  ``MeStr loc lsi``,  ``struct $list:lsi$ end``,  struct
  ``MeTyc loc me mt``,  ``($me$ : $mt$)``,  module type constraint
  ``MeUid loc s``,  ``$uid:s$``,  uppercase identifier
  ``MeUnp loc e None``,  ``(value $e$)``,  module unpacking
  ``MeUnp loc e (Some mt)``,  ``(value $e$ : $mt$)``,  module unpacking

module_type
^^^^^^^^^^^

.. csv-table:: Module expressions of the language
  :header: "Node",``<:module_type< ... >>``,"Comment"

  ``MtAcc loc mt1 mt2``,  ``$mt1$ . $mt2$``,  access
  ``MtApp loc mt1 mt2``,  ``$mt1$ $mt2$``,  application
  ``MtFun loc s mt1 mt2``,  ``functor ($s$ : $mt1$) -> $mt2$``,  functor
  ``MtLid loc s``,  ``$lid:s$``,  lowercase identifier
  ``MtQuo loc s``,  ``' $s$``,  abstract
  ``MtSig loc lsi``,  ``sig $list:lsi$ end``,  signature
  ``MtTyo loc me``,  ``module type of $me$``,  of module expression
  ``MtUid loc s``,  ``$uid:s$``,  uppercase identifier
  ``MtWit loc mt lwc``,  ``$mt$ with $list:lwc$``,  with construction

classes...
----------


class_expr
^^^^^^^^^^

.. csv-table:: Class expressions of the language
  :header: "Node",``<:class_expr< ... >>``,"Comment"

  ``CeApp loc ce e``,  ``$ce$ $e$``,  application
  ``CeCon loc ls lt``,  ``[ $list:lt$ ] $list:ls$``,  constructor
  ``CeFun loc p ce``,  ``fun $p$ -> $ce$``,  function
  ``CeLet loc True lpe ce``,  ``let rec $list:lpe$ in $ce$``,  let rec
  ``CeLet loc False lpe ce``,  ``let $list:lpe$ in $ce$``,  let non rec
  ``CeLet loc b lpe ce``,  ``let $flag:b$ $list:lpe$ in $ce$``,  let
  ``CeStr loc None lcsi``,  ``object $list:lcsi$ end``,  object
  ``CeStr loc (Some p) lcsi``,  ``object ($p$) $list:lcsi$ end``,  object
  ``CeStr loc op lcsi``,  ``object $opt:op$ $list:lcsi$ end``,  object
  ``CeTyc loc ce ct``,  ``($ce$ : $ct$)``,  class type constraint

class_type
^^^^^^^^^^

.. csv-table:: Class expressions of the language
  :header: "Node",``<:class_type< ... >>``,"Comment"

  ``CtAcc loc ct1 ct2``,  ``$ct1$ . $ct2$``,  access
  ``CtApp loc ct1 ct2``,  ``$ct1$ $ct2$``,  application
  ``CtCon loc ct lt``,  ``$ct$ [ $list:lt$ ]``,  constructor
  ``CtFun loc t ct``,  ``[ $t$ ] -> $ct$``,  arrow
  ``CtIde loc s``,  ``$id:s$``,  identifier
  ``CtSig loc None lcsi``,  ``object $list:lcsi$ end``,  object
  ``CtSig loc (Some t) lcsi``,  ``object ($t$) $list:lcsi$ end``,  object
  ``CtSig loc ot lcsi``,  ``object $opt:ot$ $list:lcsi$ end``,  object

class_str_item
^^^^^^^^^^^^^^

.. csv-table:: Class structure items of the language
  :header: "Node",``<:class_str_item< ... >>``,"Comment"

  ``CrCtr loc t1 t2``,  ``type $t1$ = $t2$``,  type constraint
  ``CrDcl loc lcsi``,  ``declare $list:lcsi$ end``,  declaration list
  ``CrInh loc ce None``,  ``inherit $ce$``,  inheritance
  ``CrInh loc ce (Some s)``,  ``inherit $ce$ $opt:Some s$``,  inheritance
  ``CrInh loc ce os``,  ``inherit $ce$ $opt:os$``,  inheritance
  ``CrIni loc e``,  ``initializer $e$``,  initialization
  ``CrMth loc True True s None e``,  ``method! private $lid:s$ = $e$``,  method
  ``CrMth loc True True s (Some t) e``,  ``method! private $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc True True s ot e``,  ``method! private $lid:s$ $opt:ot$ = $e$``,  method
  ``CrMth loc True False s None e``,  ``method! $lid:s$ = $e$``,  method
  ``CrMth loc True False s (Some t) e``,  ``method! $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc True False s ot e``,  ``method! $lid:s$ $opt:ot$ = $e$``,  method
  ``CrMth loc True b2 s None e``,  ``method! $priv:b2$ $lid:s$ = $e$``,  method
  ``CrMth loc True b2 s (Some t) e``,  ``method! $priv:b2$ $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc True b2 s ot e``,  ``method! $priv:b2$ $lid:s$ $opt:ot$ = $e$``,  method
  ``CrMth loc False True s None e``,  ``method private $lid:s$ = $e$``,  method
  ``CrMth loc False True s (Some t) e``,  ``method private $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc False True s ot e``,  ``method private $lid:s$ $opt:ot$ = $e$``,  method
  ``CrMth loc False False s None e``,  ``method $lid:s$ = $e$``,  method
  ``CrMth loc False False s (Some t) e``,  ``method $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc False False s ot e``,  ``method $lid:s$ $opt:ot$ = $e$``,  method
  ``CrMth loc False b2 s None e``,  ``method $priv:b2$ $lid:s$ = $e$``,  method
  ``CrMth loc False b2 s (Some t) e``,  ``method $priv:b2$ $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc False b2 s ot e``,  ``method $priv:b2$ $lid:s$ $opt:ot$ = $e$``,  method
  ``CrMth loc b1 True s None e``,  ``method $!:b1$ private $lid:s$ = $e$``,  method
  ``CrMth loc b1 True s (Some t) e``,  ``method $!:b1$ private $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc b1 True s ot e``,  ``method $!:b1$ private $lid:s$ $opt:ot$ = $e$``,  method
  ``CrMth loc b1 False s None e``,  ``method $!:b1$ $lid:s$ = $e$``,  method
  ``CrMth loc b1 False s (Some t) e``,  ``method $!:b1$ $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc b1 False s ot e``,  ``method $!:b1$ $lid:s$ $opt:ot$ = $e$``,  method
  ``CrMth loc b1 b2 s None e``,  ``method $!:b1$ $priv:b2$ $lid:s$ = $e$``,  method
  ``CrMth loc b1 b2 s (Some t) e``,  ``method $!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$``,  method
  ``CrMth loc b1 b2 s ot e``,  ``method $!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$``,  method
  ``CrVal loc True True s e``,  ``value! mutable $lid:s$ = $e$``,  value
  ``CrVal loc True False s e``,  ``value! $lid:s$ = $e$``,  value
  ``CrVal loc True b2 s e``,  ``value! $flag:b2$ $lid:s$ = $e$``,  value
  ``CrVal loc False True s e``,  ``value mutable $lid:s$ = $e$``,  value
  ``CrVal loc False False s e``,  ``value $lid:s$ = $e$``,  value
  ``CrVal loc False b2 s e``,  ``value $flag:b2$ $lid:s$ = $e$``,  value
  ``CrVal loc b1 True s e``,  ``value $!:b1$ mutable $lid:s$ = $e$``,  value
  ``CrVal loc b1 False s e``,  ``value $!:b1$ $lid:s$ = $e$``,  value
  ``CrVal loc b1 b2 s e``,  ``value $!:b1$ $flag:b2$ $lid:s$ = $e$``,  value
  ``CrVav loc True s t``,  ``value virtual mutable $lid:s$ : $t$``,  virtual value
  ``CrVav loc False s t``,  ``value virtual $lid:s$ : $t$``,  virtual value
  ``CrVav loc b s t``,  ``value virtual $flag:b$ $lid:s$ : $t$``,  virtual value
  ``CrVir loc True s t``,  ``method virtual private $lid:s$ : $t$``,  virtual method
  ``CrVir loc False s t``,  ``method virtual $lid:s$ : $t$``,  virtual method
  ``CrVir loc b s t``,  ``method virtual $flag:b$ $lid:s$ : $t$``,  virtual method

class_sig_item
^^^^^^^^^^^^^^

.. csv-table:: Class signature items of the language
  :header: "Node",``<:class_sig_item< ... >>``,"Comment"

  ``CgCtr loc t1 t2``,  ``type $t1$ = $t2$``,  type constraint
  ``CgDcl loc lcsi``,  ``declare $list:lcsi$ end``,  declare
  ``CgInh loc ct``,  ``inherit $ct$``,  inheritance
  ``CgMth loc True s t``,  ``method private $lid:s$ : $t$``,  method
  ``CgMth loc False s t``,  ``method $lid:s$ : $t$``,  method
  ``CgMth loc b s t``,  ``method $flag:b$ $lid:s$ : $t$``,  method
  ``CgVal loc True s t``,  ``value mutable $lid:s$ : $t$``,  value
  ``CgVal loc False s t``,  ``value $lid:s$ : $t$``,  value
  ``CgVal loc b s t``,  ``value $flag:b$ $lid:s$ : $t$``,  value
  ``CgVir loc True s t``,  ``method virtual private $lid:s$ : $t$``,  virtual method
  ``CgVir loc False s t``,  ``method virtual $lid:s$ : $t$``,  virtual method
  ``CgVir loc b s t``,  ``method virtual $flag:b$ $lid:s$ : $t$``,  virtual method

other
-----


type_decl
^^^^^^^^^

What is after 'type' or 'and' in a type declaration.

.. csv-table:: Type declarations of the language
  :header: "Node",``<:type_decl< ... >>``,"Comment"

  ``{tdNam=ls;tdPrm=ltv;tdPrv=True;tdDef=t;tdCon=ltt}``,  ``$tp:ls$ $list:ltv$ = private $t$ $list:ltt$``
  ``{tdNam=ls;tdPrm=ltv;tdPrv=False;tdDef=t;tdCon=ltt}``,  ``$tp:ls$ $list:ltv$ = $t$ $list:ltt$``
  ``{tdNam=ls;tdPrm=ltv;tdPrv=b;tdDef=t;tdCon=ltt}``,  ``$tp:ls$ $list:ltv$ = $priv:b$ $t$ $list:ltt$``


with_constr
^^^^^^^^^^^

"With" possibly following a module type.

.. csv-table:: "With" possibly following a module type.
  :header: "Node",``<:with_constr< ... >>``,"Comment"

  ``WcMod loc ls me``,  ``module $list:ls$ = $me$``,  with module
  ``WcMos loc ls me``,  ``module $list:ls$ := $me$``,  with module substitution
  ``WcTyp loc ls ltv True t``,  ``type $list:ls$ $list:ltv$ = private $t$``,  with type
  ``WcTyp loc ls ltv False t``,  ``type $list:ls$ $list:ltv$ = $t$``,  with type
  ``WcTyp loc ls ltv b t``,  ``type $list:ls$ $list:ltv$ = $flag:b$ $t$``,  with type
  ``WcTys loc ls ltv t``,  ``type $list:ls$ $list:ltv$ := $t$``,  with type substitution


poly_variant
^^^^^^^^^^^^

Polymorphic variants.

.. csv-table:: "With" possibly following a module type.
  :header: "Node",``<:poly_variant< ... >>``,"Comment"

  ``PvTag loc s True []``,  ```$s$``,  constructor
  ``PvTag loc s True lt``,  ```$s$ of &amp; $list:lt$``,  constructor
  ``PvTag loc s False lt``,  ```$s$ of $list:lt$``,  constructor
  ``PvTag loc s b lt``,  ```$s$ of $flag:b$ $list:lt$``,  constructor
  ``PvInh loc t``,  ``$t$``,  type

.. ;;; Local Variables: ***
.. ;;; mode:rst ***
.. ;;; End: ***
