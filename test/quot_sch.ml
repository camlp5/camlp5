<:expr< $e1$.$e2$ >>
<:expr< $anti:e$ >>
<:expr< ($e1$ $e2$) >>
<:expr< $e1$.($e2$) >>
<:expr< #( $list:le$ ) >>
<:expr< #( $_list:le$ ) >>
<:expr< (assert $e$) >>
<:expr< (:= $e1$ $e2$) >>
(MLast.ExBae loc e (Ploc.VaVal le))
(MLast.ExBae loc e le)
<:expr< $chr:s$ >>
<:expr< $_chr:s$ >>
(MLast.ExCoe loc e (Some t1) t2)
(MLast.ExCoe loc e None t2)
<:expr< $flo:s$ >>
<:expr< $_flo:s$ >>
<:expr< (for $lid:s$ $e1$ $e2$ $list:le$) >>
<:expr< (for $_lid:s$ $e1$ $e2$ $_list:le$) >>
<:expr< (fordown $lid:s$ $e1$ $e2$ $list:le$) >>
<:expr< (fordown $_lid:s$ $e1$ $e2$ $_list:le$) >>
(MLast.ExFor loc (Ploc.VaVal s) e1 e2 (Ploc.VaVal b) (Ploc.VaVal le))
(MLast.ExFor loc s e1 e2 b le)
<:expr< (lambda_match ($list:lpwe$)) >>
<:expr< (lambda_match ($_list:lpwe$)) >>
<:expr< (if $e1$ $e2$ $e3$) >>
<:expr< $int:s$ >>
<:expr< $_int:s$ >>
<:expr< $int32:s$ >>
<:expr< $_int32:s$ >>
<:expr< $int64:s$ >>
<:expr< $_int64:s$ >>
<:expr< $nativeint:s$ >>
<:expr< $_nativeint:s$ >>
<:expr< ~$s$ >>
<:expr< ~$_:s$ >>
<:expr< (~$s$ $e$) >>
<:expr< (~$_:s$ $e$) >>
<:expr< (lazy $e$) >>
<:expr< (let ($list:lpe$) $e$) >>
<:expr< (let ($_list:lpe$) $e$) >>
<:expr< (letrec ($list:lpe$) $e$) >>
<:expr< (letrec ($_list:lpe$) $e$) >>
(MLast.ExLet loc (Ploc.VaVal b) (Ploc.VaVal lpe) e)
(MLast.ExLet loc b lpe e)
<:expr< $lid:s$ >>
<:expr< $_lid:s$ >>
<:expr< (letmodule $uid:s$ $me$ $e$) >>
<:expr< (letmodule $_uid:s$ $me$ $e$) >>
<:expr< (match $e$ ($list:lpwe$)) >>
<:expr< (match $e$ ($_list:lpwe$)) >>
(MLast.ExNew loc (Ploc.VaVal ls))
(MLast.ExNew loc ls)
(MLast.ExObj loc (Ploc.VaVal op) (Ploc.VaVal lcstri))
(MLast.ExObj loc op lcstri)
<:expr< ?$s$ >>
<:expr< ?$_:s$ >>
<:expr< (?$s$ $e$) >>
<:expr< (?$_:s$ $e$) >>
(MLast.ExOvr loc (Ploc.VaVal lse))
(MLast.ExOvr loc lse)
<:expr< { $list:lpe$ } >>
<:expr< { $_list:lpe$ } >>
<:expr< { with $e$ $list:lpe$ } >>
<:expr< { with $e$ $_list:lpe$ } >>
<:expr< (begin $list:le$) >>
<:expr< (begin $_list:le$) >>
(MLast.ExSnd loc e (Ploc.VaVal s))
(MLast.ExSnd loc e s)
<:expr< $e1$.[ $e2$ ] >>
<:expr< $str:s$ >>
<:expr< $_str:s$ >>
<:expr< (try $e$ ($list:lpwe$)) >>
<:expr< (try $e$ ($_list:lpwe$)) >>
<:expr< (values $list:le$) >>
<:expr< (values $_list:le$) >>
<:expr< (: $e$ $t$) >>
<:expr< $uid:s$ >>
<:expr< $_uid:s$ >>
<:expr< `$s$ >>
; <:expr< `$_:s$ >>
; <:expr< while $e$ do { $list:le$ } >>
; <:expr< while $e$ do { $_list:le$ } >>
; <:patt< $p1$ . $p2$ >>
; <:patt< ($p1$ as $p2$) >>
; <:patt< $anti:p$ >>
; <:patt< _ >>
; <:patt< $p1$ $p2$ >>
; <:patt< [| $list:lp$ |] >>
; <:patt< [| $_list:lp$ |] >>
; <:patt< $chr:s$ >>
; <:patt< $_chr:s$ >>
; <:patt< $int:s$ >>
; <:patt< $_int:s$ >>
; <:patt< $int32:s$ >>
; <:patt< $_int32:s$ >>
; <:patt< $int64:s$ >>
; <:patt< $_int64:s$ >>
; <:patt< $nativeint:s$ >>
; <:patt< $_nativeint:s$ >>
; <:patt< $flo:s$ >>
; <:patt< $_flo:s$ >>
; <:patt< ~$s$ >>
; <:patt< ~$_:s$ >>
; <:patt< ~$s$: $p$ >>
; <:patt< ~$_:s$: $p$ >>
; <:patt< $lid:s$ >>
; <:patt< $_lid:s$ >>
; <:patt< ?$s$ >>
; <:patt< ?$_:s$ >>
; <:patt< ?$s$: ($p$) >>
; <:patt< ?$_:s$: ($p$) >>
; <:patt< ?$s$: ($p$ = $e$) >>
; <:patt< ?$_:s$: ($p$ = $e$) >>
; <:patt< $p1$ | $p2$ >>
; <:patt< $p1$ .. $p2$ >>
; <:patt< { $list:lpp$ } >>
; <:patt< { $_list:lpp$ } >>
; <:patt< $str:s$ >>
; <:patt< $_str:s$ >>
; <:patt< ($list:lp$) >>
; <:patt< ($_list:lp$) >>
; <:patt< ($p$ : $t$) >>
; <:patt< # $list:ls$ >>
; <:patt< # $_list:ls$ >>
; <:patt< $uid:s$ >>
; <:patt< $_uid:s$ >>
; <:patt< ` $s$ >>
; <:patt< ` $_:s$ >>
; <:ctyp< $t1$ . $t2$ >>
; <:ctyp< $t1$ as $t2$ >>
; <:ctyp< _ >>
; <:ctyp< $t1$ $t2$ >>
; <:ctyp< $t1$ -> $t2$ >>
; <:ctyp< # $list:ls$ >>
; <:ctyp< # $_list:ls$ >>
; <:ctyp< ~$s$: $t$ >>
; <:ctyp< ~$_:s$: $t$ >>
; <:ctyp< $lid:s$ >>
; <:ctyp< $_lid:s$ >>
; <:ctyp< $t1$ == $t2$ >>
; <:ctyp< < $list:lst$ > >>
; <:ctyp< < $_list:lst$ > >>
; <:ctyp< < $list:lst$ .. > >>
; <:ctyp< < $_list:lst$ .. > >>
; <:ctyp< < $list:lst$ $flag:b$ > >>
; <:ctyp< < $_list:lst$ $_flag:b$ > >>
; <:ctyp< ?$s$: $t$ >>
; <:ctyp< ?$_:s$: $t$ >>
; <:ctyp< ! $list:ls$ . $t$ >>
; <:ctyp< ! $_list:ls$ . $t$ >>
; <:ctyp< ' $s$ >>
; <:ctyp< ' $_:s$ >>
; <:ctyp< { $list:llsbt$ } >>
; <:ctyp< { $_list:llsbt$ } >>
; <:ctyp< [ $list:llslt$ ] >>
; <:ctyp< [ $_list:llslt$ ] >>
; <:ctyp< ( $list:lt$ ) >>
; <:ctyp< ( $_list:lt$ ) >>
; <:ctyp< $uid:s$ >>
; <:ctyp< $_uid:s$ >>
; <:ctyp< [ = $list:lpv$ ] >>
; <:ctyp< [ = $_list:lpv$ ] >>
; <:ctyp< [ > $list:lpv$ ] >>
; <:ctyp< [ > $_list:lpv$ ] >>
; <:ctyp< [ < $list:lpv$ ] >>
; <:ctyp< [ < $_list:lpv$ ] >>
; <:ctyp< [ < $list:lpv$ > $list:ls$ ] >>
; <:ctyp< [ < $_list:lpv$ > $_list:ls$ ] >>
; <:str_item< class $list:lcd$ >>
; <:str_item< class $_list:lcd$ >>
; <:str_item< class type $list:lctd$ >>
; <:str_item< class type $_list:lctd$ >>
; <:str_item< declare $list:lstri$ end >>
; <:str_item< declare $_list:lstri$ end >>
; <:str_item< # $s$ >>
; <:str_item< # $_:s$ >>
; <:str_item< # $s$ $e$ >>
; <:str_item< # $_:s$ $e$ >>
; <:str_item< # $s$ $opt:oe$ >>
; <:str_item< # $_:s$ $_opt:oe$ >>
; <:str_item< exception $s$ of $list:lt$ >>
; <:str_item< exception $_:s$ of $_list:lt$ >>
; <:str_item< exception $s$ of $list:lt$ = $list:ls$ >>
; <:str_item< exception $_:s$ of $_list:lt$ = $_list:ls$ >>
; <:str_item< $exp:e$ >>
; <:str_item< external $s$ : $t$ = $list:ls$ >>
; <:str_item< external $_:s$ : $t$ = $_list:ls$ >>
; <:str_item< include $me$ >>
; <:str_item< module $flag:b$ $list:lsme$ >>
; <:str_item< module $_flag:b$ $_list:lsme$ >>
; <:str_item< module type $s$ = $mt$ >>
; <:str_item< module type $_:s$ = $mt$ >>
; <:str_item< open $list:ls$ >>
; <:str_item< open $_list:ls$ >>
; <:str_item< type $list:ltd$ >>
; <:str_item< type $_list:ltd$ >>
; <:str_item< value $flag:b$ $list:lpe$ >>
; <:str_item< value $_flag:b$ $_list:lpe$ >>
; <:sig_item< class $list:lcd$ >>
; <:sig_item< class $_list:lcd$ >>
; <:sig_item< class type $list:lct$ >>
; <:sig_item< class type $_list:lct$ >>
; <:sig_item< declare $list:lsigi$ end >>
; <:sig_item< declare $_list:lsigi$ end >>
; <:sig_item< # $s$ >>
; <:sig_item< # $_:s$ >>
; <:sig_item< # $s$ $e$ >>
; <:sig_item< # $_:s$ $e$ >>
; <:sig_item< # $s$ $opt:oe$ >>
; <:sig_item< # $_:s$ $_opt:oe$ >>
; <:sig_item< exception $s$ >>
; <:sig_item< exception $_:s$ >>
; <:sig_item< exception $s$ of $list:lt$ >>
; <:sig_item< exception $_:s$ of $_list:lt$ >>
; <:sig_item< external $s$ : $t$ = $list:ls$ >>
; <:sig_item< external $_:s$ : $t$ = $_list:ls$ >>
; <:sig_item< include $me$ >>
; <:sig_item< module $flag:b$ $list:lsmt$ >>
; <:sig_item< module $_flag:b$ $_list:lsmt$ >>
; <:sig_item< module type $s$ = $mt$ >>
; <:sig_item< module type $_:s$ = $mt$ >>
; <:sig_item< open $list:ls$ >>
; <:sig_item< open $_list:ls$ >>
; <:sig_item< type $list:ltd$ >>
; <:sig_item< type $_list:ltd$ >>
; <:sig_item< value $s$ : $t$ >>
; <:sig_item< value $_:s$ : $t$ >>
; <:module_expr< $me1$ . $me2$ >>
; <:module_expr< $me1$ $me2$ >>
; <:module_expr< functor ($s$ : $mt$) -> $me$ >>
; <:module_expr< functor ($_:s$ : $mt$) -> $me$ >>
; <:module_expr< struct $list:lstri$ end >>
; <:module_expr< struct $_list:lstri$ end >>
; <:module_expr< ($me$ : $mt$) >>
; <:module_expr< $uid:s$ >>
; <:module_expr< $_uid:s$ >>
; <:module_type< $mt1$ . $mt2$ >>
; <:module_type< $mt1$ $mt2$ >>
; <:module_type< functor ($s$ : $mt1$) -> $mt2$ >>
; <:module_type< functor ($_:s$ : $mt1$) -> $mt2$ >>
; <:module_type< $lid:s$ >>
; <:module_type< $_lid:s$ >>
; <:module_type< ' $s$ >>
; <:module_type< ' $_:s$ >>
; <:module_type< sig $list:lsigi$ end >>
; <:module_type< sig $_list:lsigi$ end >>
; <:module_type< $uid:s$ >>
; <:module_type< $_uid:s$ >>
; <:module_type< $mt$ with $list:lwc$ >>
; <:module_type< $mt$ with $_list:lwc$ >>
; <:class_expr< $ce$ $e$ >>
; <:class_expr< $list:ls$ [ $list:lt$ ] >>
; <:class_expr< $_list:ls$ [ $_list:lt$ ] >>
; <:class_expr< fun $p$ -> $ce$ >>
; <:class_expr< let $flag:b$ $list:lpe$ in $ce$ >>
; <:class_expr< let $_flag:b$ $_list:lpe$ in $ce$ >>
; <:class_expr< object $opt:op$ $list:lcstri$ end >>
; <:class_expr< object $_opt:op$ $_list:lcstri$ end >>
; <:class_expr< ($ce$ : $ct$) >>
; <:class_type< $list:ls$ [ $list:lt$ ] >>
; <:class_type< $_list:ls$ [ $_list:lt$ ] >>
; <:class_type< [ $t$ ] -> $ct$ >>
; <:class_type< object $list:lcsigi$ end >>
; <:class_type< object $_list:lcsigi$ end >>
; <:class_type< object ($t$) $list:lcsigi$ end >>
; <:class_type< object ($t$) $_list:lcsigi$ end >>
; <:class_type< object $opt:ot$ $list:lcsigi$ end >>
; <:class_type< object $_opt:ot$ $_list:lcsigi$ end >>
; <:class_str_item< type $t1$ = $t2$ >>
; <:class_str_item< declare $list:lcstri$ end >>
; <:class_str_item< declare $_list:lcstri$ end >>
; <:class_str_item< inherit $ce$ >>
; <:class_str_item< inherit $ce$ $_opt:os$ >>
; <:class_str_item< initializer $e$ >>
; <:class_str_item< method $s$ = $e$ >>
; <:class_str_item< method $_:s$ = $e$ >>
; <:class_str_item< method $s$ : $t$ = $e$ >>
; <:class_str_item< method $_:s$ : $t$ = $e$ >>
; <:class_str_item< method private $s$ = $e$ >>
; <:class_str_item< method private $_:s$ = $e$ >>
; <:class_str_item< method private $s$ : $t$ = $e$ >>
; <:class_str_item< method private $_:s$ : $t$ = $e$ >>
; <:class_str_item< method $flag:b$ $s$ $opt:ot$ = $e$ >>
; <:class_str_item< method $_flag:b$ $_:s$ $_opt:ot$ = $e$ >>
; <:class_str_item< value $s$ = $e$ >>
; <:class_str_item< value $_:s$ = $e$ >>
; <:class_str_item< value mutable $s$ = $e$ >>
; <:class_str_item< value mutable $_:s$ = $e$ >>
; <:class_str_item< value $flag:b$ $s$ = $e$ >>
; <:class_str_item< value $_flag:b$ $_:s$ = $e$ >>
; <:class_str_item< method virtual $s$ : $t$ >>
; <:class_str_item< method virtual $_:s$ : $t$ >>
; <:class_str_item< method virtual private $s$ : $t$ >>
; <:class_str_item< method virtual private $_:s$ : $t$ >>
; <:class_str_item< method virtual $flag:b$ $s$ : $t$ >>
; <:class_str_item< method virtual $_flag:b$ $_:s$ : $t$ >>
; <:class_sig_item< type $t1$ = $t2$ >>
; <:class_sig_item< declare $list:lcsigi$ end >>
; <:class_sig_item< declare $_list:lcsigi$ end >>
; <:class_sig_item< inherit $ct$ >>
; <:class_sig_item< method $s$ : $t$ >>
; <:class_sig_item< method $_:s$ : $t$ >>
; <:class_sig_item< method private $s$ : $t$ >>
; <:class_sig_item< method private $_:s$ : $t$ >>
; <:class_sig_item< method $flag:b$ $s$ : $t$ >>
; <:class_sig_item< method $_flag:b$ $_:s$ : $t$ >>
; <:class_sig_item< value $s$ : $t$ >>
; <:class_sig_item< value $_:s$ : $t$ >>
; <:class_sig_item< value mutable $s$ : $t$ >>
; <:class_sig_item< value mutable $_:s$ : $t$ >>
; <:class_sig_item< value $flag:b$ $s$ : $t$ >>
; <:class_sig_item< value $_flag:b$ $_:s$ : $t$ >>
; <:class_sig_item< method virtual $s$ : $t$ >>
; <:class_sig_item< method virtual $_:s$ : $t$ >>
; <:class_sig_item< method virtual private $s$ : $t$ >>
; <:class_sig_item< method virtual private $_:s$ : $t$ >>
; <:class_sig_item< method virtual $flag:b$ $s$ : $t$ >>
; <:class_sig_item< method virtual $_flag:b$ $_:s$ : $t$ >>
; <:with_constr< type $s$ $list:ltv$ = $t$ >>
; <:with_constr< type $_:s$ $_list:ltv$ = $t$ >>
; <:with_constr< type $s$ $list:ltv$ = private $t$ >>
; <:with_constr< type $_:s$ $_list:ltv$ = private $t$ >>
; <:with_constr< type $s$ $list:ltv$ = $flag:b$ $t$ >>
; <:with_constr< type $_:s$ $_list:ltv$ = $_flag:b$ $t$ >>
; <:with_constr< module $list:ls$ = $me$ >>
; <:with_constr< module $_list:ls$ = $me$ >>
; <:poly_variant< ` $s$ >>
; <:poly_variant< ` $_:s$ >>
; <:poly_variant< ` $s$ of $list:lt$ >>
; <:poly_variant< ` $_:s$ of $_list:lt$ >>
; <:poly_variant< ` $s$ of & $list:lt$ >>
; <:poly_variant< ` $_:s$ of & $_list:lt$ >>
; <:poly_variant< ` $s$ of $flag:b$ $list:lt$ >>
; <:poly_variant< ` $_:s$ of $_flag:b$ $_list:lt$ >>
; <:poly_variant< $t$ >>
