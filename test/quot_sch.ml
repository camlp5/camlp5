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
<:expr< (~ $s$) >>
<:expr< (~ $_:s$) >>
<:expr< (~ $s$ $e$) >>
<:expr< (~ $_:s$ $e$) >>
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
<:expr< (new $ls$) >>
<:expr< (new $_:ls$) >>
(MLast.ExObj loc (Ploc.VaVal op) (Ploc.VaVal lcstri))
(MLast.ExObj loc op lcstri)
<:expr< (? $s$) >>
<:expr< (? $_:s$) >>
<:expr< (? $s$ $e$) >>
<:expr< (? $_:s$ $e$) >>
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
(MLast.ExVrn loc (Ploc.VaVal s))
(MLast.ExVrn loc s)
<:expr< (while $e$ $list:le$) >>
<:expr< (while $e$ $_list:le$) >>
<:patt< $p1$. $p2$ >>
<:patt< (as $p1$ $p2$) >>
<:patt< $anti:p$ >>
<:patt< _ >>
<:patt< ($p1$ $p2$) >>
<:patt< #( $list:lp$ ) >>
<:patt< #( $_list:lp$ ) >>
<:patt< $chr:s$ >>
<:patt< $_chr:s$ >>
<:patt< $int:s$ >>
<:patt< $_int:s$ >>
<:patt< $int32:s$ >>
<:patt< $_int32:s$ >>
<:patt< $int64:s$ >>
<:patt< $_int64:s$ >>
<:patt< $nativeint:s$ >>
<:patt< $_nativeint:s$ >>
<:patt< $flo:s$ >>
<:patt< $_flo:s$ >>
<:patt< (~ $s$) >>
<:patt< (~ $_:s$) >>
<:patt< (~ $s$ $p$) >>
<:patt< (~ $_:s$ $p$) >>
<:patt< $lid:s$ >>
<:patt< $_lid:s$ >>
<:patt< (? $s$) >>
<:patt< (? $_:s$) >>
<:patt< (? ($s$ $p$)) >>
<:patt< (? ($_:s$ $p$)) >>
<:patt< (? ($s$ $p$) $e$) >>
<:patt< (? ($_:s$ $p$) $e$) >>
<:patt< (or $p1$ $p2$) >>
<:patt< (range $p1$ $p2$) >>
<:patt< { $list:lpp$ } >>
<:patt< { $_list:lpp$ } >>
<:patt< $str:s$ >>
<:patt< $_str:s$ >>
<:patt< (values $list:lp$) >>
<:patt< (values $_list:lp$) >>
<:patt< (: $p$ $t$) >>
(MLast.PaTyp loc (Ploc.VaVal ls))
(MLast.PaTyp loc ls)
<:patt< $uid:s$ >>
<:patt< $_uid:s$ >>
(MLast.PaVrn loc (Ploc.VaVal s))
(MLast.PaVrn loc s)
<:ctyp< $t1$. $t2$ >>
<:ctyp< (as $t1$ $t2$) >>
<:ctyp< _ >>
<:ctyp< ($t1$ $t2$) >>
<:ctyp< (-> $t1$ $t2$) >>
(MLast.TyCls loc (Ploc.VaVal ls))
(MLast.TyCls loc ls)
<:ctyp< (~ $s$ $t$) >>
<:ctyp< (~ $_:s$ $t$) >>
<:ctyp< $lid:s$ >>
<:ctyp< $_lid:s$ >>
<:ctyp< (== $t1$ $t2$) >>
<:ctyp< (object $list:lst$) >>
<:ctyp< (object $_list:lst$) >>
<:ctyp< (objectvar $list:lst$) >>
<:ctyp< (objectvar $_list:lst$) >>
(MLast.TyObj loc (Ploc.VaVal lst) (Ploc.VaVal b))
(MLast.TyObj loc lst b)
<:ctyp< (? $s$ $t$) >>
<:ctyp< (? $_:s$ $t$) >>
(MLast.TyPol loc (Ploc.VaVal ls) t)
(MLast.TyPol loc ls t)
(MLast.TyQuo loc (Ploc.VaVal s))
(MLast.TyQuo loc s)
<:ctyp< { $list:llsbt$ } >>
<:ctyp< { $_list:llsbt$ } >>
<:ctyp< (sum $list:llslt$) >>
<:ctyp< (sum $_list:llslt$) >>
<:ctyp< (* $list:lt$) >>
<:ctyp< (* $_list:lt$) >>
<:ctyp< $uid:s$ >>
<:ctyp< $_uid:s$ >>
(MLast.TyVrn loc (Ploc.VaVal lpv) None)
(MLast.TyVrn loc lpv None)
(MLast.TyVrn loc (Ploc.VaVal lpv) (Some None))
(MLast.TyVrn loc lpv (Some None))
(MLast.TyVrn loc (Ploc.VaVal lpv) (Some (Some (Ploc.VaVal []))))
(MLast.TyVrn loc lpv (Some (Some (Ploc.VaVal []))))
(MLast.TyVrn loc (Ploc.VaVal lpv) (Some (Some (Ploc.VaVal ls))))
(MLast.TyVrn loc lpv (Some (Some ls)))
(MLast.StCls loc (Ploc.VaVal lcd))
(MLast.StCls loc lcd)
(MLast.StClt loc (Ploc.VaVal lctd))
(MLast.StClt loc lctd)
(MLast.StDcl loc (Ploc.VaVal lstri))
(MLast.StDcl loc lstri)
<:str_item< (# $s$) >>
<:str_item< (# $_:s$) >>
<:str_item< (# $s$ $e$) >>
<:str_item< (# $_:s$ $e$) >>
(MLast.StDir loc (Ploc.VaVal s) (Ploc.VaVal oe))
(MLast.StDir loc s oe)
<:str_item< (exception $uid:s$ $list:lt$) >>
<:str_item< (exception $_uid:s$ $_list:lt$) >>
<:str_item< (exceptionrebind $uid:s$ $list:ls$) >>
<:str_item< (exceptionrebind $_uid:s$ $_list:ls$) >>
(MLast.StExc loc (Ploc.VaVal s) (Ploc.VaVal lt) (Ploc.VaVal ls))
(MLast.StExc loc s lt ls)
<:str_item< $exp:e$ >>
<:str_item< (external $s$ $t$ $list:ls$) >>
<:str_item< (external $_:s$ $t$ $_list:ls$) >>
<:str_item< (include $me$) >>
<:str_item< (module* $list:lsme$) >>
<:str_item< (module* $_list:lsme$) >>
<:str_item< (modulerec* $list:lsme$) >>
<:str_item< (modulerec* $_list:lsme$) >>
(MLast.StMod loc (Ploc.VaVal b) (Ploc.VaVal lsme))
(MLast.StMod loc b lsme)
<:str_item< (moduletype $s$ $mt$) >>
<:str_item< (moduletype $_:s$ $mt$) >>
<:str_item< (open $list:ls$) >>
<:str_item< (open $_list:ls$) >>
<:str_item< (type* $list:ltd$) >>
<:str_item< (type* $_list:ltd$) >>
<:str_item< (define* $list:lpe$) >>
<:str_item< (define* $_list:lpe$) >>
<:str_item< (definerec* $list:lpe$) >>
<:str_item< (definerec* $_list:lpe$) >>
(MLast.StVal loc (Ploc.VaVal b) (Ploc.VaVal lpe))
(MLast.StVal loc b lpe)
(MLast.SgCls loc (Ploc.VaVal lcd))
(MLast.SgCls loc lcd)
(MLast.SgClt loc (Ploc.VaVal lct))
(MLast.SgClt loc lct)
(MLast.SgDcl loc (Ploc.VaVal lsigi))
(MLast.SgDcl loc lsigi)
<:sig_item< (# $s$) >>
<:sig_item< (# $_:s$) >>
<:sig_item< (# $s$ $e$) >>
<:sig_item< (# $_:s$ $e$) >>
(MLast.SgDir loc (Ploc.VaVal s) (Ploc.VaVal oe))
(MLast.SgDir loc s oe)
<:sig_item< (exception $s$) >>
<:sig_item< (exception $_:s$) >>
<:sig_item< (exception $s$ $list:lt$) >>
<:sig_item< (exception $_:s$ $_list:lt$) >>
<:sig_item< (external $s$ $t$ $list:ls$) >>
<:sig_item< (external $_:s$ $t$ $_list:ls$) >>
<:sig_item< (include $me$) >>
<:sig_item< (module* $list:lsmt$) >>
<:sig_item< (module* $_list:lsmt$) >>
<:sig_item< (modulerec* $list:lsmt$) >>
<:sig_item< (modulerec* $_list:lsmt$) >>
(MLast.SgMod loc (Ploc.VaVal b) (Ploc.VaVal lsmt))
(MLast.SgMod loc b lsmt)
<:sig_item< (moduletype $s$ $mt$) >>
<:sig_item< (moduletype $_:s$ $mt$) >>
<:sig_item< (open $list:ls$) >>
<:sig_item< (open $_list:ls$) >>
<:sig_item< (type* $list:ltd$) >>
<:sig_item< (type* $_list:ltd$) >>
<:sig_item< (value $s$ $t$) >>
<:sig_item< (value $_:s$ $t$) >>
<:module_expr< $me1$. $me2$ >>
<:module_expr< ($me1$ $me2$) >>
<:module_expr< (functor $s$ $mt$ $me$) >>
<:module_expr< (functor $_:s$ $mt$ $me$) >>
<:module_expr< (struct $list:lstri$) >>
<:module_expr< (struct $_list:lstri$) >>
<:module_expr< (: $me$ $mt$) >>
<:module_expr< $uid:s$ >>
<:module_expr< $_uid:s$ >>
<:module_type< $mt1$.$mt2$ >>
<:module_type< ($mt1$ $mt2$) >>
<:module_type< (functor $s$ $mt1$ $mt2$) >>
<:module_type< (functor $_:s$ $mt1$ $mt2$) >>
<:module_type< $lid:s$ >>
<:module_type< $_lid:s$ >>
(MLast.MtQuo loc (Ploc.VaVal s))
(MLast.MtQuo loc s)
<:module_type< (sig $list:lsigi$) >>
<:module_type< (sig $_list:lsigi$) >>
<:module_type< $uid:s$ >>
<:module_type< $_uid:s$ >>
<:module_type< (with $mt$ $list:lwc$) >>
<:module_type< (with $mt$ $_list:lwc$) >>
<:with_constr< (type ($s$ $list:ltv$) $t$) >>
<:with_constr< (type ($_:s$ $_list:ltv$) $t$) >>
<:with_constr< (typeprivate ($s$ $list:ltv$) $t$) >>
<:with_constr< (typeprivate ($_:s$ $_list:ltv$) $t$) >>
(MLast.WcTyp loc (Ploc.VaVal s) (Ploc.VaVal ltv) (Ploc.VaVal b) t)
(MLast.WcTyp loc s ltv b t)
; <:with_constr< module $list:ls$ = $me$ >>
; <:with_constr< module $_list:ls$ = $me$ >>
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
; <:poly_variant< ` $s$ >>
; <:poly_variant< ` $_:s$ >>
; <:poly_variant< ` $s$ of $list:lt$ >>
; <:poly_variant< ` $_:s$ of $_list:lt$ >>
; <:poly_variant< ` $s$ of & $list:lt$ >>
; <:poly_variant< ` $_:s$ of & $_list:lt$ >>
; <:poly_variant< ` $s$ of $flag:b$ $list:lt$ >>
; <:poly_variant< ` $_:s$ of $_flag:b$ $_list:lt$ >>
; <:poly_variant< $t$ >>
