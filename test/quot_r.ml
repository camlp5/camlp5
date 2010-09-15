(* $Id: quot_r.ml,v 6.5 2010/09/15 19:31:47 deraugla Exp $ *)

(* dot *)
<:ctyp< $t1$ . $t2$ >>;
(* alias *)
<:ctyp< $t1$ as $t2$ >>;
(* wildcard *)
<:ctyp< _ >>;
(* application *)
<:ctyp< $t1$ $t2$ >>;
(* arrow *)
<:ctyp< $t1$ -> $t2$ >>;
(* class *)
<:ctyp< # $list:ls$ >>;
<:ctyp< # $_list:ls$ >>;

(* label *)
<:ctyp< ~$s$: $t$ >>;
<:ctyp< ~$_:s$: $t$ >>;

(* lowercase identifier *)
<:ctyp< $lid:s$ >>;
<:ctyp< $_lid:s$ >>;

(* manifest *)
<:ctyp< $t1$ == $t2$ >>;

(* object *)
<:ctyp< < $list:lst$ .. > >>;
(* object *)
<:ctyp< < $list:lst$ > >>;
(* object (general) *)
<:ctyp< < $list:lst$ $flag:b$ > >>;
<:ctyp< < $list:lst$ $_flag:b$ > >>;
<:ctyp< < $_list:lst$ .. > >>;
<:ctyp< < $_list:lst$ > >>;
<:ctyp< < $_list:lst$ $flag:b$ > >>;
<:ctyp< < $_list:lst$ $_flag:b$ > >>;

(* option label *)
<:ctyp< ?$s$: $t$ >>;
<:ctyp< ?$_:s$: $t$ >>;

MLast.TyPck loc mt;

(* polymorph *)
<:ctyp< ! $list:ls$ . $t$ >>;
<:ctyp< ! $_list:ls$ . $t$ >>;

(* variable *)
<:ctyp< '$s$ >>;
<:ctyp< '$_:s$ >>;

(* record *)
<:ctyp< { $list:llsbt$ } >>;
<:ctyp< { $_list:llsbt$ } >>;

(* sum *)
<:ctyp< [ $list:llslt$ ] >>;
<:ctyp< [ $_list:llslt$ ] >>;

(* t-uple *)
<:ctyp< ( $list:lt$ ) >>;
<:ctyp< ( $_list:lt$ ) >>;

(* uppercase identifier *)
<:ctyp< $uid:s$ >>;
<:ctyp< $_uid:s$ >>;

(* variant *)
<:ctyp< [ = $list:lpv$ ] >>;
(* variant *)
<:ctyp< [ > $list:lpv$ ] >>;
<:ctyp< [ < $list:lpv$ > $list:ls$ ] >>;
(* variant *)
<:ctyp< [ < $list:lpv$ > $_list:ls$ ] >>;
MLast.TyVrn loc (Ploc.VaVal lpv) (Some ls);
MLast.TyVrn loc (Ploc.VaVal lpv) ls;
<:ctyp< [ = $_list:lpv$ ] >>;
<:ctyp< [ > $_list:lpv$ ] >>;
<:ctyp< [ < $_list:lpv$ > $list:ls$ ] >>;
<:ctyp< [ < $_list:lpv$ > $_list:ls$ ] >>;
MLast.TyVrn loc lpv (Some ls);
MLast.TyVrn loc lpv ls;

MLast.TyXtr loc s None;
MLast.TyXtr loc s (Some (Ploc.VaVal t));
MLast.TyXtr loc s (Some t);
MLast.TyXtr loc s t;

<:poly_variant< `$s$ of & $list:lt$ >>;
<:poly_variant< `$s$ of & $_list:lt$ >>;
<:poly_variant< `$s$ of $list:lt$ >>;
<:poly_variant< `$s$ of $_list:lt$ >>;
<:poly_variant< `$s$ of $flag:b$ $list:lt$ >>;
<:poly_variant< `$s$ of $flag:b$ $_list:lt$ >>;
<:poly_variant< `$s$ of $_flag:b$ $list:lt$ >>;
<:poly_variant< `$s$ of $_flag:b$ $_list:lt$ >>;
<:poly_variant< `$_:s$ of & $list:lt$ >>;
<:poly_variant< `$_:s$ of & $_list:lt$ >>;
<:poly_variant< `$_:s$ of $list:lt$ >>;
<:poly_variant< `$_:s$ of $_list:lt$ >>;
<:poly_variant< `$_:s$ of $flag:b$ $list:lt$ >>;
<:poly_variant< `$_:s$ of $flag:b$ $_list:lt$ >>;
<:poly_variant< `$_:s$ of $_flag:b$ $list:lt$ >>;
<:poly_variant< `$_:s$ of $_flag:b$ $_list:lt$ >>;

MLast.PvInh t;

(* dot *)
<:patt< $p1$ . $p2$ >>;
(* alias *)
<:patt< ($p1$ as $p2$) >>;
(* antiquotation <a href="#patt_1">(1)</a> *)
<:patt< $anti:p$ >>;
(* wildcard *)
<:patt< _ >>;
(* application *)
<:patt< $p1$ $p2$ >>;
(* array *)
<:patt< [| $list:lp$ |] >>;
<:patt< [| $_list:lp$ |] >>;
(* character *)
<:patt< $chr:s$ >>;
<:patt< $_chr:s$ >>;

(* integer *)
<:patt< $int:s1$ >>;
<:patt< $_int:s1$ >>;
(* integer 32 bits *)
<:patt< $int32:s1$ >>;
<:patt< $_int32:s1$ >>;
(* integer 64 bits *)
<:patt< $int64:s1$ >>;
<:patt< $_int64:s1$ >>;
(* native integer *)
<:patt< $nativeint:s1$ >>;
<:patt< $_nativeint:s1$ >>;

(* float *)
<:patt< $flo:s$ >>;
<:patt< $_flo:s$ >>;

(* label *)
<:patt< ~{$p1$} >>;
(* label *)
<:patt< ~{$p1$ = $p2$} >>;
(* label *)
<:patt< ~{$p1$ $opt:p2$} >>;
(* label *)
<:patt< ~{$p1$ $_opt:p2$} >>;

(* lazy *)
<:patt< lazy $p$ >>;
(* lowercase identifier *)
<:patt< $lid:s$ >>;
<:patt< $_lid:s$ >>;

(* option label *)
<:patt< ?{$p$} >>;
(* option label *)
<:patt< ?{$p$ = $e$} >>;
(* option label *)
<:patt< ?{$p$ $opt:e$} >>;
(* option label *)
<:patt< ?{$p$ $_opt:e$} >>;

(* or *)
<:patt< $p1$ | $p2$ >>;

(* record *)
<:patt< { $list:lpp$ } >>;
<:patt< { $_list:lpp$ } >>;

MLast.PaRng loc p1 p2;
MLast.PaStr loc (Ploc.VaVal s);
MLast.PaStr loc s;
MLast.PaTup loc (Ploc.VaVal lp);
MLast.PaTup loc lp;
MLast.PaTyc loc p t;
MLast.PaTyp loc (Ploc.VaVal ls);
MLast.PaTyp loc ls;
MLast.PaUid loc (Ploc.VaVal s);
MLast.PaUid loc s;
MLast.PaVrn loc (Ploc.VaVal s);
MLast.PaVrn loc s;
MLast.PaXtr loc s None;
MLast.PaXtr loc s (Some (Ploc.VaVal p));
MLast.PaXtr loc s (Some p);
MLast.PaXtr loc s p;

<:expr< $e1$ . $e2$ >>;
<:expr< $anti:e$ >>;
<:expr< $e1$ $e2$ >>;
<:expr< $e1$.($e2$) >>;
<:expr< [| $list:le$ |] >>;
<:expr< [| $_list:le$ |] >>;
<:expr< assert $e$ >>;
<:expr< $e1$ := $e2$ >>;
<:expr< $e$.{$list:le$} >>;
<:expr< $e$.{$_list:le$} >>;
<:expr< $chr:s$ >>;
<:expr< $_chr:s$ >>;
<:expr< ($e$ :> $t2$) >>;
<:expr< ($e$ : $t1$ :> $t2$) >>;
MLast.ExCoe loc e t1 t2;
<:expr< $flo:s$ >>;
<:expr< $_flo:s$ >>;

<:expr< for $lid:s$ = $e1$ to $e2$ do { $list:le$ } >>;
<:expr< for $lid:s$ = $e1$ to $e2$ do { $_list:le$ } >>;
<:expr< for $lid:s$ = $e1$ downto $e2$ do { $list:le$ } >>;
<:expr< for $lid:s$ = $e1$ downto $e2$ do { $_list:le$ } >>;
<:expr< for $lid:s$ = $e1$ $to:b$ $e2$ do { $list:le$ } >>;
<:expr< for $lid:s$ = $e1$ $to:b$ $e2$ do { $_list:le$ } >>;
<:expr< for $lid:s$ = $e1$ $_to:b$ $e2$ do { $list:le$ } >>;
<:expr< for $lid:s$ = $e1$ $_to:b$ $e2$ do { $_list:le$ } >>;
<:expr< for $_lid:s$ = $e1$ to $e2$ do { $list:le$ } >>;
<:expr< for $_lid:s$ = $e1$ to $e2$ do { $_list:le$ } >>;
<:expr< for $_lid:s$ = $e1$ downto $e2$ do { $list:le$ } >>;
<:expr< for $_lid:s$ = $e1$ downto $e2$ do { $_list:le$ } >>;
<:expr< for $_lid:s$ = $e1$ $to:b$ $e2$ do { $list:le$ } >>;
<:expr< for $_lid:s$ = $e1$ $to:b$ $e2$ do { $_list:le$ } >>;
<:expr< for $_lid:s$ = $e1$ $_to:b$ $e2$ do { $list:le$ } >>;
<:expr< for $_lid:s$ = $e1$ $_to:b$ $e2$ do { $_list:le$ } >>;

<:expr< fun [ $list:lpee$ ] >>;
<:expr< fun [ $_list:lpee$ ] >>;
<:expr< if $e1$ then $e2$ else $e3$ >>;
<:expr< $int:s1$ >>;
<:expr< $_int:s1$ >>;
<:expr< $int32:s1$ >>;
<:expr< $_int32:s1$ >>;
<:expr< $int64:s1$ >>;
<:expr< $_int64:s1$ >>;
<:expr< $nativeint:s1$ >>;
<:expr< $_nativeint:s1$ >>;

<:expr< ~{$p$} >>;
<:expr< ~{$p$ = $e$} >>;
<:expr< ~{$p$ $opt:e$} >>;
<:expr< ~{$p$ $_opt:e$} >>;

MLast.ExLaz loc e;

<:expr< let rec $list:lpe$ in $e$ >>;
<:expr< let rec $_list:lpe$ in $e$ >>;
<:expr< let $list:lpe$ in $e$ >>;
<:expr< let $_list:lpe$ in $e$ >>;
<:expr< let $flag:b$ $list:lpe$ in $e$ >>;
<:expr< let $flag:b$ $_list:lpe$ in $e$ >>;
<:expr< let $_flag:b$ $list:lpe$ in $e$ >>;
<:expr< let $_flag:b$ $_list:lpe$ in $e$ >>;

MLast.ExLid loc (Ploc.VaVal s);
MLast.ExLid loc s;
MLast.ExLmd loc (Ploc.VaVal s) me e;
MLast.ExLmd loc s me e;
MLast.ExMat loc e (Ploc.VaVal lpee);
MLast.ExMat loc e lpee;
MLast.ExNew loc (Ploc.VaVal ls);
MLast.ExNew loc ls;

<:expr< object $list:lcsi$ end >>;
<:expr< object $_list:lcsi$ end >>;
<:expr< object ($p$) $list:lcsi$ end >>;
<:expr< object ($p$) $_list:lcsi$ end >>;
<:expr< object $opt:p$ $list:lcsi$ end >>;
<:expr< object $opt:p$ $_list:lcsi$ end >>;
<:expr< object $_opt:p$ $list:lcsi$ end >>;
<:expr< object $_opt:p$ $_list:lcsi$ end >>;

<:expr< ?{$p$} >>;
<:expr< ?{$p$ = $e$} >>;
<:expr< ?{$p$ $opt:e$} >>;
<:expr< ?{$p$ $_opt:e$} >>;

MLast.ExOvr loc (Ploc.VaVal lse);
MLast.ExOvr loc lse;
MLast.ExPck loc me mt;

<:expr< {$list:lpe$} >>;
<:expr< {($e$) with $list:lpe$} >>;
MLast.ExRec loc (Ploc.VaVal lpe) e;
<:expr< {$_list:lpe$} >>;
<:expr< {($e$) with $_list:lpe$} >>;
MLast.ExRec loc lpe e;

MLast.ExSeq loc (Ploc.VaVal le);
MLast.ExSeq loc le;
MLast.ExSnd loc e (Ploc.VaVal s);
MLast.ExSnd loc e s;
MLast.ExSte loc e1 e2;
MLast.ExStr loc (Ploc.VaVal s);
MLast.ExStr loc s;
MLast.ExTry loc e (Ploc.VaVal lpee);
MLast.ExTry loc e lpee;
MLast.ExTup loc (Ploc.VaVal le);
MLast.ExTup loc le;
MLast.ExTyc loc e t;
MLast.ExUid loc (Ploc.VaVal s);
MLast.ExUid loc s;
MLast.ExVrn loc (Ploc.VaVal s);
MLast.ExVrn loc s;
MLast.ExWhi loc e (Ploc.VaVal le);
MLast.ExWhi loc e le;
MLast.ExXtr loc s None;
MLast.ExXtr loc s (Some (Ploc.VaVal e));
MLast.ExXtr loc s (Some e);
MLast.ExXtr loc s e;
MLast.MtAcc loc mt1 mt2;
MLast.MtApp loc mt1 mt2;
MLast.MtFun loc (Ploc.VaVal s) mt1 mt2;
MLast.MtFun loc s mt1 mt2;
MLast.MtLid loc (Ploc.VaVal s);
MLast.MtLid loc s;
MLast.MtQuo loc (Ploc.VaVal s);
MLast.MtQuo loc s;
MLast.MtSig loc (Ploc.VaVal lsi);
MLast.MtSig loc lsi;
MLast.MtTyo loc me;
MLast.MtUid loc (Ploc.VaVal s);
MLast.MtUid loc s;
MLast.MtWit loc mt (Ploc.VaVal lwc);
MLast.MtWit loc mt lwc;
MLast.MtXtr loc s None;
MLast.MtXtr loc s (Some (Ploc.VaVal mt));
MLast.MtXtr loc s (Some mt);
MLast.MtXtr loc s mt;
MLast.SgCls loc (Ploc.VaVal lcict);
MLast.SgCls loc lcict;
MLast.SgClt loc (Ploc.VaVal lcict);
MLast.SgClt loc lcict;
MLast.SgDcl loc (Ploc.VaVal lsi);
MLast.SgDcl loc lsi;

<:sig_item< # $lid:s$ >>;
<:sig_item< # $lid:s$ $e$ >>;
<:sig_item< # $lid:s$ $opt:e$ >>;
<:sig_item< # $lid:s$ $_opt:e$ >>;
<:sig_item< # $_lid:s$ >>;
<:sig_item< # $_lid:s$ $e$ >>;
<:sig_item< # $_lid:s$ $opt:e$ >>;
<:sig_item< # $_lid:s$ $_opt:e$ >>;

<:sig_item< exception $s$ of $list:lt$ >>;
<:sig_item< exception $s$ of $_list:lt$ >>;
<:sig_item< exception $_:s$ of $list:lt$ >>;
<:sig_item< exception $_:s$ of $_list:lt$ >>;

<:sig_item< external $s$ : $t$ = $list:ls$ >>;
<:sig_item< external $s$ : $t$ = $_list:ls$ >>;
<:sig_item< external $_:s$ : $t$ = $list:ls$ >>;
<:sig_item< external $_:s$ : $t$ = $_list:ls$ >>;

MLast.SgInc loc mt;

<:sig_item< module rec $list:lsmt$ >>;
<:sig_item< module rec $_list:lsmt$ >>;
<:sig_item< module $list:lsmt$ >>;
<:sig_item< module $_list:lsmt$ >>;
<:sig_item< module $flag:b$ $list:lsmt$ >>;
<:sig_item< module $flag:b$ $_list:lsmt$ >>;
<:sig_item< module $_flag:b$ $list:lsmt$ >>;
<:sig_item< module $_flag:b$ $_list:lsmt$ >>;

MLast.SgMty loc (Ploc.VaVal s) mt;
MLast.SgMty loc s mt;
MLast.SgOpn loc (Ploc.VaVal ls);
MLast.SgOpn loc ls;
MLast.SgTyp loc (Ploc.VaVal ltd);
MLast.SgTyp loc ltd;
MLast.SgUse loc s lsil;
MLast.SgVal loc (Ploc.VaVal s) t;
MLast.SgVal loc s t;
MLast.SgXtr loc s None;
MLast.SgXtr loc s (Some (Ploc.VaVal si));
MLast.SgXtr loc s (Some si);
MLast.SgXtr loc s si;

<:with_constr< type $list:ls$ $list:ltv$ = private $t$ >>;
<:with_constr< type $list:ls$ $list:ltv$ = $t$ >>;
<:with_constr< type $list:ls$ $list:ltv$ = $flag:b$ $t$ >>;
<:with_constr< type $list:ls$ $list:ltv$ = $_flag:b$ $t$ >>;
<:with_constr< type $list:ls$ $_list:ltv$ = private $t$ >>;
<:with_constr< type $list:ls$ $_list:ltv$ = $t$ >>;
<:with_constr< type $list:ls$ $_list:ltv$ = $flag:b$ $t$ >>;
<:with_constr< type $list:ls$ $_list:ltv$ = $_flag:b$ $t$ >>;
<:with_constr< type $_list:ls$ $list:ltv$ = private $t$ >>;
<:with_constr< type $_list:ls$ $list:ltv$ = $t$ >>;
<:with_constr< type $_list:ls$ $list:ltv$ = $flag:b$ $t$ >>;
<:with_constr< type $_list:ls$ $list:ltv$ = $_flag:b$ $t$ >>;
<:with_constr< type $_list:ls$ $_list:ltv$ = private $t$ >>;
<:with_constr< type $_list:ls$ $_list:ltv$ = $t$ >>;
<:with_constr< type $_list:ls$ $_list:ltv$ = $flag:b$ $t$ >>;
<:with_constr< type $_list:ls$ $_list:ltv$ = $_flag:b$ $t$ >>;

<:with_constr< module $list:ls$ = $me$ >>;
<:with_constr< module $_list:ls$ = $me$ >>;

MLast.MeAcc loc me1 me2;
MLast.MeApp loc me1 me2;
MLast.MeFun loc (Ploc.VaVal s) mt me;
MLast.MeFun loc s mt me;
MLast.MeStr loc (Ploc.VaVal lsi);
MLast.MeStr loc lsi;
MLast.MeTyc loc me mt;
MLast.MeUid loc (Ploc.VaVal s);
MLast.MeUid loc s;
MLast.MeUnp loc e mt;
MLast.MeXtr loc s None;
MLast.MeXtr loc s (Some (Ploc.VaVal me));
MLast.MeXtr loc s (Some me);
MLast.MeXtr loc s me;
MLast.StCls loc (Ploc.VaVal lcice);
MLast.StCls loc lcice;
MLast.StClt loc (Ploc.VaVal lcict);
MLast.StClt loc lcict;
MLast.StDcl loc (Ploc.VaVal lsi);
MLast.StDcl loc lsi;

<:str_item< # $lid:s$ >>;
<:str_item< # $lid:s$ $e$ >>;
<:str_item< # $lid:s$ $opt:e$ >>;
<:str_item< # $lid:s$ $_opt:e$ >>;
<:str_item< # $_lid:s$ >>;
<:str_item< # $_lid:s$ $e$ >>;
<:str_item< # $_lid:s$ $opt:e$ >>;
<:str_item< # $_lid:s$ $_opt:e$ >>;

<:str_item< exception $uid:s$ of $list:lt$ = $list:ls$ >>;
<:str_item< exception $uid:s$ of $list:lt$ = $_list:ls$ >>;
<:str_item< exception $uid:s$ of $_list:lt$ = $list:ls$ >>;
<:str_item< exception $uid:s$ of $_list:lt$ = $_list:ls$ >>;
<:str_item< exception $_uid:s$ of $list:lt$ = $list:ls$ >>;
<:str_item< exception $_uid:s$ of $list:lt$ = $_list:ls$ >>;
<:str_item< exception $_uid:s$ of $_list:lt$ = $list:ls$ >>;
<:str_item< exception $_uid:s$ of $_list:lt$ = $_list:ls$ >>;

MLast.StExp loc e;

<:str_item< external $s$ : $t$ = $list:ls$ >>;
<:str_item< external $s$ : $t$ = $_list:ls$ >>;
<:str_item< external $_:s$ : $t$ = $list:ls$ >>;
<:str_item< external $_:s$ : $t$ = $_list:ls$ >>;

MLast.StInc loc me;

<:str_item< module rec $list:lsme$ >>;
<:str_item< module rec $_list:lsme$ >>;
<:str_item< module $list:lsme$ >>;
<:str_item< module $_list:lsme$ >>;
<:str_item< module $flag:b$ $list:lsme$ >>;
<:str_item< module $flag:b$ $_list:lsme$ >>;
<:str_item< module $_flag:b$ $list:lsme$ >>;
<:str_item< module $_flag:b$ $_list:lsme$ >>;

MLast.StMty loc (Ploc.VaVal s) mt;
MLast.StMty loc s mt;
MLast.StOpn loc (Ploc.VaVal ls);
MLast.StOpn loc ls;
MLast.StTyp loc (Ploc.VaVal ltd);
MLast.StTyp loc ltd;
MLast.StUse loc s lsil;

<:str_item< value rec $list:lpe$ >>;
<:str_item< value rec $_list:lpe$ >>;
<:str_item< value $list:lpe$ >>;
<:str_item< value $_list:lpe$ >>;
<:str_item< value $flag:b$ $list:lpe$ >>;
<:str_item< value $flag:b$ $_list:lpe$ >>;
<:str_item< value $_flag:b$ $list:lpe$ >>;
<:str_item< value $_flag:b$ $_list:lpe$ >>;

MLast.StXtr loc s None;
MLast.StXtr loc s (Some (Ploc.VaVal si));
MLast.StXtr loc s (Some si);
MLast.StXtr loc s si;

<:type_decl< $tp:ls$ $list:ltv$ = private $t$ $list:ltt$ >>;
<:type_decl< $tp:ls$ $list:ltv$ = private $t$ $_list:ltt$ >>;
<:type_decl< $tp:ls$ $list:ltv$ = $t$ $list:ltt$ >>;
<:type_decl< $tp:ls$ $list:ltv$ = $t$ $_list:ltt$ >>;
<:type_decl< $tp:ls$ $list:ltv$ = $priv:b$ $t$ $list:ltt$ >>;
<:type_decl< $tp:ls$ $list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>;
<:type_decl< $tp:ls$ $list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>;
<:type_decl< $tp:ls$ $list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>;
<:type_decl< $tp:ls$ $_list:ltv$ = private $t$ $list:ltt$ >>;
<:type_decl< $tp:ls$ $_list:ltv$ = private $t$ $_list:ltt$ >>;
<:type_decl< $tp:ls$ $_list:ltv$ = $t$ $list:ltt$ >>;
<:type_decl< $tp:ls$ $_list:ltv$ = $t$ $_list:ltt$ >>;
<:type_decl< $tp:ls$ $_list:ltv$ = $priv:b$ $t$ $list:ltt$ >>;
<:type_decl< $tp:ls$ $_list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>;
<:type_decl< $tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>;
<:type_decl< $tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>;
<:type_decl< $_tp:ls$ $list:ltv$ = private $t$ $list:ltt$ >>;
<:type_decl< $_tp:ls$ $list:ltv$ = private $t$ $_list:ltt$ >>;
<:type_decl< $_tp:ls$ $list:ltv$ = $t$ $list:ltt$ >>;
<:type_decl< $_tp:ls$ $list:ltv$ = $t$ $_list:ltt$ >>;
<:type_decl< $_tp:ls$ $list:ltv$ = $priv:b$ $t$ $list:ltt$ >>;
<:type_decl< $_tp:ls$ $list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>;
<:type_decl< $_tp:ls$ $list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>;
<:type_decl< $_tp:ls$ $list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>;
<:type_decl< $_tp:ls$ $_list:ltv$ = private $t$ $list:ltt$ >>;
<:type_decl< $_tp:ls$ $_list:ltv$ = private $t$ $_list:ltt$ >>;
<:type_decl< $_tp:ls$ $_list:ltv$ = $t$ $list:ltt$ >>;
<:type_decl< $_tp:ls$ $_list:ltv$ = $t$ $_list:ltt$ >>;
<:type_decl< $_tp:ls$ $_list:ltv$ = $priv:b$ $t$ $list:ltt$ >>;
<:type_decl< $_tp:ls$ $_list:ltv$ = $priv:b$ $t$ $_list:ltt$ >>;
<:type_decl< $_tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $list:ltt$ >>;
<:type_decl< $_tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >>;

MLast.CtAcc loc ct1 ct2;
MLast.CtApp loc ct1 ct2;
MLast.CtCon loc ct (Ploc.VaVal lt);
MLast.CtCon loc ct lt;
MLast.CtFun loc t ct;
MLast.CtIde loc (Ploc.VaVal s);
MLast.CtIde loc s;

<:class_type< object $list:lcsi$ end >>;
<:class_type< object $_list:lcsi$ end >>;
<:class_type< object ($t$) $list:lcsi$ end >>;
<:class_type< object ($t$) $_list:lcsi$ end >>;
<:class_type< object $opt:t$ $list:lcsi$ end >>;
<:class_type< object $opt:t$ $_list:lcsi$ end >>;
<:class_type< object $_opt:t$ $list:lcsi$ end >>;
<:class_type< object $_opt:t$ $_list:lcsi$ end >>;

MLast.CtXtr loc s None;
MLast.CtXtr loc s (Some (Ploc.VaVal ct));
MLast.CtXtr loc s (Some ct);
MLast.CtXtr loc s ct;
MLast.CgCtr loc t1 t2;
MLast.CgDcl loc (Ploc.VaVal lcsi);
MLast.CgDcl loc lcsi;
MLast.CgInh loc ct;

<:class_sig_item< method private $lid:s$ : $t$ >>;
<:class_sig_item< method private $_lid:s$ : $t$ >>;
<:class_sig_item< method $lid:s$ : $t$ >>;
<:class_sig_item< method $_lid:s$ : $t$ >>;
<:class_sig_item< method $flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< method $flag:b$ $_lid:s$ : $t$ >>;
<:class_sig_item< method $_flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< method $_flag:b$ $_lid:s$ : $t$ >>;

<:class_sig_item< value mutable $lid:s$ : $t$ >>;
<:class_sig_item< value mutable $_lid:s$ : $t$ >>;
<:class_sig_item< value $lid:s$ : $t$ >>;
<:class_sig_item< value $_lid:s$ : $t$ >>;
<:class_sig_item< value $flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< value $flag:b$ $_lid:s$ : $t$ >>;
<:class_sig_item< value $_flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< value $_flag:b$ $_lid:s$ : $t$ >>;

<:class_sig_item< method virtual private $lid:s$ : $t$ >>;
<:class_sig_item< method virtual private $_lid:s$ : $t$ >>;
<:class_sig_item< method virtual $lid:s$ : $t$ >>;
<:class_sig_item< method virtual $_lid:s$ : $t$ >>;
<:class_sig_item< method virtual $flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< method virtual $flag:b$ $_lid:s$ : $t$ >>;
<:class_sig_item< method virtual $_flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< method virtual $_flag:b$ $_lid:s$ : $t$ >>;

<:class_expr< $ce$ $e$ >>;

<:class_expr< [ $list:lt$ ] $list:ls$ >>;
<:class_expr< [ $_list:lt$ ] $list:ls$ >>;
<:class_expr< [ $list:lt$ ] $_list:ls$ >>;
<:class_expr< [ $_list:lt$ ] $_list:ls$ >>;

<:class_expr< fun $p$ -> $ce$ >>;

<:class_expr< let rec $list:lpe$ in $ce$ >>;
<:class_expr< let rec $_list:lpe$ in $ce$ >>;
<:class_expr< let $list:lpe$ in $ce$ >>;
<:class_expr< let $_list:lpe$ in $ce$ >>;
<:class_expr< let $flag:b$ $list:lpe$ in $ce$ >>;
<:class_expr< let $flag:b$ $_list:lpe$ in $ce$ >>;
<:class_expr< let $_flag:b$ $list:lpe$ in $ce$ >>;
<:class_expr< let $_flag:b$ $_list:lpe$ in $ce$ >>;

<:class_expr< object $list:lcsi$ end >>;
<:class_expr< object $_list:lcsi$ end >>;
<:class_expr< object ($p$) $list:lcsi$ end >>;
<:class_expr< object ($p$) $_list:lcsi$ end >>;
<:class_expr< object $opt:p$ $list:lcsi$ end >>;
<:class_expr< object $opt:p$ $_list:lcsi$ end >>;
<:class_expr< object $_opt:p$ $list:lcsi$ end >>;
<:class_expr< object $_opt:p$ $_list:lcsi$ end >>;

MLast.CeTyc loc ce ct;
MLast.CeXtr loc s None;
MLast.CeXtr loc s (Some (Ploc.VaVal ce));
MLast.CeXtr loc s (Some ce);
MLast.CeXtr loc s ce;
MLast.CrCtr loc t1 t2;
MLast.CrDcl loc (Ploc.VaVal lcsi);
MLast.CrDcl loc lcsi;

<:class_str_item< inherit $ce$ >>;
<:class_str_item< inherit $ce$ $opt:Some s$ >>;
<:class_str_item< inherit $ce$ $opt:s$ >>;
<:class_str_item< inherit $ce$ $_opt:s$ >>;

MLast.CrIni loc e;

<:class_str_item< method! private $lid:s$ = $e$ >>;
<:class_str_item< method! private $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! private $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method! private $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method! private $_lid:s$ = $e$ >>;
<:class_str_item< method! private $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! private $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method! private $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method! $lid:s$ = $e$ >>;
<:class_str_item< method! $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method! $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method! $_lid:s$ = $e$ >>;
<:class_str_item< method! $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method! $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method private $lid:s$ = $e$ >>;
<:class_str_item< method private $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method private $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method private $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method private $_lid:s$ = $e$ >>;
<:class_str_item< method private $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method private $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method private $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $lid:s$ = $e$ >>;
<:class_str_item< method $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_lid:s$ = $e$ >>;
<:class_str_item< method $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $_opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $opt:t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $_opt:t$ = $e$ >>;

<:class_str_item< value! mutable $lid:s$ = $e$ >>;
<:class_str_item< value! mutable $_lid:s$ = $e$ >>;
<:class_str_item< value! $lid:s$ = $e$ >>;
<:class_str_item< value! $_lid:s$ = $e$ >>;
<:class_str_item< value! $flag:b2$ $lid:s$ = $e$ >>;
<:class_str_item< value! $flag:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< value! $_flag:b2$ $lid:s$ = $e$ >>;
<:class_str_item< value! $_flag:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< value mutable $lid:s$ = $e$ >>;
<:class_str_item< value mutable $_lid:s$ = $e$ >>;
<:class_str_item< value $lid:s$ = $e$ >>;
<:class_str_item< value $_lid:s$ = $e$ >>;
<:class_str_item< value $flag:b2$ $lid:s$ = $e$ >>;
<:class_str_item< value $flag:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< value $_flag:b2$ $lid:s$ = $e$ >>;
<:class_str_item< value $_flag:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< value $!:b1$ mutable $lid:s$ = $e$ >>;
<:class_str_item< value $!:b1$ mutable $_lid:s$ = $e$ >>;
<:class_str_item< value $!:b1$ $lid:s$ = $e$ >>;
<:class_str_item< value $!:b1$ $_lid:s$ = $e$ >>;
<:class_str_item< value $!:b1$ $flag:b2$ $lid:s$ = $e$ >>;
<:class_str_item< value $!:b1$ $flag:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< value $!:b1$ $_flag:b2$ $lid:s$ = $e$ >>;
<:class_str_item< value $!:b1$ $_flag:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< value $_!:b1$ mutable $lid:s$ = $e$ >>;
<:class_str_item< value $_!:b1$ mutable $_lid:s$ = $e$ >>;
<:class_str_item< value $_!:b1$ $lid:s$ = $e$ >>;
<:class_str_item< value $_!:b1$ $_lid:s$ = $e$ >>;
<:class_str_item< value $_!:b1$ $flag:b2$ $lid:s$ = $e$ >>;
<:class_str_item< value $_!:b1$ $flag:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< value $_!:b1$ $_flag:b2$ $lid:s$ = $e$ >>;
<:class_str_item< value $_!:b1$ $_flag:b2$ $_lid:s$ = $e$ >>;

<:class_str_item< method virtual private $lid:s$ : $t$ >>;
<:class_str_item< method virtual private $_lid:s$ : $t$ >>;
<:class_str_item< method virtual $lid:s$ : $t$ >>;
<:class_str_item< method virtual $_lid:s$ : $t$ >>;
<:class_str_item< method virtual $flag:b$ $lid:s$ : $t$ >>;
<:class_str_item< method virtual $flag:b$ $_lid:s$ : $t$ >>;
<:class_str_item< method virtual $_flag:b$ $lid:s$ : $t$ >>;
<:class_str_item< method virtual $_flag:b$ $_lid:s$ : $t$ >>;
