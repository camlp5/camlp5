(* quot_r.ml,v *)

(* ctyp: Type expressions of the language. *)

(* access *)
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
<:ctyp< $t1$ == private $t2$ >>;
<:ctyp< $t1$ == $t2$ >>;
<:ctyp< $t1$ == $priv:b$ $t2$ >>;
<:ctyp< $t1$ == $_priv:b$ $t2$ >>;

(* object *)
<:ctyp< < $list:lst$ .. > >>;
<:ctyp< < $list:lst$ > >>;
<:ctyp< < $list:lst$ $flag:b$ > >>;
<:ctyp< < $list:lst$ $_flag:b$ > >>;
<:ctyp< < $_list:lst$ .. > >>;
<:ctyp< < $_list:lst$ > >>;
<:ctyp< < $_list:lst$ $flag:b$ > >>;
<:ctyp< < $_list:lst$ $_flag:b$ > >>;

(* option label *)
<:ctyp< ?$s$: $t$ >>;
<:ctyp< ?$_:s$: $t$ >>;

(* package *)
<:ctyp< (module $mt$) >>;

(* polymorph *)
<:ctyp< ! $list:ls$ . $t$ >>;
<:ctyp< ! $_list:ls$ . $t$ >>;

(* polymorph for gadt *)
<:ctyp< type $list:ls$ . $t$ >>;
<:ctyp< type $_list:ls$ . $t$ >>;

(* variable *)
<:ctyp< '$s$ >>;
<:ctyp< '$_:s$ >>;

(* record *)
<:ctyp< { $list:llsbt$ } >>;
<:ctyp< { $_list:llsbt$ } >>;

(* sum *)
<:ctyp< [ $list:llsltt$ ] >>;
<:ctyp< [ $_list:llsltt$ ] >>;

(* t-uple *)
<:ctyp< ( $list:lt$ ) >>;
<:ctyp< ( $_list:lt$ ) >>;

(* uppercase identifier *)
<:ctyp< $uid:s$ >>;
<:ctyp< $_uid:s$ >>;

(* variant *)
<:ctyp< [ = $list:lpv$ ] >>;
<:ctyp< [ > $list:lpv$ ] >>;
<:ctyp< [ < $list:lpv$ ] >>;
<:ctyp< [ < $list:lpv$ > $list:ls$ ] >>;
<:ctyp< [ < $list:lpv$ > $_list:ls$ ] >>;
MLast.TyVrn loc (Ploc.VaVal lpv) (Some ols);
MLast.TyVrn loc (Ploc.VaVal lpv) ools;
<:ctyp< [ = $_list:lpv$ ] >>;
<:ctyp< [ > $_list:lpv$ ] >>;
<:ctyp< [ < $_list:lpv$ ] >>;
<:ctyp< [ < $_list:lpv$ > $list:ls$ ] >>;
<:ctyp< [ < $_list:lpv$ > $_list:ls$ ] >>;
MLast.TyVrn loc lpv (Some ols);
MLast.TyVrn loc lpv ools;

(* poly_variant: Polymorphic variants. *)

(* constructor *)
<:poly_variant< `$s$ >>;
<:poly_variant< `$s$ of & $list:lt$ >>;
<:poly_variant< `$s$ of & $_list:lt$ >>;
<:poly_variant< `$s$ of $list:lt$ >>;
<:poly_variant< `$s$ of $_list:lt$ >>;
<:poly_variant< `$s$ of $flag:b$ $list:lt$ >>;
<:poly_variant< `$s$ of $flag:b$ $_list:lt$ >>;
<:poly_variant< `$s$ of $_flag:b$ $list:lt$ >>;
<:poly_variant< `$s$ of $_flag:b$ $_list:lt$ >>;
<:poly_variant< `$_:s$ >>;
<:poly_variant< `$_:s$ of & $list:lt$ >>;
<:poly_variant< `$_:s$ of & $_list:lt$ >>;
<:poly_variant< `$_:s$ of $list:lt$ >>;
<:poly_variant< `$_:s$ of $_list:lt$ >>;
<:poly_variant< `$_:s$ of $flag:b$ $list:lt$ >>;
<:poly_variant< `$_:s$ of $flag:b$ $_list:lt$ >>;
<:poly_variant< `$_:s$ of $_flag:b$ $list:lt$ >>;
<:poly_variant< `$_:s$ of $_flag:b$ $_list:lt$ >>;

(* type *)
<:poly_variant< $t$ >>;

(* patt: Patterns of the language. *)

(* access *)
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

(* float *)
<:patt< $flo:s$ >>;
<:patt< $_flo:s$ >>;

(* integer constant *)
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

(* label *)
<:patt< ~{$list:lpp$} >>;
<:patt< ~{$_list:lpp$} >>;

(* lazy *)
<:patt< lazy $p$ >>;
(* lowercase identifier *)
<:patt< $lid:s$ >>;
<:patt< $_lid:s$ >>;

(* new type *)
<:patt< (type $lid:s$) >>;
<:patt< (type $_lid:s$) >>;

(* option label *)
<:patt< ?{$p$} >>;
<:patt< ?{$p$ = $e$} >>;
<:patt< ?{$p$ $opt:oe$} >>;
<:patt< ?{$p$ $_opt:oe$} >>;

(* or *)
<:patt< $p1$ | $p2$ >>;

(* record *)
<:patt< { $list:lpp$ } >>;
<:patt< { $_list:lpp$ } >>;

(* range *)
<:patt< $p1$ .. $p2$ >>;

(* string *)
<:patt< $str:s$ >>;
<:patt< $_str:s$ >>;

(* t-uple *)
<:patt< ($list:lp$) >>;
<:patt< ($_list:lp$) >>;

(* type constraint *)
<:patt< ($p$ : $t$) >>;

(* type pattern *)
<:patt< # $list:ls$ >>;
<:patt< # $_list:ls$ >>;

(* uppercase identifier *)
<:patt< $uid:s$ >>;
<:patt< $_uid:s$ >>;

(* module unpacking *)
<:patt< (module $uid:s$) >>;
<:patt< (module $uid:s$ : $mt$) >>;
MLast.PaUnp loc (Ploc.VaVal s) omt;
<:patt< (module $_uid:s$) >>;
<:patt< (module $_uid:s$ : $mt$) >>;
MLast.PaUnp loc s omt;

(* variant *)
<:patt< ` $s$ >>;
<:patt< ` $_:s$ >>;

(* expr: Expressions of the language. *)

(* access *)
<:expr< $e1$ . $e2$ >>;
(* antiquotation <a href="#expr_1">(1)</a> *)
<:expr< $anti:e$ >>;
(* application *)
<:expr< $e1$ $e2$ >>;
(* array element *)
<:expr< $e1$ .( $e2$ ) >>;

(* array *)
<:expr< [| $list:le$ |] >>;
<:expr< [| $_list:le$ |] >>;

(* assert *)
<:expr< assert $e$ >>;
(* assignment *)
<:expr< $e1$ := $e2$ >>;
(* big array element *)
<:expr< $e$ .{ $list:le$ } >>;
<:expr< $e$ .{ $_list:le$ } >>;
(* character constant *)
<:expr< $chr:s$ >>;
<:expr< $_chr:s$ >>;

(* coercion *)
<:expr< ($e$ :> $t2$) >>;
<:expr< ($e$ : $t1$ :> $t2$) >>;
MLast.ExCoe loc e ot1 t2;

(* float constant *)
<:expr< $flo:s$ >>;
<:expr< $_flo:s$ >>;

(* for (increasing) *)
<:expr< for $lid:s$ = $e1$ to $e2$ do { $list:le$ } >>;
<:expr< for $lid:s$ = $e1$ to $e2$ do { $_list:le$ } >>;
(* for (decreasing) *)
<:expr< for $lid:s$ = $e1$ downto $e2$ do { $list:le$ } >>;
<:expr< for $lid:s$ = $e1$ downto $e2$ do { $_list:le$ } >>;
(* for *)
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

(* function <a href="#expr_2">(2)</a> *)
<:expr< fun [ $list:lpee$ ] >>;
<:expr< fun [ $_list:lpee$ ] >>;

(* if *)
<:expr< if $e1$ then $e2$ else $e3$ >>;

(* integer constant *)
<:expr< $int:s1$ >>;
<:expr< $_int:s1$ >>;
(* integer 32 bits *)
<:expr< $int32:s1$ >>;
<:expr< $_int32:s1$ >>;
(* integer 64 bits *)
<:expr< $int64:s1$ >>;
<:expr< $_int64:s1$ >>;
(* native integer *)
<:expr< $nativeint:s1$ >>;
<:expr< $_nativeint:s1$ >>;

(* jocaml def *)
(* <:expr< def $list:lx$ in $e$ >>; *)
(* <:expr< def $_list:lx$ in $e$ >>; *)
MLast.ExJdf loc (Ploc.VaVal lx) e;
MLast.ExJdf loc lx e;

(* label *)
<:expr< ~{$list:lpe$} >>;
<:expr< ~{$_list:lpe$} >>;

(* lazy *)
<:expr< lazy $e$ >>;

(* let rec *)
<:expr< let rec $list:lpe$ in $e$ >>;
<:expr< let rec $_list:lpe$ in $e$ >>;
(* let not rec *)
<:expr< let $list:lpe$ in $e$ >>;
<:expr< let $_list:lpe$ in $e$ >>;
(* let *)
<:expr< let $flag:b$ $list:lpe$ in $e$ >>;
<:expr< let $flag:b$ $_list:lpe$ in $e$ >>;
<:expr< let $_flag:b$ $list:lpe$ in $e$ >>;
<:expr< let $_flag:b$ $_list:lpe$ in $e$ >>;

(* lowercase identifier *)
<:expr< $lid:s$ >>;
<:expr< $_lid:s$ >>;

(* let module *)
<:expr< let module $uid:s$ = $me$ in $e$ >>;
<:expr< let module $_uid:s$ = $me$ in $e$ >>;
(* let open *)
<:expr< let open $me$ in $e$ >>;

(* match <a href="#expr_2">(2)</a> *)
<:expr< match $e$ with [ $list:lpee$ ] >>;
<:expr< match $e$ with [ $_list:lpee$ ] >>;

(* new *)
<:expr< new $list:ls$ >>;
<:expr< new $_list:ls$ >>;

(* object expression *)
<:expr< object $list:lcsi$ end >>;
<:expr< object $_list:lcsi$ end >>;
<:expr< object ($p$) $list:lcsi$ end >>;
<:expr< object ($p$) $_list:lcsi$ end >>;
<:expr< object $opt:op$ $list:lcsi$ end >>;
<:expr< object $opt:op$ $_list:lcsi$ end >>;
<:expr< object $_opt:op$ $list:lcsi$ end >>;
<:expr< object $_opt:op$ $_list:lcsi$ end >>;

(* option label *)
<:expr< ?{$p$} >>;
<:expr< ?{$p$ = $e$} >>;
<:expr< ?{$p$ $opt:oe$} >>;
<:expr< ?{$p$ $_opt:oe$} >>;

(* override *)
<:expr< {< $list:lse$ >} >>;
<:expr< {< $_list:lse$ >} >>;

(* jocaml & *)
(* <:expr< $e1$ & $e2$ >>; *)
MLast.ExPar loc e1 e2;

(* module packing *)
<:expr< (module $me$) >>;
<:expr< (module $me$ : $mt$) >>;
MLast.ExPck loc me omt;

(* record *)
<:expr< {$list:lpe$} >>;
<:expr< {($e$) with $list:lpe$} >>;
MLast.ExRec loc (Ploc.VaVal lpe) oe;
<:expr< {$_list:lpe$} >>;
<:expr< {($e$) with $_list:lpe$} >>;
MLast.ExRec loc lpe oe;

(* jocaml reply *)
(* <:expr< reply to $jid:ls$ >>; *)
(* <:expr< reply to $_jid:ls$ >>; *)
(* <:expr< reply $e$ to $jid:ls$ >>; *)
(* <:expr< reply $e$ to $_jid:ls$ >>; *)
(* <:expr< reply $opt:oe$ to $jid:ls$ >>; *)
(* <:expr< reply $opt:oe$ to $_jid:ls$ >>; *)
(* <:expr< reply $_opt:oe$ to $jid:ls$ >>; *)
(* <:expr< reply $_opt:oe$ to $_jid:ls$ >>; *)
MLast.ExRpl loc (Ploc.VaVal None) (Ploc.VaVal ls);
MLast.ExRpl loc (Ploc.VaVal None) ls;
MLast.ExRpl loc (Ploc.VaVal (Some e)) (Ploc.VaVal ls);
MLast.ExRpl loc (Ploc.VaVal (Some e)) ls;
MLast.ExRpl loc (Ploc.VaVal oe) (Ploc.VaVal ls);
MLast.ExRpl loc (Ploc.VaVal oe) ls;
MLast.ExRpl loc oe (Ploc.VaVal ls);
MLast.ExRpl loc oe ls;

(* sequence *)
<:expr< do { $list:le$ } >>;
<:expr< do { $_list:le$ } >>;

(* jocaml spawn *)
(* <:expr< spawn $e$ >>; *)
MLast.ExSpw loc e;

(* method call *)
<:expr< $e$ # $s$ >>;
<:expr< $e$ # $_:s$ >>;

(* string element *)
<:expr< $e1$ .[ $e2$ ] >>;

(* string *)
<:expr< $str:s$ >>;
<:expr< $_str:s$ >>;

(* try <a href="#expr_2">(2)</a> *)
<:expr< try $e$ with [ $list:lpee$ ] >>;
<:expr< try $e$ with [ $_list:lpee$ ] >>;

(* t-uple *)
<:expr< ($list:le$) >>;
<:expr< ($_list:le$) >>;

(* type constraint *)
<:expr< ($e$ : $t$) >>;
(* uppercase identifier *)
<:expr< $uid:s$ >>;
<:expr< $_uid:s$ >>;

(* variant *)
<:expr< ` $s$ >>;
<:expr< ` $_:s$ >>;

(* while *)
<:expr< while $e$ do { $list:le$ } >>;
<:expr< while $e$ do { $_list:le$ } >>;

(* access *)
<:module_type< $mt1$ . $mt2$ >>;
(* application *)
<:module_type< $mt1$ $mt2$ >>;

(* functor *)
<:module_type< functor ($s$ : $mt1$) -> $mt2$ >>;
<:module_type< functor ($_:s$ : $mt1$) -> $mt2$ >>;

(* lowercase identifier *)
<:module_type< $lid:s$ >>;
<:module_type< $_lid:s$ >>;

(* abstract *)
<:module_type< ' $s$ >>;
<:module_type< ' $_:s$ >>;

(* signature *)
<:module_type< sig $list:lsi$ end >>;
<:module_type< sig $_list:lsi$ end >>;

(* of module expression *)
<:module_type< module type of $me$ >>;

(* uppercase identifier *)
<:module_type< $uid:s$ >>;
<:module_type< $_uid:s$ >>;

(* with construction *)
<:module_type< $mt$ with $list:lwc$ >>;
<:module_type< $mt$ with $_list:lwc$ >>;

(* class *)
<:sig_item< class $list:lcict$ >>;
<:sig_item< class $_list:lcict$ >>;

(* class type *)
<:sig_item< class type $list:lcict$ >>;
<:sig_item< class type $_list:lcict$ >>;

(* declare *)
<:sig_item< declare $list:lsi$ end >>;
<:sig_item< declare $_list:lsi$ end >>;

(* directive *)
<:sig_item< # $lid:s$ >>;
<:sig_item< # $lid:s$ $e$ >>;
<:sig_item< # $lid:s$ $opt:oe$ >>;
<:sig_item< # $lid:s$ $_opt:oe$ >>;
<:sig_item< # $_lid:s$ >>;
<:sig_item< # $_lid:s$ $e$ >>;
<:sig_item< # $_lid:s$ $opt:oe$ >>;
<:sig_item< # $_lid:s$ $_opt:oe$ >>;

(* exception *)
<:sig_item< exception $s$ >>;
<:sig_item< exception $s$ of $list:lt$ >>;
<:sig_item< exception $s$ of $_list:lt$ >>;
<:sig_item< exception $_:s$ >>;
<:sig_item< exception $_:s$ of $list:lt$ >>;
<:sig_item< exception $_:s$ of $_list:lt$ >>;

(* external *)
<:sig_item< external $s$ : $t$ = $list:ls$ >>;
<:sig_item< external $s$ : $t$ = $_list:ls$ >>;
<:sig_item< external $_:s$ : $t$ = $list:ls$ >>;
<:sig_item< external $_:s$ : $t$ = $_list:ls$ >>;

(* include *)
<:sig_item< include $mt$ >>;

(* module rec *)
<:sig_item< module rec $list:lsmt$ >>;
<:sig_item< module rec $_list:lsmt$ >>;
(* module non rec *)
<:sig_item< module $list:lsmt$ >>;
<:sig_item< module $_list:lsmt$ >>;
(* module *)
<:sig_item< module $flag:b$ $list:lsmt$ >>;
<:sig_item< module $flag:b$ $_list:lsmt$ >>;
<:sig_item< module $_flag:b$ $list:lsmt$ >>;
<:sig_item< module $_flag:b$ $_list:lsmt$ >>;

(* module type *)
<:sig_item< module type $s$ = $mt$ >>;
<:sig_item< module type $_:s$ = $mt$ >>;

(* open *)
<:sig_item< open $list:ls$ >>;
<:sig_item< open $_list:ls$ >>;

(* type declaration *)
<:sig_item< type $list:ltd$ >>;
<:sig_item< type $_list:ltd$ >>;

(* ... internal use ... <a href="#t_sig_item_1">(1)</a> *)
<:sig_item< # $str:s$ $list:lsil$ >>;
<:sig_item< # $str:s$ $_list:lsil$ >>;
<:sig_item< # $_str:s$ $list:lsil$ >>;
<:sig_item< # $_str:s$ $_list:lsil$ >>;

(* value *)
<:sig_item< value $s$ : $t$ >>;
<:sig_item< value $_:s$ : $t$ >>;

(* with_constr: "With" possibly following a module type. *)

(* with module *)
<:with_constr< module $list:ls$ = $me$ >>;
<:with_constr< module $_list:ls$ = $me$ >>;

(* with module substitution *)
<:with_constr< module $list:ls$ := $me$ >>;
<:with_constr< module $_list:ls$ := $me$ >>;

(* with type *)
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

(* with type substitution *)
<:with_constr< type $list:ls$ $list:ltv$ := $t$ >>;
<:with_constr< type $list:ls$ $_list:ltv$ := $t$ >>;
<:with_constr< type $_list:ls$ $list:ltv$ := $t$ >>;
<:with_constr< type $_list:ls$ $_list:ltv$ := $t$ >>;

(* access *)
<:module_expr< $me1$ . $me2$ >>;
(* application *)
<:module_expr< $me1$ $me2$ >>;

(* functor *)
<:module_expr< functor ($s$ : $mt$) -> $me$ >>;
<:module_expr< functor ($_:s$ : $mt$) -> $me$ >>;

(* struct *)
<:module_expr< struct $list:lsi$ end >>;
<:module_expr< struct $_list:lsi$ end >>;

(* module type constraint *)
<:module_expr< ($me$ : $mt$) >>;

(* uppercase identifier *)
<:module_expr< $uid:s$ >>;
<:module_expr< $_uid:s$ >>;

(* module unpacking *)
<:module_expr< (value $e$) >>;
<:module_expr< (value $e$ : $mt$) >>;
MLast.MeUnp loc e omt;

(* str_item: Structure items, i.e. phrases in a ".ml" file or "struct" *)
(* str_item:   elements. *)

(* class declaration *)
<:str_item< class $list:lcice$ >>;
<:str_item< class $_list:lcice$ >>;

(* class type declaration *)
<:str_item< class type $list:lcict$ >>;
<:str_item< class type $_list:lcict$ >>;

(* declare *)
<:str_item< declare $list:lsi$ end >>;
<:str_item< declare $_list:lsi$ end >>;

(* jocaml def *)
(* <:str_item< def $list:lx$ >>; *)
(* <:str_item< def $_list:lx$ >>; *)
MLast.StDef loc (Ploc.VaVal lx);
MLast.StDef loc lx;

(* directive *)
<:str_item< # $lid:s$ >>;
<:str_item< # $lid:s$ $e$ >>;
<:str_item< # $lid:s$ $opt:oe$ >>;
<:str_item< # $lid:s$ $_opt:oe$ >>;
<:str_item< # $_lid:s$ >>;
<:str_item< # $_lid:s$ $e$ >>;
<:str_item< # $_lid:s$ $opt:oe$ >>;
<:str_item< # $_lid:s$ $_opt:oe$ >>;

(* exception *)
<:str_item< exception $uid:s$ >>;
<:str_item< exception $uid:s$ of $list:lt$ >>;
<:str_item< exception $uid:s$ = $list:ls$ >>;
<:str_item< exception $uid:s$ of $list:lt$ = $list:ls$ >>;
<:str_item< exception $uid:s$ = $_list:ls$ >>;
<:str_item< exception $uid:s$ of $list:lt$ = $_list:ls$ >>;
<:str_item< exception $uid:s$ of $_list:lt$ >>;
<:str_item< exception $uid:s$ of $_list:lt$ = $list:ls$ >>;
<:str_item< exception $uid:s$ of $_list:lt$ = $_list:ls$ >>;
<:str_item< exception $_uid:s$ >>;
<:str_item< exception $_uid:s$ of $list:lt$ >>;
<:str_item< exception $_uid:s$ = $list:ls$ >>;
<:str_item< exception $_uid:s$ of $list:lt$ = $list:ls$ >>;
<:str_item< exception $_uid:s$ = $_list:ls$ >>;
<:str_item< exception $_uid:s$ of $list:lt$ = $_list:ls$ >>;
<:str_item< exception $_uid:s$ of $_list:lt$ >>;
<:str_item< exception $_uid:s$ of $_list:lt$ = $list:ls$ >>;
<:str_item< exception $_uid:s$ of $_list:lt$ = $_list:ls$ >>;

(* expression *)
<:str_item< $exp:e$ >>;

(* external *)
<:str_item< external $s$ : $t$ = $list:ls$ >>;
<:str_item< external $s$ : $t$ = $_list:ls$ >>;
<:str_item< external $_:s$ : $t$ = $list:ls$ >>;
<:str_item< external $_:s$ : $t$ = $_list:ls$ >>;

(* include *)
<:str_item< include $me$ >>;

(* module rec *)
<:str_item< module rec $list:lsme$ >>;
<:str_item< module rec $_list:lsme$ >>;
(* module non rec *)
<:str_item< module $list:lsme$ >>;
<:str_item< module $_list:lsme$ >>;
(* module *)
<:str_item< module $flag:b$ $list:lsme$ >>;
<:str_item< module $flag:b$ $_list:lsme$ >>;
<:str_item< module $_flag:b$ $list:lsme$ >>;
<:str_item< module $_flag:b$ $_list:lsme$ >>;

(* module type *)
<:str_item< module type $s$ = $mt$ >>;
<:str_item< module type $_:s$ = $mt$ >>;

(* open *)
<:str_item< open $list:ls$ >>;
<:str_item< open $_list:ls$ >>;

(* type declaration *)
<:str_item< type $list:ltd$ >>;
<:str_item< type $_list:ltd$ >>;

(* ... internal use ... <a href="#t_str_item_1">(1)</a> *)
<:str_item< # $str:s$ $list:lsil$ >>;
<:str_item< # $str:s$ $_list:lsil$ >>;
<:str_item< # $_str:s$ $list:lsil$ >>;
<:str_item< # $_str:s$ $_list:lsil$ >>;

(* value rec *)
<:str_item< value rec $list:lpe$ >>;
<:str_item< value rec $_list:lpe$ >>;
(* value non rec *)
<:str_item< value $list:lpe$ >>;
<:str_item< value $_list:lpe$ >>;
(* value *)
<:str_item< value $flag:b$ $list:lpe$ >>;
<:str_item< value $flag:b$ $_list:lpe$ >>;
<:str_item< value $_flag:b$ $list:lpe$ >>;
<:str_item< value $_flag:b$ $_list:lpe$ >>;

{MLast.jcLoc = loc; MLast.jcVal = Ploc.VaVal lllllspe};
{MLast.jcLoc = loc; MLast.jcVal = lllllspe};

(* type_decl: What is after 'type' or 'and' in a type declaration. *)

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

(* access *)
<:class_type< $ct1$ . $ct2$ >>;
(* application *)
<:class_type< $ct1$ $ct2$ >>;

(* constructor *)
<:class_type< $ct$ [ $list:lt$ ] >>;
<:class_type< $ct$ [ $_list:lt$ ] >>;

(* arrow *)
<:class_type< [ $t$ ] -> $ct$ >>;

(* identifier *)
<:class_type< $id:s$ >>;
<:class_type< $_id:s$ >>;

(* object *)
<:class_type< object $list:lcsi$ end >>;
<:class_type< object $_list:lcsi$ end >>;
<:class_type< object ($t$) $list:lcsi$ end >>;
<:class_type< object ($t$) $_list:lcsi$ end >>;
<:class_type< object $opt:ot$ $list:lcsi$ end >>;
<:class_type< object $opt:ot$ $_list:lcsi$ end >>;
<:class_type< object $_opt:ot$ $list:lcsi$ end >>;
<:class_type< object $_opt:ot$ $_list:lcsi$ end >>;

(* sig_item: Signature items, i.e. phrases in a ".mli" file or elements *)
(* sig_item:   inside "sig ... end". *)

(* type constraint *)
<:class_sig_item< type $t1$ = $t2$ >>;

(* declare *)
<:class_sig_item< declare $list:lcsi$ end >>;
<:class_sig_item< declare $_list:lcsi$ end >>;

(* inheritance *)
<:class_sig_item< inherit $ct$ >>;

(* method *)
<:class_sig_item< method private $lid:s$ : $t$ >>;
<:class_sig_item< method private $_lid:s$ : $t$ >>;
<:class_sig_item< method $lid:s$ : $t$ >>;
<:class_sig_item< method $_lid:s$ : $t$ >>;
<:class_sig_item< method $flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< method $flag:b$ $_lid:s$ : $t$ >>;
<:class_sig_item< method $_flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< method $_flag:b$ $_lid:s$ : $t$ >>;

(* value *)
<:class_sig_item< value mutable $lid:s$ : $t$ >>;
<:class_sig_item< value mutable $_lid:s$ : $t$ >>;
<:class_sig_item< value $lid:s$ : $t$ >>;
<:class_sig_item< value $_lid:s$ : $t$ >>;
<:class_sig_item< value $flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< value $flag:b$ $_lid:s$ : $t$ >>;
<:class_sig_item< value $_flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< value $_flag:b$ $_lid:s$ : $t$ >>;

(* virtual method *)
<:class_sig_item< method virtual private $lid:s$ : $t$ >>;
<:class_sig_item< method virtual private $_lid:s$ : $t$ >>;
<:class_sig_item< method virtual $lid:s$ : $t$ >>;
<:class_sig_item< method virtual $_lid:s$ : $t$ >>;
<:class_sig_item< method virtual $flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< method virtual $flag:b$ $_lid:s$ : $t$ >>;
<:class_sig_item< method virtual $_flag:b$ $lid:s$ : $t$ >>;
<:class_sig_item< method virtual $_flag:b$ $_lid:s$ : $t$ >>;

(* application *)
<:class_expr< $ce$ $e$ >>;

(* constructor *)
<:class_expr< [ $list:lt$ ] $list:ls$ >>;
<:class_expr< [ $_list:lt$ ] $list:ls$ >>;
<:class_expr< [ $list:lt$ ] $_list:ls$ >>;
<:class_expr< [ $_list:lt$ ] $_list:ls$ >>;

(* function *)
<:class_expr< fun $p$ -> $ce$ >>;

(* let rec *)
<:class_expr< let rec $list:lpe$ in $ce$ >>;
<:class_expr< let rec $_list:lpe$ in $ce$ >>;
(* let non rec *)
<:class_expr< let $list:lpe$ in $ce$ >>;
<:class_expr< let $_list:lpe$ in $ce$ >>;
(* let *)
<:class_expr< let $flag:b$ $list:lpe$ in $ce$ >>;
<:class_expr< let $flag:b$ $_list:lpe$ in $ce$ >>;
<:class_expr< let $_flag:b$ $list:lpe$ in $ce$ >>;
<:class_expr< let $_flag:b$ $_list:lpe$ in $ce$ >>;

(* object *)
<:class_expr< object $list:lcsi$ end >>;
<:class_expr< object $_list:lcsi$ end >>;
<:class_expr< object ($p$) $list:lcsi$ end >>;
<:class_expr< object ($p$) $_list:lcsi$ end >>;
<:class_expr< object $opt:op$ $list:lcsi$ end >>;
<:class_expr< object $opt:op$ $_list:lcsi$ end >>;
<:class_expr< object $_opt:op$ $list:lcsi$ end >>;
<:class_expr< object $_opt:op$ $_list:lcsi$ end >>;

(* class type constraint *)
<:class_expr< ($ce$ : $ct$) >>;

(* type constraint *)
<:class_str_item< type $t1$ = $t2$ >>;

(* declaration list *)
<:class_str_item< declare $list:lcsi$ end >>;
<:class_str_item< declare $_list:lcsi$ end >>;

(* inheritance *)
<:class_str_item< inherit $ce$ >>;
<:class_str_item< inherit $ce$ $opt:Some s$ >>;
<:class_str_item< inherit $ce$ $opt:os$ >>;
<:class_str_item< inherit $ce$ $_opt:os$ >>;

(* initialization *)
<:class_str_item< initializer $e$ >>;

(* method *)
<:class_str_item< method! private $lid:s$ = $e$ >>;
<:class_str_item< method! private $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! private $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method! private $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method! private $_lid:s$ = $e$ >>;
<:class_str_item< method! private $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! private $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method! private $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method! $lid:s$ = $e$ >>;
<:class_str_item< method! $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method! $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method! $_lid:s$ = $e$ >>;
<:class_str_item< method! $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method! $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method private $lid:s$ = $e$ >>;
<:class_str_item< method private $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method private $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method private $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method private $_lid:s$ = $e$ >>;
<:class_str_item< method private $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method private $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method private $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $lid:s$ = $e$ >>;
<:class_str_item< method $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_lid:s$ = $e$ >>;
<:class_str_item< method $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ >>;

(* value *)
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

(* virtual value *)
<:class_str_item< value virtual mutable $lid:s$ : $t$ >>;
<:class_str_item< value virtual mutable $_lid:s$ : $t$ >>;
<:class_str_item< value virtual $lid:s$ : $t$ >>;
<:class_str_item< value virtual $_lid:s$ : $t$ >>;
<:class_str_item< value virtual $flag:b$ $lid:s$ : $t$ >>;
<:class_str_item< value virtual $flag:b$ $_lid:s$ : $t$ >>;
<:class_str_item< value virtual $_flag:b$ $lid:s$ : $t$ >>;
<:class_str_item< value virtual $_flag:b$ $_lid:s$ : $t$ >>;

(* virtual method *)
<:class_str_item< method virtual private $lid:s$ : $t$ >>;
<:class_str_item< method virtual private $_lid:s$ : $t$ >>;
<:class_str_item< method virtual $lid:s$ : $t$ >>;
<:class_str_item< method virtual $_lid:s$ : $t$ >>;
<:class_str_item< method virtual $flag:b$ $lid:s$ : $t$ >>;
<:class_str_item< method virtual $flag:b$ $_lid:s$ : $t$ >>;
<:class_str_item< method virtual $_flag:b$ $lid:s$ : $t$ >>;
<:class_str_item< method virtual $_flag:b$ $_lid:s$ : $t$ >>;
