(* quot_r.ml,v *)

(* longid: Long identifiers for modules and module types *)

<:extended_longident< $longid:x$ . $uid:s$ >> ;
<:extended_longident< $longid:x$ . $_uid:s$ >> ;
<:extended_longident< $longid:x1$ ( $longid:x2$ ) >> ;
<:extended_longident< $uid:s$ >> ;
<:extended_longident< $_uid:s$ >> ;

(* ctyp: Type expressions of the language. *)

(* access *)
<:ctyp< $longid:x$ . $lid:s$ >>;
<:ctyp< $longid:x$ . $_lid:s$ >>;

(* alias *)
<:ctyp< $t1$ as $t2$ >>;
(* wildcard *)
<:ctyp< _ >>;
(* application *)
<:ctyp< $t1$ $t2$ >>;
(* arrow *)
<:ctyp< $t1$ -> $t2$ >>;
(* class *)
<:ctyp< # $lilongid:x$ >>;
<:ctyp< # $_lilongid:x$ >>;

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
<:ctyp< < $list:lstx$ .. > >>;
<:ctyp< < $list:lstx$ > >>;
<:ctyp< < $list:lstx$ $flag:b$ > >>;
<:ctyp< < $list:lstx$ $_flag:b$ > >>;
<:ctyp< < $_list:lstx$ .. > >>;
<:ctyp< < $_list:lstx$ > >>;
<:ctyp< < $_list:lstx$ $flag:b$ > >>;
<:ctyp< < $_list:lstx$ $_flag:b$ > >>;

(* option label *)
<:ctyp< ?$s$: $t$ >>;
<:ctyp< ?$_:s$: $t$ >>;

(* open type (e.g. type t = .. ) *)
<:ctyp< .. >> ;

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
<:ctyp< { $list:llsbtx$ } >>;
<:ctyp< { $_list:llsbtx$ } >>;

(* sum *)
<:ctyp< [ $list:lx$ ] >>;
<:ctyp< [ $_list:lx$ ] >>;

(* t-uple *)
<:ctyp< ( $list:lt$ ) >>;
<:ctyp< ( $_list:lt$ ) >>;

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

(* ctyp PPX attributes and extensions *)

<:ctyp< $t$ [@ $_attribute:x$ ] >> ;
<:ctyp< [% $_extension:x$ ] >> ;

(* poly_variant: Polymorphic variants. *)

(* constructor *)
<:poly_variant< `$s$ of & $list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$s$ of & $list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$s$ of & $_list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$s$ of & $_list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$s$ of $list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$s$ of $list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$s$ of $_list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$s$ of $_list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$s$ of $flag:b$ $list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$s$ of $flag:b$ $list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$s$ of $flag:b$ $_list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$s$ of $flag:b$ $_list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$s$ of $_flag:b$ $list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$s$ of $_flag:b$ $list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$s$ of $_flag:b$ $_list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$s$ of $_flag:b$ $_list:lt$ $_algattrs:x$ >> ;

<:poly_variant< `$_:s$ of & $list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$_:s$ of & $list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$_:s$ of & $_list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$_:s$ of & $_list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $_list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $_list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $flag:b$ $list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $flag:b$ $list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $flag:b$ $_list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $flag:b$ $_list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $_flag:b$ $list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $_flag:b$ $list:lt$ $_algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $_flag:b$ $_list:lt$ $algattrs:x$ >> ;
<:poly_variant< `$_:s$ of $_flag:b$ $_list:lt$ $_algattrs:x$ >> ;

(* type *)
<:poly_variant< $t$ >>;

(* patt: Patterns of the language. *)

(* access *)
<:patt< $longid:x$ . $p$ >>;
<:patt< $longid:x$ (type $list:lls$) >>;
<:patt< $longid:x$ (type $_list:lls$) >>;
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

(* exception *)
<:patt< exception $p$ >> ;

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
<:patt< # $lilongid:x$ >>;
<:patt< # $_lilongid:x$ >>;

(* module unpacking *)
#ifdef QMLAST
  <:patt< (module _) >>;
<:patt< (module _ : $mt$) >>;
#else
  MLast.PaUnp loc (Ploc.VaVal None) None;
MLast.PaUnp loc (Ploc.VaVal None) (Some mt);
#endif
  MLast.PaUnp loc (Ploc.VaVal None) omt;
<:patt< (module $uid:s$) >>;
<:patt< (module $uid:s$ : $mt$) >>;
MLast.PaUnp loc (Ploc.VaVal (Some (Ploc.VaVal s))) omt;
<:patt< (module $_uid:s$) >>;
<:patt< (module $_uid:s$ : $mt$) >>;
MLast.PaUnp loc (Ploc.VaVal (Some s)) omt;
<:patt< (module $uidopt:os$) >>;
<:patt< (module $uidopt:os$ : $mt$)>>;
MLast.PaUnp loc (Ploc.VaVal os) omt;
<:patt< (module $_uidopt:os$) >>;
<:patt< (module $_uidopt:os$ : $mt$)>>;
MLast.PaUnp loc os omt;

(* variant *)
<:patt< ` $s$ >>;
<:patt< ` $_:s$ >>;

(* patt PPX attributes and extensions *)

<:patt< $p$ [@ $_attribute:x$ ] >> ;
<:patt< [% $_extension:x$ ] >> ;

(* expr: Expressions of the language. *)

(* access *)
<:expr< $longid:x$ >>;
<:expr< $longid:x$ . ( $e$ ) >> ;
<:expr< $e$ . $lilongid:x$ >> ;
<:expr< $e$ . $_lilongid:x$ >> ;

(* antiquotation <a href="#expr_1">(1)</a> *)
<:expr< $anti:e$ >>;
(* application *)
<:expr< $e1$ $e2$ >>;
(* array element ops *)
<:expr< $e$ $dotop:s$ ( $list:le$ ) >> ;
<:expr< $e$ $dotop:s$ ( $_list:le$ ) >> ;
<:expr< $e$ $_dotop:s$ ( $list:le$ ) >> ;
<:expr< $e$ $_dotop:s$ ( $_list:le$ ) >> ;
(* UGH: this isn't produced by pa_mktest, sigh: <:expr< $e1$ .( $e2$ ) >>; *)

(* array *)
<:expr< [| $list:le$ |] >>;
<:expr< [| $_list:le$ |] >>;

(* assert *)
<:expr< assert $e$ >>;
(* assignment *)
<:expr< $e1$ := $e2$ >>;
(* big array element *)
<:expr< $e$ $dotop:s$ { $list:le$ } >> ;
<:expr< $e$ $dotop:s$ { $_list:le$ } >> ;
<:expr< $e$ $_dotop:s$ { $list:le$ } >> ;
<:expr< $e$ $_dotop:s$ { $_list:le$ } >> ;
(* ExBae: this isn't produced by pa_mktest: <:expr< $e$ .{ $list:le$ } >>; *)
(* ExBae: this isn't produced by pa_mktest: <:expr< $e$ .{ $_list:le$ } >>; *)
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
<:expr< for $p$ = $e1$ to $e2$ do { $list:le$ } >>;
<:expr< for $p$ = $e1$ to $e2$ do { $_list:le$ } >>;

(* for (decreasing) *)
<:expr< for $p$ = $e1$ downto $e2$ do { $list:le$ } >>;
<:expr< for $p$ = $e1$ downto $e2$ do { $_list:le$ } >>;

<:expr< for $p$ = $e1$ $to:b$ $e2$ do { $list:le$ } >>;
<:expr< for $p$ = $e1$ $to:b$ $e2$ do { $_list:le$ } >>;

<:expr< for $p$ = $e1$ $_to:b$ $e2$ do { $list:le$ } >>;
<:expr< for $p$ = $e1$ $_to:b$ $e2$ do { $_list:le$ } >>;

(* function <a href="#expr_2">(2)</a> *)
<:expr< fun [ $list:lx$ ] >>;
<:expr< fun [ $_list:lx$ ] >>;

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

(* label *)
<:expr< ~{$list:lpe$} >>;
<:expr< ~{$_list:lpe$} >>;

(* lazy *)
<:expr< lazy $e$ >>;

(* let rec *)
<:expr< let rec $list:lpex$ in $e$ >>;
<:expr< let rec $_list:lpex$ in $e$ >>;
(* let not rec *)
<:expr< let $list:lpex$ in $e$ >>;
<:expr< let $_list:lpex$ in $e$ >>;
(* let *)
<:expr< let $flag:b$ $list:lpex$ in $e$ >>;
<:expr< let $flag:b$ $_list:lpex$ in $e$ >>;
<:expr< let $_flag:b$ $list:lpex$ in $e$ >>;
<:expr< let $_flag:b$ $_list:lpex$ in $e$ >>;

(* let exception *)
<:expr< let exception $uid:s$ of $list:lt$ $algattrs:x$ in $e$ >> ;
<:expr< let exception $uid:s$ of $list:lt$ $_algattrs:x$ in $e$ >> ;
<:expr< let exception $uid:s$ of $_list:lt$ $algattrs:x$ in $e$ >> ;
<:expr< let exception $uid:s$ of $_list:lt$ $_algattrs:x$ in $e$ >> ;
<:expr< let exception $_uid:s$ of $list:lt$ $algattrs:x$ in $e$ >> ;
<:expr< let exception $_uid:s$ of $list:lt$ $_algattrs:x$ in $e$ >> ;
<:expr< let exception $_uid:s$ of $_list:lt$ $algattrs:x$ in $e$ >> ;
<:expr< let exception $_uid:s$ of $_list:lt$ $_algattrs:x$ in $e$ >> ;

(* lowercase identifier *)
<:expr< $lid:s$ >>;
<:expr< $_lid:s$ >>;

(* let module *)
#ifdef OCAML_4_10_0
  <:expr< let module _ = $me$ in $e$ >>;
#else
  MLast.ExLmd loc (Ploc.VaVal None) me e;
#endif
  <:expr< let module $uid:s$ = $me$ in $e$ >>;
<:expr< let module $_uid:s$ = $me$ in $e$ >>;
<:expr< let module $uidopt:os$ = $me$ in $e$ >>;
<:expr< let module $_uidopt:os$ = $me$ in $e$ >>;
(* let open *)
<:expr< let open! $me$ in $e$ >>;
<:expr< let open $me$ in $e$ >>;
<:expr< let open $!:b$ $me$ in $e$ >>;
<:expr< let open $_!:b$ $me$ in $e$ >>;

(* match <a href="#expr_2">(2)</a> *)
<:expr< match $e$ with [ $list:lx$ ] >>;
<:expr< match $e$ with [ $_list:lx$ ] >>;

(* new *)
<:expr< new $lilongid:x$ >>;
<:expr< new $_lilongid:x$ >>;

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

(* sequence *)
<:expr< do { $list:le$ } >>;
<:expr< do { $_list:le$ } >>;

(* method call *)
<:expr< $e$ # $s$ >>;
<:expr< $e$ # $_:s$ >>;

(* string element *)
<:expr< $e$ $dotop:s$ [ $list:le$ ] >> ;
<:expr< $e$ $dotop:s$ [ $_list:le$ ] >> ;
<:expr< $e$ $_dotop:s$ [ $list:le$ ] >> ;
<:expr< $e$ $_dotop:s$ [ $_list:le$ ] >> ;
(* ExSte: this isn't produced by pa_mktest: <:expr< $e1$ .[ $e2$ ] >>; *)


(* string *)
<:expr< $str:s$ >>;
<:expr< $_str:s$ >>;

(* try <a href="#expr_2">(2)</a> *)
<:expr< try $e$ with [ $list:lx$ ] >>;
<:expr< try $e$ with [ $_list:lx$ ] >>;

(* t-uple *)
<:expr< ($list:le$) >>;
<:expr< ($_list:le$) >>;

(* type constraint *)
<:expr< ($e$ : $t$) >>;

(* variant *)
<:expr< ` $s$ >>;
<:expr< ` $_:s$ >>;

(* while *)
<:expr< while $e$ do { $list:le$ } >>;
<:expr< while $e$ do { $_list:le$ } >>;

(* expr PPX attributes and extensions *)

<:expr< $e$ [@ $_attribute:x$ ] >> ;
<:expr< [% $_extension:x$ ] >> ;

(* unreachable *)
<:expr< . >> ;

(* access *)
<:module_type< $longid:x$ >>;
<:module_type< $longid:x$ . $lid:s$ >>;
<:module_type< $longid:x$ . $_lid:s$ >>;

(* lowercase identifier *)
<:module_type< $lid:s$ >>;
<:module_type< $_lid:s$ >>;

(* functor *)
#ifdef OCAML_4_10_0
<:module_type< functor () -> $mt$ >>;
<:module_type< functor (_ : $smtf2$) -> $mt$ >>;
#else
MLast.MtFun loc (Ploc.VaVal None) mt;
MLast.MtFun loc (Ploc.VaVal (Some (Ploc.VaVal None, smtf2))) mt;
#endif
<:module_type< functor ($uid:smtf1$ : $smtf2$) -> $mt$ >>;
<:module_type< functor ($_uid:smtf1$ : $smtf2$) -> $mt$ >>;
<:module_type< functor ($uidopt:osmtf1$ : $smtf2$) -> $mt$ >>;
<:module_type< functor ($_uidopt:osmtf1$ : $smtf2$) -> $mt$ >>;
<:module_type< functor $fp:osmt$ -> $mt$ >>;
<:module_type< functor $_fp:osmt$ -> $mt$ >>;

(* abstract *)
<:module_type< ' $s$ >>;
<:module_type< ' $_:s$ >>;

(* signature *)
<:module_type< sig $list:lsi$ end >>;
<:module_type< sig $_list:lsi$ end >>;

(* of module expression *)
<:module_type< module type of $me$ >>;

(* with construction *)
<:module_type< $mt$ with $list:lwc$ >>;
<:module_type< $mt$ with $_list:lwc$ >>;

(* module_type PPX attributes and extensions *)

<:module_type< $mt$ [@ $_attribute:x$ ] >> ;
<:module_type< [% $_extension:x$ ] >> ;

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

(* TODO CHET: GADT quotation support isn't so great yet *)
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ : $x1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ : $x1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ : $x1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ : $x1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ : $x1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ : $x1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ : $x1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ : $x1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ : $x1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ : $x1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ : $x1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ : $x1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ : $x1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ : $x1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ : $x1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ : $x1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ : $x1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $algattrs:x1f6$ $_itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $itemattrs:x2$ >>;
<:sig_item< exception $_:x1f2$ of $_list:x1f3$ . $_list:x1f4$ $_rto:ox1f5$ $_algattrs:x1f6$ $_itemattrs:x2$ >>;

(* external *)
<:sig_item< external $s$ : $list:ls1$ . $t$ = $list:ls2$ $itemattrs:x$ >> ;
<:sig_item< external $s$ : $list:ls1$ . $t$ = $list:ls2$ $_itemattrs:x$ >> ;
<:sig_item< external $s$ : $list:ls1$ . $t$ = $_list:ls2$ $itemattrs:x$ >> ;
<:sig_item< external $s$ : $list:ls1$ . $t$ = $_list:ls2$ $_itemattrs:x$ >> ;
<:sig_item< external $s$ : $_list:ls1$ . $t$ = $list:ls2$ $itemattrs:x$ >> ;
<:sig_item< external $s$ : $_list:ls1$ . $t$ = $list:ls2$ $_itemattrs:x$ >> ;
<:sig_item< external $s$ : $_list:ls1$ . $t$ = $_list:ls2$ $itemattrs:x$ >> ;
<:sig_item< external $s$ : $_list:ls1$ . $t$ = $_list:ls2$ $_itemattrs:x$ >> ;
<:sig_item< external $_:s$ : $list:ls1$ . $t$ = $list:ls2$ $itemattrs:x$ >> ;
<:sig_item< external $_:s$ : $list:ls1$ . $t$ = $list:ls2$ $_itemattrs:x$ >> ;
<:sig_item< external $_:s$ : $list:ls1$ . $t$ = $_list:ls2$ $itemattrs:x$ >> ;
<:sig_item< external $_:s$ : $list:ls1$ . $t$ = $_list:ls2$ $_itemattrs:x$ >> ;
<:sig_item< external $_:s$ : $_list:ls1$ . $t$ = $list:ls2$ $itemattrs:x$ >> ;
<:sig_item< external $_:s$ : $_list:ls1$ . $t$ = $list:ls2$ $_itemattrs:x$ >> ;
<:sig_item< external $_:s$ : $_list:ls1$ . $t$ = $_list:ls2$ $itemattrs:x$ >> ;
<:sig_item< external $_:s$ : $_list:ls1$ . $t$ = $_list:ls2$ $_itemattrs:x$ >> ;

(* include *)
<:sig_item< include $mt$ $itemattrs:x$ >>;
<:sig_item< include $mt$ $_itemattrs:x$ >>;

(* module rec *)
<:sig_item< module rec $list:lsmtx$ >>;
<:sig_item< module rec $_list:lsmtx$ >>;
(* module non rec *)
<:sig_item< module $list:lsmtx$ >>;
<:sig_item< module $_list:lsmtx$ >>;
(* module *)
<:sig_item< module $flag:b$ $list:lsmtx$ >>;
<:sig_item< module $flag:b$ $_list:lsmtx$ >>;
<:sig_item< module $_flag:b$ $list:lsmtx$ >>;
<:sig_item< module $_flag:b$ $_list:lsmtx$ >>;

(* module type *)
<:sig_item< module type $s$ = $mt$ $itemattrs:x$ >>;
<:sig_item< module type $s$ = $mt$ $_itemattrs:x$ >>;
<:sig_item< module type $_:s$ = $mt$ $itemattrs:x$ >>;
<:sig_item< module type $_:s$ = $mt$ $_itemattrs:x$ >>;

(* module type substitution *)
<:sig_item< module type $s$ := $mt$ $itemattrs:x$ >>;
<:sig_item< module type $s$ := $mt$ $_itemattrs:x$ >>;
<:sig_item< module type $_:s$ := $mt$ $itemattrs:x$ >>;
<:sig_item< module type $_:s$ := $mt$ $_itemattrs:x$ >>;

(* module alias *)

<:sig_item< module alias $uid:s$ = $longid:x1$ $itemattrs:x2$ >>;
<:sig_item< module alias $uid:s$ = $longid:x1$ $_itemattrs:x2$ >>;
<:sig_item< module alias $uid:s$ = $_longid:x1$ $itemattrs:x2$ >>;
<:sig_item< module alias $uid:s$ = $_longid:x1$ $_itemattrs:x2$ >>;
<:sig_item< module alias $_uid:s$ = $longid:x1$ $itemattrs:x2$ >>;
<:sig_item< module alias $_uid:s$ = $longid:x1$ $_itemattrs:x2$ >>;
<:sig_item< module alias $_uid:s$ = $_longid:x1$ $itemattrs:x2$ >>;
<:sig_item< module alias $_uid:s$ = $_longid:x1$ $_itemattrs:x2$ >>;

(* module substitution *)

<:sig_item< module $uid:s$ := $longid:x1$ $itemattrs:x2$ >>;
<:sig_item< module $uid:s$ := $longid:x1$ $_itemattrs:x2$ >>;
<:sig_item< module $_uid:s$ := $longid:x1$ $itemattrs:x2$ >>;
<:sig_item< module $_uid:s$ := $longid:x1$ $_itemattrs:x2$ >>;

(* open *)
<:sig_item< open $longid:x1$ $itemattrs:x2$ >>;
<:sig_item< open $longid:x1$ $_itemattrs:x2$ >>;

(* type declaration *)
<:sig_item< type nonrec $list:ltd$ >>;
<:sig_item< type nonrec $_list:ltd$ >>;
<:sig_item< type $list:ltd$ >>;
<:sig_item< type $_list:ltd$ >>;
<:sig_item< type $flag:b$ $list:ltd$ >>;
<:sig_item< type $flag:b$ $_list:ltd$ >>;
<:sig_item< type $_flag:b$ $list:ltd$ >>;
<:sig_item< type $_flag:b$ $_list:ltd$ >>;

(* extensible variant types *)

<:sig_item< type $lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:sig_item< type $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;

(* ... internal use ... <a href="#t_sig_item_1">(1)</a> *)
<:sig_item< # $str:s$ $list:lsil$ >>;
<:sig_item< # $str:s$ $_list:lsil$ >>;
<:sig_item< # $_str:s$ $list:lsil$ >>;
<:sig_item< # $_str:s$ $_list:lsil$ >>;

(* value *)
<:sig_item< value $s$ : $t$ $itemattrs:x$ >>;
<:sig_item< value $s$ : $t$ $_itemattrs:x$ >>;
<:sig_item< value $_:s$ : $t$ $itemattrs:x$ >>;
<:sig_item< value $_:s$ : $t$ $_itemattrs:x$ >>;

<:sig_item< [@@@ $_attribute:x$ ] >> ;
<:sig_item< [%% $_extension:x1$ ] $itemattrs:x2$ >> ;
<:sig_item< [%% $_extension:x1$ ] $_itemattrs:x2$ >> ;

(* with_constr: "With" possibly following a module type. *)

(* with module *)
<:with_constr< module $longid:x$ = $me$ >>;
<:with_constr< module $_longid:x$ = $me$ >>;

(* with module substitution *)
<:with_constr< module $longid:x$ := $me$ >>;
<:with_constr< module $_longid:x$ := $me$ >>;

(* with module type *)
<:with_constr< module type $longid:x$ = $mt$ >>;
<:with_constr< module type $_longid:x$ = $mt$ >>;

(* with module type substitution *)
<:with_constr< module type $longid:x$ := $mt$ >>;
<:with_constr< module type $_longid:x$ := $mt$ >>;

(* with type *)
<:with_constr< type $lilongid:x$ $list:ltv$ = private $t$ >>;
<:with_constr< type $lilongid:x$ $list:ltv$ = $t$ >>;
<:with_constr< type $lilongid:x$ $list:ltv$ = $flag:b$ $t$ >>;
<:with_constr< type $lilongid:x$ $list:ltv$ = $_flag:b$ $t$ >>;
<:with_constr< type $lilongid:x$ $_list:ltv$ = private $t$ >>;
<:with_constr< type $lilongid:x$ $_list:ltv$ = $t$ >>;
<:with_constr< type $lilongid:x$ $_list:ltv$ = $flag:b$ $t$ >>;
<:with_constr< type $lilongid:x$ $_list:ltv$ = $_flag:b$ $t$ >>;
<:with_constr< type $_lilongid:x$ $list:ltv$ = private $t$ >>;
<:with_constr< type $_lilongid:x$ $list:ltv$ = $t$ >>;
<:with_constr< type $_lilongid:x$ $list:ltv$ = $flag:b$ $t$ >>;
<:with_constr< type $_lilongid:x$ $list:ltv$ = $_flag:b$ $t$ >>;
<:with_constr< type $_lilongid:x$ $_list:ltv$ = private $t$ >>;
<:with_constr< type $_lilongid:x$ $_list:ltv$ = $t$ >>;
<:with_constr< type $_lilongid:x$ $_list:ltv$ = $flag:b$ $t$ >>;
<:with_constr< type $_lilongid:x$ $_list:ltv$ = $_flag:b$ $t$ >>;

(* with type substitution *)
<:with_constr< type $lilongid:x$ $list:ltv$ := $t$ >>;
<:with_constr< type $lilongid:x$ $_list:ltv$ := $t$ >>;
<:with_constr< type $_lilongid:x$ $list:ltv$ := $t$ >>;
<:with_constr< type $_lilongid:x$ $_list:ltv$ := $t$ >>;

(* access *)
<:module_expr< $me1$ . $me2$ >>;
(* application *)
<:module_expr< $me1$ $me2$ >>;

(* functor *)
#ifdef OCAML_4_10_0
<:module_expr< functor () -> $me$ >>;
<:module_expr< functor (_ : $smtf2$) -> $me$ >>;
#else
MLast.MeFun loc (Ploc.VaVal None) me;
MLast.MeFun loc (Ploc.VaVal (Some (Ploc.VaVal None, smtf2))) me;
#endif
<:module_expr< functor ($uid:smtf1$ : $smtf2$) -> $me$ >>;
<:module_expr< functor ($_uid:smtf1$ : $smtf2$) -> $me$ >>;
<:module_expr< functor ($uidopt:osmtf1$ : $smtf2$) -> $me$ >>;
<:module_expr< functor ($_uidopt:osmtf1$ : $smtf2$) -> $me$ >>;
<:module_expr< functor $fp:osmt$ -> $me$ >>;
<:module_expr< functor $_fp:osmt$ -> $me$ >>;

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
MLast.MeUnp loc e None (Some mt2);
MLast.MeUnp loc e None omt2;
<:module_expr< (value $e$ : $mt1$) >>;
<:module_expr< (value $e$ : $mt1$ :> $mt2$) >>;
MLast.MeUnp loc e (Some mt1) omt2;
MLast.MeUnp loc e omt1 None;
MLast.MeUnp loc e omt1 (Some mt2);
MLast.MeUnp loc e omt1 omt2;

(* module_expr PPX attributes and extensions *)

<:module_expr< $me$ [@ $_attribute:x$ ] >> ;
<:module_expr< [% $_extension:x$ ] >> ;

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
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $itemattrs:x2$ >>;
<:str_item< exception $_:xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ $_itemattrs:x2$ >>;
<:str_item< exception $uid:s$ = $longid:x1$ $algattrs:x2$ $itemattrs:x2$ >>;
<:str_item< exception $uid:s$ = $longid:x1$ $algattrs:x2$ $_itemattrs:x2$ >>;
<:str_item< exception $uid:s$ = $longid:x1$ $_algattrs:x2$ $itemattrs:x2$ >>;
<:str_item< exception $uid:s$ = $longid:x1$ $_algattrs:x2$ $_itemattrs:x2$ >>;
<:str_item< exception $uid:s$ = $_longid:x1$ $algattrs:x2$ $itemattrs:x2$ >>;
<:str_item< exception $uid:s$ = $_longid:x1$ $algattrs:x2$ $_itemattrs:x2$ >>;
<:str_item< exception $uid:s$ = $_longid:x1$ $_algattrs:x2$ $itemattrs:x2$ >>;
<:str_item< exception $uid:s$ = $_longid:x1$ $_algattrs:x2$ $_itemattrs:x2$ >>;
<:str_item< exception $_uid:s$ = $longid:x1$ $algattrs:x2$ $itemattrs:x2$ >>;
<:str_item< exception $_uid:s$ = $longid:x1$ $algattrs:x2$ $_itemattrs:x2$ >>;
<:str_item< exception $_uid:s$ = $longid:x1$ $_algattrs:x2$ $itemattrs:x2$ >>;
<:str_item< exception $_uid:s$ = $longid:x1$ $_algattrs:x2$ $_itemattrs:x2$ >>;
<:str_item< exception $_uid:s$ = $_longid:x1$ $algattrs:x2$ $itemattrs:x2$ >>;
<:str_item< exception $_uid:s$ = $_longid:x1$ $algattrs:x2$ $_itemattrs:x2$ >>;
<:str_item< exception $_uid:s$ = $_longid:x1$ $_algattrs:x2$ $itemattrs:x2$ >>;
<:str_item< exception $_uid:s$ = $_longid:x1$ $_algattrs:x2$ $_itemattrs:x2$ >>;
<:str_item< exception $_excon:x1$ $itemattrs:x2$ >>;
<:str_item< exception $_excon:x1$ $_itemattrs:x2$ >>;

(* expression *)
<:str_item< $exp:e$ $itemattrs:x$ >>;
<:str_item< $exp:e$ $_itemattrs:x$ >>;

(* external *)
<:str_item< external $s$ : $list:ls1$ . $t$ = $list:ls2$ $itemattrs:x$ >> ;
<:str_item< external $s$ : $list:ls1$ . $t$ = $list:ls2$ $_itemattrs:x$ >> ;
<:str_item< external $s$ : $list:ls1$ . $t$ = $_list:ls2$ $itemattrs:x$ >> ;
<:str_item< external $s$ : $list:ls1$ . $t$ = $_list:ls2$ $_itemattrs:x$ >> ;
<:str_item< external $s$ : $_list:ls1$ . $t$ = $list:ls2$ $itemattrs:x$ >> ;
<:str_item< external $s$ : $_list:ls1$ . $t$ = $list:ls2$ $_itemattrs:x$ >> ;
<:str_item< external $s$ : $_list:ls1$ . $t$ = $_list:ls2$ $itemattrs:x$ >> ;
<:str_item< external $s$ : $_list:ls1$ . $t$ = $_list:ls2$ $_itemattrs:x$ >> ;
<:str_item< external $_:s$ : $list:ls1$ . $t$ = $list:ls2$ $itemattrs:x$ >> ;
<:str_item< external $_:s$ : $list:ls1$ . $t$ = $list:ls2$ $_itemattrs:x$ >> ;
<:str_item< external $_:s$ : $list:ls1$ . $t$ = $_list:ls2$ $itemattrs:x$ >> ;
<:str_item< external $_:s$ : $list:ls1$ . $t$ = $_list:ls2$ $_itemattrs:x$ >> ;
<:str_item< external $_:s$ : $_list:ls1$ . $t$ = $list:ls2$ $itemattrs:x$ >> ;
<:str_item< external $_:s$ : $_list:ls1$ . $t$ = $list:ls2$ $_itemattrs:x$ >> ;
<:str_item< external $_:s$ : $_list:ls1$ . $t$ = $_list:ls2$ $itemattrs:x$ >> ;
<:str_item< external $_:s$ : $_list:ls1$ . $t$ = $_list:ls2$ $_itemattrs:x$ >> ;

(* include *)
<:str_item< include $me$ $itemattrs:x$ >>;
<:str_item< include $me$ $_itemattrs:x$ >>;

(* module rec *)
<:str_item< module rec $list:lsmex$ >>;
<:str_item< module rec $_list:lsmex$ >>;
(* module non rec *)
<:str_item< module $list:lsmex$ >>;
<:str_item< module $_list:lsmex$ >>;
(* module *)
<:str_item< module $flag:b$ $list:lsmex$ >>;
<:str_item< module $flag:b$ $_list:lsmex$ >>;
<:str_item< module $_flag:b$ $list:lsmex$ >>;
<:str_item< module $_flag:b$ $_list:lsmex$ >>;

(* module type *)
<:str_item< module type $s$ = $mt$ $itemattrs:x$ >>;
<:str_item< module type $s$ = $mt$ $_itemattrs:x$ >>;
<:str_item< module type $_:s$ = $mt$ $itemattrs:x$ >>;
<:str_item< module type $_:s$ = $mt$ $_itemattrs:x$ >>;

(* open *)
(* TODO: should be able to put variables on $me$ *)
<:str_item< open! $me$ $itemattrs:x$ >>;
<:str_item< open! $me$ $_itemattrs:x$ >>;
<:str_item< open $me$ $itemattrs:x$ >>;
<:str_item< open $me$ $_itemattrs:x$ >>;
<:str_item< open $!:b$ $me$ $itemattrs:x$ >>;
<:str_item< open $!:b$ $me$ $_itemattrs:x$ >>;
<:str_item< open $_!:b$ $me$ $itemattrs:x$ >>;
<:str_item< open $_!:b$ $me$ $_itemattrs:x$ >>;

(* type declaration *)
<:str_item< type nonrec $list:ltd$ >>;
<:str_item< type nonrec $_list:ltd$ >>;
<:str_item< type $list:ltd$ >>;
<:str_item< type $_list:ltd$ >>;
<:str_item< type $flag:b$ $list:ltd$ >>;
<:str_item< type $flag:b$ $_list:ltd$ >>;
<:str_item< type $_flag:b$ $list:ltd$ >>;
<:str_item< type $_flag:b$ $_list:ltd$ >>;

(* extensible variant types *)

<:str_item< type $lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:str_item< type $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;

(* ... internal use ... <a href="#t_str_item_1">(1)</a> *)
<:str_item< # $str:s$ $list:lsil$ >>;
<:str_item< # $str:s$ $_list:lsil$ >>;
<:str_item< # $_str:s$ $list:lsil$ >>;
<:str_item< # $_str:s$ $_list:lsil$ >>;

(* value rec *)
<:str_item< value rec $list:lpex$ >>;
<:str_item< value rec $_list:lpex$ >>;
(* value non rec *)
<:str_item< value $list:lpex$ >>;
<:str_item< value $_list:lpex$ >>;
(* value *)
<:str_item< value $flag:b$ $list:lpex$ >>;
<:str_item< value $flag:b$ $_list:lpex$ >>;
<:str_item< value $_flag:b$ $list:lpex$ >>;
<:str_item< value $_flag:b$ $_list:lpex$ >>;

(* str_item PPX attributes and extensions *)

<:str_item< [@@@ $_attribute:x$ ] >> ;
<:str_item< [%% $_extension:x1$ ] $itemattrs:x2$ >> ;
<:str_item< [%% $_extension:x1$ ] $_itemattrs:x2$ >> ;

(* type_decl: What is after 'type' or 'and' in a type declaration. *)

<:type_decl< $lid:lsf2$ $list:ltv$ = private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $lid:lsf2$ $_list:ltv$ = private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $_lid:lsf2$ $list:ltv$ = private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $_lid:lsf2$ $_list:ltv$ = private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl<$_tp:ls$ $list:ltv$ = private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl<$_tp:ls$ $_list:ltv$ = private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ = $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $lid:lsf2$ $list:ltv$ := private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $lid:lsf2$ $_list:ltv$ := private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $_lid:lsf2$ $list:ltv$ := private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $_lid:lsf2$ $_list:ltv$ := private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl<$_tp:ls$ $list:ltv$ := private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl<$_tp:ls$ $_list:ltv$ := private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ := $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl< $_lid:lsf2$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ private $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ private $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $list:ltt$ $_itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $itemattrs:x$ >>;
<:type_decl<$_tp:ls$ $_list:ltv$ $_isdecl:b1$ $_priv:b2$ $t$ $_list:ltt$ $_itemattrs:x$ >>;

(* generic constructor *)

<:constructor< $uid:s$ of $list:ls$ . $list:lt$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $list:lt$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $list:lt$ : $t$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $list:lt$ : $t$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $list:lt$ $rto:ot$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $list:lt$ $rto:ot$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $list:lt$ $_rto:ot$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $list:lt$ $_rto:ot$ $_algattrs:x$ >>;

<:constructor< $uid:s$ of $list:ls$ . $_list:lt$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $_list:lt$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $_list:lt$ : $t$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $_list:lt$ : $t$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $_list:lt$ $rto:ot$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $_list:lt$ $rto:ot$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $_list:lt$ $_rto:ot$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $list:ls$ . $_list:lt$ $_rto:ot$ $_algattrs:x$ >>;

<:constructor< $uid:s$ of $_list:ls$ . $list:lt$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $list:lt$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $list:lt$ : $t$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $list:lt$ : $t$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $list:lt$ $rto:ot$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $list:lt$ $rto:ot$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $list:lt$ $_rto:ot$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $list:lt$ $_rto:ot$ $_algattrs:x$ >>;

<:constructor< $uid:s$ of $_list:ls$ . $_list:lt$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $_list:lt$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $_list:lt$ : $t$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $_list:lt$ : $t$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $_list:lt$ $rto:ot$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $_list:lt$ $rto:ot$ $_algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $_list:lt$ $_rto:ot$ $algattrs:x$ >>;
<:constructor< $uid:s$ of $_list:ls$ . $_list:lt$ $_rto:ot$ $_algattrs:x$ >>;

<:constructor< $_uid:s$ of $list:ls$ . $list:lt$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $list:lt$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $list:lt$ : $t$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $list:lt$ : $t$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $list:lt$ $rto:ot$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $list:lt$ $rto:ot$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $list:lt$ $_rto:ot$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $list:lt$ $_rto:ot$ $_algattrs:x$ >>;

<:constructor< $_uid:s$ of $list:ls$ . $_list:lt$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $_list:lt$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $_list:lt$ : $t$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $_list:lt$ : $t$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $_list:lt$ $rto:ot$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $_list:lt$ $rto:ot$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $_list:lt$ $_rto:ot$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $list:ls$ . $_list:lt$ $_rto:ot$ $_algattrs:x$ >>;

<:constructor< $_uid:s$ of $_list:ls$ . $list:lt$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $list:lt$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $list:lt$ : $t$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $list:lt$ : $t$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $list:lt$ $rto:ot$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $list:lt$ $rto:ot$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $list:lt$ $_rto:ot$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $list:lt$ $_rto:ot$ $_algattrs:x$ >>;

<:constructor< $_uid:s$ of $_list:ls$ . $_list:lt$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $_list:lt$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $_list:lt$ : $t$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $_list:lt$ : $t$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $_list:lt$ $rto:ot$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $_list:lt$ $rto:ot$ $_algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $_list:lt$ $_rto:ot$ $algattrs:x$ >>;
<:constructor< $_uid:s$ of $_list:ls$ . $_list:lt$ $_rto:ot$ $_algattrs:x$ >>;

(* extension constructor *)

<:extension_constructor< $uid:xf2$ of $list:xf3$ . $list:xf4$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $list:xf4$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ >> ;

<:extension_constructor< $uid:xf2$ of $list:xf3$ . $_list:xf4$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $_list:xf4$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ >> ;

<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $list:xf4$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $list:xf4$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ >> ;

<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $_list:xf4$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $_list:xf4$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $uid:xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ >> ;

<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $list:xf4$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $list:xf4$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ >> ;

<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $_list:xf4$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $_list:xf4$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ >> ;

<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $list:xf4$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $list:xf4$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $list:xf4$ : $xf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $list:xf4$ $rto:oxf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ >> ;

<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $_list:xf4$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $_list:xf4$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $_list:xf4$ : $xf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $_list:xf4$ $rto:oxf5$ $_algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $algattrs:xf6$ >> ;
<:extension_constructor< $_uid:xf2$ of $_list:xf3$ . $_list:xf4$ $_rto:oxf5$ $_algattrs:xf6$ >> ;

<:extension_constructor< $uid:s$ = $longid:x1$ $algattrs:x2$ >> ;
<:extension_constructor< $uid:s$ = $longid:x1$ $_algattrs:x2$ >> ;
<:extension_constructor< $uid:s$ = $_longid:x1$ $algattrs:x2$ >> ;
<:extension_constructor< $uid:s$ = $_longid:x1$ $_algattrs:x2$ >> ;
<:extension_constructor< $_uid:s$ = $longid:x1$ $algattrs:x2$ >> ;
<:extension_constructor< $_uid:s$ = $longid:x1$ $_algattrs:x2$ >> ;
<:extension_constructor< $_uid:s$ = $_longid:x1$ $algattrs:x2$ >> ;
<:extension_constructor< $_uid:s$ = $_longid:x1$ $_algattrs:x2$ >> ;

(* type extension *)

<:type_extension< $lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;

<:type_extension< $_lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += private [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += private [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += $priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $list:lx$ ] $_itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $itemattrs:x2$ >> ;
<:type_extension< $_lilongid:x1$ $_list:ltv$ += $_priv:b$ [ $_list:lx$ ] $_itemattrs:x2$ >> ;

(* access *)
<:class_type< $longid:x$ . $lid:s$ >>;
<:class_type< $longid:x$ . $_lid:s$ >>;

(* identifier *)
<:class_type< $lid:s$ >>;
<:class_type< $_lid:s$ >>;

(* let-open *)

<:class_type< let open! $longid:x$ in $ct$ >> ;
<:class_type< let open $longid:x$ in $ct$ >> ;
<:class_type< let open $!:b$ $longid:x$ in $ct$ >> ;
<:class_type< let open $_!:b$ $longid:x$ in $ct$ >> ;

(* constructor *)
<:class_type< $ct$ [ $list:lt$ ] >>;
<:class_type< $ct$ [ $_list:lt$ ] >>;

(* arrow *)
<:class_type< [ $t$ ] -> $ct$ >>;

(* object *)
<:class_type< object $list:lcsi$ end >>;
<:class_type< object $_list:lcsi$ end >>;
<:class_type< object ($t$) $list:lcsi$ end >>;
<:class_type< object ($t$) $_list:lcsi$ end >>;
<:class_type< object $opt:ot$ $list:lcsi$ end >>;
<:class_type< object $opt:ot$ $_list:lcsi$ end >>;
<:class_type< object $_opt:ot$ $list:lcsi$ end >>;
<:class_type< object $_opt:ot$ $_list:lcsi$ end >>;

(* class_type PPX attributes and extensions *)

<:class_type< $ct$ [@ $_attribute:x$ ] >> ;
<:class_type< [% $_extension:x$ ] >> ;

(* sig_item: Signature items, i.e. phrases in a ".mli" file or elements *)
(* sig_item:   inside "sig ... end". *)

(* type constraint *)
<:class_sig_item< type $t1$ = $t2$ $itemattrs:x$ >>;
<:class_sig_item< type $t1$ = $t2$ $_itemattrs:x$ >>;

(* declare *)
<:class_sig_item< declare $list:lcsi$ end >>;
<:class_sig_item< declare $_list:lcsi$ end >>;

(* inheritance *)
<:class_sig_item< inherit $ct$ $itemattrs:x$ >>;
<:class_sig_item< inherit $ct$ $_itemattrs:x$ >>;

(* method *)
<:class_sig_item< method private $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method private $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method private $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method private $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method $flag:b$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method $flag:b$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method $flag:b$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method $flag:b$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method $_flag:b$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method $_flag:b$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method $_flag:b$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method $_flag:b$ $_lid:s$ : $t$ $_itemattrs:x$ >>;

(* value *)

<:class_sig_item< value mutable virtual $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value mutable virtual $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value mutable virtual $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value mutable virtual $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value mutable $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value mutable $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value mutable $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value mutable $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value mutable $flag:b2$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value mutable $flag:b2$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value mutable $flag:b2$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value mutable $flag:b2$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value mutable $_flag:b2$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value mutable $_flag:b2$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value mutable $_flag:b2$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value mutable $_flag:b2$ $_lid:s$ : $t$ $_itemattrs:x$ >>;

<:class_sig_item< value virtual $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value virtual $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value virtual $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value virtual $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:False$ $flag:b2$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:False$ $flag:b2$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:False$ $flag:b2$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:False$ $flag:b2$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:False$ $_flag:b2$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:False$ $_flag:b2$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:False$ $_flag:b2$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:False$ $_flag:b2$ $_lid:s$ : $t$ $_itemattrs:x$ >>;

<:class_sig_item< value $flag:b1$ virtual $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ virtual $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ virtual $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ virtual $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $flag:b2$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $flag:b2$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $flag:b2$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $flag:b2$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $_flag:b2$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $_flag:b2$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $_flag:b2$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $flag:b1$ $_flag:b2$ $_lid:s$ : $t$ $_itemattrs:x$ >>;

<:class_sig_item< value $_flag:b1$ virtual $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ virtual $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ virtual $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ virtual $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $flag:b2$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $flag:b2$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $flag:b2$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $flag:b2$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $_flag:b2$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $_flag:b2$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $_flag:b2$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< value $_flag:b1$ $_flag:b2$ $_lid:s$ : $t$ $_itemattrs:x$ >>;

(* virtual method *)
<:class_sig_item< method virtual private $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method virtual private $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method virtual private $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method virtual private $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method virtual $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method virtual $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method virtual $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method virtual $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method virtual $flag:b$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method virtual $flag:b$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method virtual $flag:b$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method virtual $flag:b$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method virtual $_flag:b$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method virtual $_flag:b$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_sig_item< method virtual $_flag:b$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_sig_item< method virtual $_flag:b$ $_lid:s$ : $t$ $_itemattrs:x$ >>;

(* class_sig_item PPX attributes and extensions *)

<:class_sig_item< [@@@ $_attribute:x$ ] >> ;
<:class_sig_item< [%% $_extension:x$ ] >> ;

(* application *)
<:class_expr< $ce$ $exp:e$ >>;

(* constructor *)
<:class_expr< [ $list:lt$ ] $lilongid:x$ >>;
<:class_expr< [ $_list:lt$ ] $lilongid:x$ >>;
<:class_expr< [ $list:lt$ ] $_lilongid:x$ >>;
<:class_expr< [ $_list:lt$ ] $_lilongid:x$ >>;

(* function *)
<:class_expr< fun $p$ -> $ce$ >>;

(* let rec *)
<:class_expr< let rec $list:lpex$ in $ce$ >>;
<:class_expr< let rec $_list:lpex$ in $ce$ >>;
(* let non rec *)
<:class_expr< let $list:lpex$ in $ce$ >>;
<:class_expr< let $_list:lpex$ in $ce$ >>;
(* let *)
<:class_expr< let $flag:b$ $list:lpex$ in $ce$ >>;
<:class_expr< let $flag:b$ $_list:lpex$ in $ce$ >>;
<:class_expr< let $_flag:b$ $list:lpex$ in $ce$ >>;
<:class_expr< let $_flag:b$ $_list:lpex$ in $ce$ >>;

(* let open *)
<:class_expr< let open! $longid:x$ in $ce$ >> ;
<:class_expr< let open $longid:x$ in $ce$ >> ;
<:class_expr< let open $!:b$ $longid:x$ in $ce$ >> ;
<:class_expr< let open $_!:b$ $longid:x$ in $ce$ >> ;

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

(* class_expr PPX attributes and extensions *)

<:class_expr< $ce$ [@ $_attribute:x$ ] >> ;
<:class_expr< [% $_extension:x$ ] >> ;

(* type constraint *)
<:class_str_item< type $t1$ = $t2$ $itemattrs:x$ >>;
<:class_str_item< type $t1$ = $t2$ $_itemattrs:x$ >>;

(* declaration list *)
<:class_str_item< declare $list:lcsi$ end >>;
<:class_str_item< declare $_list:lcsi$ end >>;

(* inheritance *)
<:class_str_item< inherit! $ce$ $itemattrs:x$ >>;
<:class_str_item< inherit! $ce$ $_itemattrs:x$ >>;
<:class_str_item< inherit! $ce$ $opt:Some s$ $itemattrs:x$ >>;
<:class_str_item< inherit! $ce$ $opt:Some s$ $_itemattrs:x$ >>;
<:class_str_item< inherit! $ce$ $opt:os$ $itemattrs:x$ >>;
<:class_str_item< inherit! $ce$ $opt:os$ $_itemattrs:x$ >>;
<:class_str_item< inherit! $ce$ $_opt:os$ $itemattrs:x$ >>;
<:class_str_item< inherit! $ce$ $_opt:os$ $_itemattrs:x$ >>;
<:class_str_item< inherit $ce$ $itemattrs:x$ >>;
<:class_str_item< inherit $ce$ $_itemattrs:x$ >>;
<:class_str_item< inherit $ce$ $opt:Some s$ $itemattrs:x$ >>;
<:class_str_item< inherit $ce$ $opt:Some s$ $_itemattrs:x$ >>;
<:class_str_item< inherit $ce$ $opt:os$ $itemattrs:x$ >>;
<:class_str_item< inherit $ce$ $opt:os$ $_itemattrs:x$ >>;
<:class_str_item< inherit $ce$ $_opt:os$ $itemattrs:x$ >>;
<:class_str_item< inherit $ce$ $_opt:os$ $_itemattrs:x$ >>;
<:class_str_item< inherit $!:b$ $ce$ $itemattrs:x$ >>;
<:class_str_item< inherit $!:b$ $ce$ $_itemattrs:x$ >>;
<:class_str_item< inherit $!:b$ $ce$ $opt:Some s$ $itemattrs:x$ >>;
<:class_str_item< inherit $!:b$ $ce$ $opt:Some s$ $_itemattrs:x$ >>;
<:class_str_item< inherit $!:b$ $ce$ $opt:os$ $itemattrs:x$ >>;
<:class_str_item< inherit $!:b$ $ce$ $opt:os$ $_itemattrs:x$ >>;
<:class_str_item< inherit $!:b$ $ce$ $_opt:os$ $itemattrs:x$ >>;
<:class_str_item< inherit $!:b$ $ce$ $_opt:os$ $_itemattrs:x$ >>;
<:class_str_item< inherit $_!:b$ $ce$ $itemattrs:x$ >>;
<:class_str_item< inherit $_!:b$ $ce$ $_itemattrs:x$ >>;
<:class_str_item< inherit $_!:b$ $ce$ $opt:Some s$ $itemattrs:x$ >>;
<:class_str_item< inherit $_!:b$ $ce$ $opt:Some s$ $_itemattrs:x$ >>;
<:class_str_item< inherit $_!:b$ $ce$ $opt:os$ $itemattrs:x$ >>;
<:class_str_item< inherit $_!:b$ $ce$ $opt:os$ $_itemattrs:x$ >>;
<:class_str_item< inherit $_!:b$ $ce$ $_opt:os$ $itemattrs:x$ >>;
<:class_str_item< inherit $_!:b$ $ce$ $_opt:os$ $_itemattrs:x$ >>;

(* initialization *)
<:class_str_item< initializer $e$ $itemattrs:x$ >>;
<:class_str_item< initializer $e$ $_itemattrs:x$ >>;

(* method *)
<:class_str_item< method! private $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! private $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! private $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! private $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! private $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! private $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! private $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! private $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! private $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! private $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! private $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! private $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! private $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! private $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! private $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! private $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method! $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method private $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method private $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method private $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method private $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method private $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method private $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method private $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method private $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method private $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method private $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method private $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method private $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method private $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method private $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method private $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method private $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ private $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ private $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ : $t$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $opt:ot$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $itemattrs:x$ >>;
<:class_str_item< method $_!:b1$ $_priv:b2$ $_lid:s$ $_opt:ot$ = $e$ $_itemattrs:x$ >>;

(* value *)
<:class_str_item< value! mutable $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value! mutable $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value! mutable $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value! mutable $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value! $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value! $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value! $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value! $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value! $flag:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value! $flag:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value! $flag:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value! $flag:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value! $_flag:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value! $_flag:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value! $_flag:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value! $_flag:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value mutable $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value mutable $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value mutable $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value mutable $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $flag:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $flag:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $flag:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $flag:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_flag:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_flag:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_flag:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_flag:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $!:b1$ mutable $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $!:b1$ mutable $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $!:b1$ mutable $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $!:b1$ mutable $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $flag:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $flag:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $flag:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $flag:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $_flag:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $_flag:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $_flag:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $!:b1$ $_flag:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ mutable $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ mutable $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ mutable $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ mutable $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $flag:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $flag:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $flag:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $flag:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $_flag:b2$ $lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $_flag:b2$ $lid:s$ = $e$ $_itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $_flag:b2$ $_lid:s$ = $e$ $itemattrs:x$ >>;
<:class_str_item< value $_!:b1$ $_flag:b2$ $_lid:s$ = $e$ $_itemattrs:x$ >>;

(* virtual value *)
<:class_str_item< value virtual mutable $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< value virtual mutable $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< value virtual mutable $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< value virtual mutable $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< value virtual $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< value virtual $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< value virtual $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< value virtual $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< value virtual $flag:b$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< value virtual $flag:b$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< value virtual $flag:b$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< value virtual $flag:b$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< value virtual $_flag:b$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< value virtual $_flag:b$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< value virtual $_flag:b$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< value virtual $_flag:b$ $_lid:s$ : $t$ $_itemattrs:x$ >>;

(* virtual method *)
<:class_str_item< method virtual private $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< method virtual private $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< method virtual private $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< method virtual private $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< method virtual $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< method virtual $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< method virtual $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< method virtual $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< method virtual $flag:b$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< method virtual $flag:b$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< method virtual $flag:b$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< method virtual $flag:b$ $_lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< method virtual $_flag:b$ $lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< method virtual $_flag:b$ $lid:s$ : $t$ $_itemattrs:x$ >>;
<:class_str_item< method virtual $_flag:b$ $_lid:s$ : $t$ $itemattrs:x$ >>;
<:class_str_item< method virtual $_flag:b$ $_lid:s$ : $t$ $_itemattrs:x$ >>;

(* class_str_item PPX attributes and extensions *)

<:class_str_item< [@@@ $_attribute:x$ ] >> ;
<:class_str_item< [%% $_extension:x$ ] >> ;

(* PPX attribute body *)

<:attribute_body< $attrid:(loc, lsf2)$ $structure:lsi$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ $_structure:lsi$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ : $signature:lsi$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ : $_signature:lsi$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ : $type:t$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ : $_type:t$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ ? $patt:p$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ ? $patt:p$ when $expr:e$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ ? $patt:p$ when $_expr:e$ >>;
(Ploc.VaVal (loc, lsf2), MLast.PaAttr loc (Ploc.VaVal p) oe);
<:attribute_body< $attrid:(loc, lsf2)$ ? $_patt:p$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ ? $_patt:p$ when $expr:e$ >>;
<:attribute_body< $attrid:(loc, lsf2)$ ? $_patt:p$ when $_expr:e$ >>;
(Ploc.VaVal (loc, lsf2), MLast.PaAttr loc p oe);
<:attribute_body< $_attrid:ls$ $structure:lsi$ >>;
<:attribute_body< $_attrid:ls$ $_structure:lsi$ >>;
<:attribute_body< $_attrid:ls$ : $signature:lsi$ >>;
<:attribute_body< $_attrid:ls$ : $_signature:lsi$ >>;
<:attribute_body< $_attrid:ls$ : $type:t$ >>;
<:attribute_body< $_attrid:ls$ : $_type:t$ >>;
<:attribute_body< $_attrid:ls$ ? $patt:p$ >>;
<:attribute_body< $_attrid:ls$ ? $patt:p$ when $expr:e$ >>;
<:attribute_body< $_attrid:ls$ ? $patt:p$ when $_expr:e$ >>;
(ls, MLast.PaAttr loc (Ploc.VaVal p) oe);
<:attribute_body< $_attrid:ls$ ? $_patt:p$ >>;
<:attribute_body< $_attrid:ls$ ? $_patt:p$ when $expr:e$ >>;
<:attribute_body< $_attrid:ls$ ? $_patt:p$ when $_expr:e$ >>;
(ls, MLast.PaAttr loc p oe);
