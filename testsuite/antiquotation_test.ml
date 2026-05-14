(* camlp5r *)
(* q_MLast_test.ml *)

open Testutil ;
open Testutil2 ;
open OUnit2 ;
open OUnitTest ;

Pcaml.inter_phrases.val := Some (";\n") ;

value pa1 = PAPR.Implem.pa1 ;
value pr = PAPR.Implem.pr ;
value fmt_string s = Printf.sprintf "<<%s>>" s ;

value stripws s = Pcre2.(replace ~{pat="[ \n\t\r]"} ~{itempl=subst ""} s) ;
value cmp_string (s1 : string) (s2 : string) =
    stripws s1 = stripws s2
;

type instance = {
    name : string
  ; code : string
  ; expect : string
}
;

value mktest i = 
i.name >:: (fun  [ _ ->
        assert_equal ~{msg="not equal"} ~{cmp=cmp_string} ~{printer=fmt_string}
          i.expect
          (pr (pa1 i.code))
                         ])
;

value shared_syntax_tests = "shared-syntax" >::: (List.map mktest
    [
      {
        name = "prototype";
        code = {foo||foo};
        expect = {foo||foo}
      }
      ;{
        name = "expr-simplest";
        code = {foo| <:expr< 1 >> ; |foo};
        expect = {foo|MLast.ExInt loc (Ploc.VaVal "1") "";
|foo}
      }
      ;{
        name = "expr-patt-any";
        code = {foo| <:patt< _ >> ; |foo} ;
        expect = {foo|MLast.PaAny loc;
|foo}
      }
      ; { name = "expr-apply-1" ;
          expect = {foo|MLast.ExApp loc e1 e2;
|foo} ;
          code = {foo|<:expr< $e1$ $e2$ >>;|foo}
        }
      ; { name = "expr-new-1" ; 
          expect = {foo|MLast.ExNew loc
  (Ploc.VaVal
     (Some (Ploc.VaVal (MLast.LiUid loc (Ploc.VaVal "A"))), Ploc.VaVal "x"));
|foo} ;
          code = {foo|<:expr< new A.x >>;|foo}
        }
      ; { name = "expr-new-2" ; 
          expect = {foo|MLast.ExNew loc (Ploc.VaVal (None, Ploc.VaVal "x"));
|foo} ;
          code = {foo|<:expr< new x >>;|foo}
        }
      ; { name = "expr-new-3" ; 
          expect = {foo|MLast.ExNew loc (Ploc.VaVal (Some (Ploc.VaVal li), Ploc.VaVal id));
|foo} ;
          code = {foo|<:expr< new $longid:li$ . $lid:id$ >>;|foo}
        }
      ; { name = "expr-new-4" ; 
          expect = {foo|MLast.ExNew loc (Ploc.VaVal (None, Ploc.VaVal id));
|foo} ;
          code = {foo|<:expr< new $lid:id$ >>;|foo}
        }
      ; { name = "expr-new-5" ; 
          expect = {foo|MLast.ExNew loc (Ploc.VaVal li);
|foo} ;
          code = {foo|<:expr< new $lilongid:li$ >>;|foo}
        }
      ; { name = "expr-open-1" ; 
          expect = {foo|MLast.ExOpen loc (MLast.LiUid loc (Ploc.VaVal "A"))
  (MLast.ExLid loc (Ploc.VaVal "e"));
|foo} ;
          code = {foo|<:expr< A.( e ) >>;|foo}
        }
      ; { name = "expr-open-2" ; 
          expect = {foo|MLast.ExOpen loc li t;
|foo} ;
          code = {foo|<:expr< $longid:li$.( $t$ ) >>;|foo}
        }
      ; { name = "ctyp-tycls-1" ; 
          expect = {foo|MLast.TyCls loc (Ploc.VaVal (None, Ploc.VaVal "a"));
|foo} ;
          code = {foo|<:ctyp< # a >> ;|foo}
        }
      ; { name = "ctyp-tycls-2" ; 
          expect = {foo|MLast.TyCls loc
  (Ploc.VaVal
     (Some (Ploc.VaVal (MLast.LiUid loc (Ploc.VaVal "A"))), Ploc.VaVal "a"));
|foo} ;
          code = {foo|<:ctyp< # A.a >> ;|foo}
        }
      ; { name = "ctyp-tycls-3" ; 
          expect = {foo|MLast.TyCls loc (Ploc.VaVal (Some (Ploc.VaVal li), Ploc.VaVal id));
|foo} ;
          code = {foo|<:ctyp< # $longid:li$ . $lid:id$ >> ;|foo}
        }
      ; { name = "ctyp-tycls-4" ; 
          expect = {foo|MLast.TyCls loc (Ploc.VaVal li);
|foo} ;
          code = {foo|<:ctyp< # $lilongid:li$ >> ;|foo}
        }
      ; { name = "ctyp-tyopen-1" ; 
          expect = {foo|MLast.TyOpen loc (MLast.LiUid loc (Ploc.VaVal "M"))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo} ;
          code = {foo|<:ctyp< M.( t ) >> ;|foo}
        }
      ; { name = "ctyp-tyopen-2" ; 
          expect = {foo|MLast.TyOpen loc li t;
|foo} ;
          code = {foo|<:ctyp< $longid:li$ . ( $t$ ) >> ;|foo}
        }
      ; { name = "class-expr-cecon-1" ; 
          expect = {foo|MLast.CeCon loc (Ploc.VaVal (None, Ploc.VaVal "a"))
  (Ploc.VaVal
     [MLast.TyLid loc (Ploc.VaVal "b"); MLast.TyLid loc (Ploc.VaVal "c")]);
|foo} ;
          code = {foo|<:class_expr< [ b, c ] a >> ;|foo}
        }
      ; { name = "class-expr-cecon-2" ; 
          expect = {foo|MLast.CeCon loc
  (Ploc.VaVal
     (Some (Ploc.VaVal (MLast.LiUid loc (Ploc.VaVal "A"))), Ploc.VaVal "a"))
  (Ploc.VaVal
     [MLast.TyLid loc (Ploc.VaVal "b"); MLast.TyLid loc (Ploc.VaVal "c")]);
|foo} ;
          code = {foo|<:class_expr< [ b, c ] A.a >> ;|foo}
        }
      ; { name = "class-expr-cecon-3" ; 
          expect = {foo|MLast.CeCon loc (Ploc.VaVal (Some (Ploc.VaVal li), Ploc.VaVal id))
  (Ploc.VaVal
     [MLast.TyLid loc (Ploc.VaVal "b"); MLast.TyLid loc (Ploc.VaVal "c")]);
|foo} ;
          code = {foo|<:class_expr< [ b, c ] $longid:li$ . $lid:id$ >> ;|foo}
        }
      ; { name = "class-expr-cecon-4" ; 
          expect = {foo|MLast.CeCon loc (Ploc.VaVal li)
  (Ploc.VaVal
     [MLast.TyLid loc (Ploc.VaVal "b"); MLast.TyLid loc (Ploc.VaVal "c")]);
|foo} ;
          code = {foo|<:class_expr< [ b, c ] $lilongid:li$ >> ;|foo}
        }

      ; { name = "class-expr-cecon-5" ; 
          expect = {foo|MLast.CeCon loc (Ploc.VaVal (None, Ploc.VaVal "a")) (Ploc.VaVal []);
|foo} ;
          code = {foo|<:class_expr< a >> ;|foo}
        }
      ; { name = "class-expr-cecon-6" ; 
          expect = {foo|MLast.CeCon loc
  (Ploc.VaVal
     (Some (Ploc.VaVal (MLast.LiUid loc (Ploc.VaVal "A"))), Ploc.VaVal "a"))
  (Ploc.VaVal []);
|foo} ;
          code = {foo|<:class_expr< A.a >> ;|foo}
        }
      ; { name = "class-expr-cecon-7" ; 
          expect = {foo|MLast.CeCon loc (Ploc.VaVal (Some (Ploc.VaVal li), Ploc.VaVal id))
  (Ploc.VaVal []);
|foo} ;
          code = {foo|<:class_expr< $longid:li$ . $lid:id$ >> ;|foo}
        }
      ; { name = "class-expr-cecon-8" ; 
          expect = {foo|MLast.CeCon loc (Ploc.VaVal li) (Ploc.VaVal []);
|foo} ;
          code = {foo|<:class_expr< $lilongid:li$ >> ;|foo}
        }
      ; { name = "attribute-1" ; 
          expect = {foo|MLast.ExExten loc
  (Ploc.VaVal (Ploc.VaVal (loc, "a"), MLast.StAttr loc (Ploc.VaVal [])));
|foo} ;
          code = {foo| <:expr< [%a] >> ; |foo}
        }
      ; { name = "attribute-2" ; 
          expect = {foo|MLast.ExExten loc
  (Ploc.VaVal
     (Ploc.VaVal (loc, "a"),
      MLast.StAttr loc
        (Ploc.VaVal
           [MLast.StExp loc (MLast.ExLid loc (Ploc.VaVal "b"))
              (Ploc.VaVal [])])));
|foo} ;
          code = {foo| <:expr< [%a b;] >> ; |foo}
        }
      ; { name = "tuple-type-antiquotation-1" ; 
          expect = {foo|MLast.TyTup loc (Ploc.VaVal l);
|foo} ;
          code = {foo|<:ctyp< ( $list:l$ ) >>; |foo}
        }
      ; { name = "tuple-type-antiquotation-2" ; 
          expect = {foo|MLast.TyTup loc l;
|foo} ;
          code = {foo|<:ctyp< ( $_list:l$ ) >>; |foo}
        }
      ; { name = "tuple-expr-antiquotation-1" ; 
          expect = {foo|MLast.ExTup loc (Ploc.VaVal l);
|foo} ;
          code = {foo|<:expr< ( $list:l$ ) >>; |foo}
        }
      ; { name = "tuple-expr-antiquotation-2" ; 
          expect = {foo|MLast.ExTup loc l;
|foo} ;
          code = {foo|<:expr< ( $_list:l$ ) >>; |foo}
        }
      ; { name = "tuple-patt-antiquotation-1" ; 
          expect = {foo|MLast.PaTup loc (Ploc.VaVal l) (Ploc.VaVal True);
|foo} ;
          code = {foo|<:patt< ( $list:l$ ) >>; |foo}
        }
      ; { name = "tuple-patt-antiquotation-2" ; 
          expect = {foo|MLast.PaTup loc l (Ploc.VaVal True);
|foo} ;
          code = {foo|<:patt< ( $_list:l$ ) >>; |foo}
        }
      ; { name = "tuple-patt-antiquotation-3" ; 
          expect = {foo|MLast.PaTup loc (Ploc.VaVal l) (Ploc.VaVal f);
|foo} ;
          code = {foo|<:patt< ( $list:l$, $closed:f$ ) >>; |foo}
        }
      ; { name = "tuple-patt-antiquotation-4" ; 
          expect = {foo|MLast.PaTup loc l f;
|foo} ;
          code = {foo|<:patt< ( $_list:l$, $_closed:f$ ) >>; |foo}
        }
      ; { name = "variants-2" ; 
          expect = {foo|MLast.PaVrn loc (Ploc.VaVal "Foo");
|foo} ;
          code = {foo|<:patt< `Foo >> ;|foo}
        }
      ; { name = "variants-3" ; 
          expect = {foo|MLast.PaVrn loc (Ploc.VaVal "foo");
|foo} ;
          code = {foo|<:patt< `foo >> ;|foo}
        }
      ; { name = "patt-empty-list" ; 
          expect = {foo|MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "[]")) (Ploc.VaVal []);
|foo} ;
          code = {foo|<:patt< [] >> ;|foo}
        }
      ; { name = "patt-list-1" ; 
          expect = {foo|MLast.PaApp loc
  (MLast.PaApp loc
     (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "::")) (Ploc.VaVal []))
     (MLast.PaLid loc (Ploc.VaVal "a")))
  (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "[]")) (Ploc.VaVal []));
|foo} ;
          code = {foo|<:patt< [a] >> ;|foo}
        }
      ; { name = "patt-list-2" ; 
          expect = {foo|MLast.PaApp loc
  (MLast.PaApp loc
     (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "::")) (Ploc.VaVal []))
     (MLast.PaLid loc (Ploc.VaVal "a")))
  (MLast.PaApp loc
     (MLast.PaApp loc
        (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "::")) (Ploc.VaVal []))
        (MLast.PaLid loc (Ploc.VaVal "b")))
     (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "[]")) (Ploc.VaVal [])));
|foo} ;
          code = {foo|<:patt< [a;b] >> ;|foo}
        }
      ; { name = "patt-type-0" ;
          expect = {foo|MLast.PaNty loc (Ploc.VaVal "a");
|foo} ;
          code = {foo|<:patt< (type a) >> ;|foo}
        }
      ; { name = "patt-type-1" ;
          expect = {foo|MLast.PaNty loc (Ploc.VaVal (PM.type_id p));
|foo} ;
          code = {foo|<:patt< (type $lid:PM.type_id p$) >> ;|foo}
        }
      ; { name = "expr-long-1" ; 
          expect = {foo|MLast.ExLong loc
  (MLast.LiAcc loc (MLast.LiUid loc (Ploc.VaVal "A")) (Ploc.VaVal "B"));
|foo} ;
          code = {foo|<:expr< A . B >>;|foo}
        }
      ; { name = "expr-acc-1d" ; 
          expect = {foo|MLast.ExFle loc (MLast.ExLong loc (MLast.LiUid loc (Ploc.VaVal e1)))
  (Ploc.VaVal (None, Ploc.VaVal m));
|foo} ;
          code = {foo|<:expr< $uid:e1$ . $lid:m$ >> ;|foo}
        }
      ; { name = "two-level-expr-1" ;
          expect = {foo|MLast.ExTup loc
  (Ploc.VaVal
     [MLast.ExLid loc (Ploc.VaVal x); MLast.ExLid loc (Ploc.VaVal y)]);
|foo} ;
          code = {foo|<:expr< ($lid:x$, $lid:y$) >> ;|foo}
        }
      ; { name = "extended-longident-1" ; 
          expect = {foo|MLast.LiAcc loc li (Ploc.VaVal m);
|foo} ;
          code = {foo|<:extended_longident< $longid:li$ . $uid:m$ >> ;|foo}
        }
      ; {
        name = "expr-extension-type-1";
        code = {foo|<:expr< [%typ: bool] >>;|foo};
        expect = {foo|MLast.ExExten loc
  (Ploc.VaVal
     (Ploc.VaVal (loc, "typ"),
      MLast.TyAttr loc (Ploc.VaVal (MLast.TyLid loc (Ploc.VaVal "bool")))));
|foo}
      }
      ; {
        name = "patt-PaLong-1";
        code = {foo|<:patt< $longid:li$ (type $_list:loc_ids$ ) >>;|foo};
        expect = {foo|MLast.PaLong loc li loc_ids;
|foo}
      }
      ; {
        name = "patt-PaLong-2";
        code = {foo|<:patt< $longid:li$ >>;|foo};
        expect = {foo|MLast.PaLong loc li (Ploc.VaVal []);
|foo}
      }
      ; {
        name = "patt-PaLong-3";
        code = {foo|<:patt< $longid:li$ (type a) >>;|foo};
        expect = {foo|MLast.PaLong loc li (Ploc.VaVal [(loc, "a")]);
|foo}
      }
      ; {
        name = "patt-PaLong-4";
        code = {foo|<:patt< $longid:li$ (type a b c) >>;|foo};
        expect = {foo|MLast.PaLong loc li (Ploc.VaVal [(loc, "a"); (loc, "b"); (loc, "c")]);
|foo}
      }
      ; {
        name = "binders-external-1";
        code = {foo|<:str_item< external $_lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >> ;|foo};
        expect = {foo|MLast.StExt loc i ls t pd attrs;
|foo}
      }
      ; {
        name = "binders-external-2";
        code = {foo|<:sig_item< external $_lid:i$ : $t$ = $_list:pd$ $_itemattrs:attrs$ >> ;|foo};
        expect = {foo|MLast.SgExt loc i (Ploc.VaVal []) t pd attrs;
|foo}
      }
    ])
 ;

value revised_syntax_tests = "revised-syntax" >::: (List.map mktest
    [
      {
        name = "prototype";
        code = {foo||foo};
        expect = {foo||foo}
      }
      ;{
        name = "patt-patt-any";
        code = {foo| match x with [ <:patt< _ >> -> 1 ]; |foo} ;
        expect = {foo|match x with [ MLast.PaAny _ -> 1 ];
|foo}
      }
      ; { name = "expr-apply-2" ;
          expect = {foo|fun
[ MLast.ExApp _ _ e2 -> 1 ];
|foo} ;
          code = {foo|fun [ <:expr< $_$ $e2$ >> -> 1 ];|foo}
        }
      ; { name = "variants-1" ; 
          expect = {foo|MLast.TyVrn loc (Ploc.VaVal l) None;
|foo} ;
          code = {foo|<:ctyp< [= $list:l$ ] >>; |foo}
        }
      ; { name = "type-extension" ;
          expect = {foo|MLast.StTypExten loc
  {MLast.teNam = Ploc.VaVal (None, Ploc.VaVal "t");
   MLast.tePrm = Ploc.VaVal []; MLast.tePrv = Ploc.VaVal False;
   MLast.teECs =
     Ploc.VaVal
       [MLast.EcTuple loc
          (loc, Ploc.VaVal "A", Ploc.VaVal [], Ploc.VaVal [], Ploc.VaVal None,
           Ploc.VaVal [])];
   MLast.teAttributes = Ploc.VaVal []};
|foo} ;
          code = {foo|<:str_item< type t += [ A ] >> ;|foo}
        }
      ; { name = "typedecl-0" ;
          expect = {foo|MLast.StTyp loc (Ploc.VaVal False)
  (Ploc.VaVal
     [{MLast.tdIsDecl = Ploc.VaVal True;
       MLast.tdNam = Ploc.VaVal (loc, Ploc.VaVal li);
       MLast.tdPrm = Ploc.VaVal []; MLast.tdPrv = Ploc.VaVal False;
       MLast.tdDef =
         MLast.TySum loc
           (Ploc.VaVal
              [(loc, Ploc.VaVal "A", Ploc.VaVal [], Ploc.VaVal [],
                Ploc.VaVal None, Ploc.VaVal [])]);
       MLast.tdCon = Ploc.VaVal []; MLast.tdAttributes = Ploc.VaVal []}]);
|foo} ;
          code = {foo|<:str_item< type $lid:li$ = [ A ] >>;|foo}
        }
      ; { name = "typedecl-1" ;
          expect = {foo|fun
[ MLast.SgTyp _ (Ploc.VaVal False)
    (Ploc.VaVal
       [{MLast.tdIsDecl = Ploc.VaVal True;
         MLast.tdNam = Ploc.VaVal (_, Ploc.VaVal x);
         MLast.tdPrm = Ploc.VaVal _; MLast.tdPrv = Ploc.VaVal _;
         MLast.tdDef = MLast.TyOpn _; MLast.tdCon = Ploc.VaVal [];
         MLast.tdAttributes = _}]) ->
    1 ];
|foo} ;
          code = {foo|fun [ <:sig_item< type $lid:x$ $list:_$ = $priv:_$ .. $_itemattrs:_$ >> -> 1 ] ;|foo}
        }
      ; { name = "typedecl-2" ;
          expect = {foo|{MLast.tdIsDecl = Ploc.VaVal True; MLast.tdNam = Ploc.VaVal x;
 MLast.tdPrm = Ploc.VaVal pl; MLast.tdPrv = Ploc.VaVal False;
 MLast.tdDef = tk; MLast.tdCon = Ploc.VaVal [];
 MLast.tdAttributes = Ploc.VaVal []};
|foo} ;
          code = {foo|<:type_decl< $tp:x$ $list:pl$ = $tk$ >>;|foo}
        }
      ; { name = "typedecl-3" ;
          expect = {foo|{MLast.tdIsDecl = Ploc.VaVal True; MLast.tdNam = Ploc.VaVal (loc, x);
 MLast.tdPrm = Ploc.VaVal pl; MLast.tdPrv = Ploc.VaVal False;
 MLast.tdDef = tk; MLast.tdCon = Ploc.VaVal [];
 MLast.tdAttributes = Ploc.VaVal []};
|foo} ;
          code = {foo|<:type_decl< $tp:(loc,x)$ $list:pl$ = $tk$ >>;|foo}
        }
      ; { name = "typedecl-3" ;
          expect = {foo|{MLast.tdIsDecl = Ploc.VaVal True; MLast.tdNam = Ploc.VaVal (loc, Ploc.VaVal "t");
 MLast.tdPrm = Ploc.VaVal [(Ploc.VaVal v, Ploc.VaVal vastr)]; MLast.tdPrv = Ploc.VaVal False;
 MLast.tdDef = tk; MLast.tdCon = Ploc.VaVal [];
 MLast.tdAttributes = Ploc.VaVal []};
|foo} ;
          code = {foo|<:type_decl< t $variance:vastr$ $var:v$ = $tk$ >>;|foo}
        }
      ; { name = "attribute-body-1" ;
          expect = {foo|fun
[ (Ploc.VaVal (_, "add"), MLast.StAttr _ (Ploc.VaVal [si])) -> si ];
|foo} ;
          code = {foo|fun [ <:attribute_body< "add" $stri:si$ ; >> -> si ] ;|foo}
        }
      ; { name = "attribute-body-2" ;
          expect = {foo|(Ploc.VaVal (loc, "add"), MLast.StAttr loc (Ploc.VaVal [si]));
|foo} ;
          code = {foo|<:attribute_body< "add" $stri:si$ ; >> ;|foo}
        }
      ; { name = "dotop-1" ;
          expect = {foo|MLast.ExAre loc (Ploc.VaVal s) e (Ploc.VaVal le);
|foo} ;
          code = {foo|<:expr< $e$ $dotop:s$ ( $list:le$ ) >> ;|foo}
        }
      ; { name = "two-level-patt-1" ;
          expect = {foo|fun
[ MLast.ExTup loc
    (Ploc.VaVal
       [MLast.ExLid _ (Ploc.VaVal x); MLast.ExLid _ (Ploc.VaVal y)]) ->
    1 ];
|foo} ;
          code = {foo|fun [ <:expr:< ($lid:x$, $lid:y$) >> -> 1 ] ;|foo}
        }
      ; { name = "generic-constructor-1" ;
          expect = {foo|fun
[ (loc, Ploc.VaVal ci, Ploc.VaVal [], Ploc.VaVal tl, Ploc.VaVal None, l) ->
    1 ];
|foo} ;
          code = {foo|fun [ <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:l$ >> -> 1 ];|foo}
        }
      ; { name = "generic-constructor-2" ;
          expect = {foo|fun
[ (loc, Ploc.VaVal ci, Ploc.VaVal [], Ploc.VaVal tl, Ploc.VaVal None,
   l) as gc ->
    1 ];
|foo} ;
          code = {foo|fun [ <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:l$ >> as gc -> 1 ];|foo}
        }
      ; { name = "generic-constructor-3" ;
          expect = {foo|match b with
[ (loc, Ploc.VaVal ci, Ploc.VaVal [], Ploc.VaVal tl, Ploc.VaVal None,
   _) as gc ->
    1 ];
|foo} ;
          code = {foo|match b with [
    <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:_$ >> as gc -> 1 ];|foo}
        }
      ; {
        name = "binders-constructor-1";
        code = {foo|<:constructor< $_uid:ci$ of $_list:ls$ . $_list:tl$ $_rto:rto$ $_algattrs:attrs$ >> ;|foo};
        expect = {foo|(loc, ci, ls, tl, rto, attrs);
|foo}
      }
    ])
 ;

value type_functor_syntax_tests = "type_functor-syntax" >::: (List.map mktest
    [
      {
        name = "prototype";
        code = {foo||foo};
        expect = {foo||foo}
      }
     ;{
        name = "type-functor-0";
        code = {foo|<:ctyp< m:(module M:MT) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-1";
        code = {foo|<:ctyp< (module M:MT) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal None) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-2";
        code = {foo|<:ctyp< $lid:l$:(module M:MT) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal l))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-3";
        code = {foo|<:ctyp< $lidopt:l$:(module M:MT) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal l) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-4";
        code = {foo|<:ctyp< m:(module $uid:m$:MT) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal m)
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-5";
        code = {foo|<:ctyp< m:(module M:$mt$) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  mt
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-6";
        code = {foo|<:ctyp< m:(module M:MT) -> $ct$ >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  ct;
|foo}
      }
    ])
 ;

value official_type_functor_syntax_tests = "official type_functor-syntax" >::: (List.map mktest
    [
      {
        name = "prototype";
        code = {foo||foo};
        expect = {foo||foo}
      }
     ;{
        name = "type-functor-0";
        code = {foo|<:ctyp< m:(module M:MT) -> t >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"))
|foo}
      }
     ;{
        name = "type-functor-1";
        code = {foo|<:ctyp< (module M:MT) -> t >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal None) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-2";
        code = {foo|<:ctyp< $lid:l$:(module M:MT) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal l))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-3";
        code = {foo|<:ctyp< $lidopt:l$:(module M:MT) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal l) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-4";
        code = {foo|<:ctyp< m:(module $uid:m$:MT) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal m)
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-5";
        code = {foo|<:ctyp< m:(module M:$mt$) -> t >>;|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  mt
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-6";
        code = {foo|<:ctyp< m:(module M:MT) -> $ct$ >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  ct;
|foo}
      }
    ])
 ;


value official_syntax_tests = "official-syntax" >::: (List.map mktest
    [
      {
        name = "prototype";
        code = {foo||foo};
        expect = {foo||foo}
      }
    ; { name = "tuple-type-antiquotation-1" ; 
        expect = {foo|MLast.TyTup loc (Ploc.VaVal l);
|foo} ;
        code = {foo|<:ctyp< ( $list:l$ ) >>; |foo}
      }
      ; { name = "tuple-type-antiquotation-2" ; 
          expect = {foo|MLast.TyTup loc l;
|foo} ;
          code = {foo|<:ctyp< ( $_list:l$ ) >>; |foo}
        }
    ])
 ;

value q_MLast_parser_tests = "q_MLast parser" >::: [
    "shared syntax" >: shared_syntax_tests
  ; "revised syntax" >: revised_syntax_tests
  ; "type_functor-syntax" >: type_functor_syntax_tests
]
;

value revised_parser_tests = "revised parser" >::: [
    "shared syntax" >: shared_syntax_tests
  ; "revised syntax" >: revised_syntax_tests
  ; "type_functor-syntax" >: type_functor_syntax_tests
]
;

value official_parser_tests = "official parser" >::: [
    "shared syntax" >: shared_syntax_tests
  ; "official syntax" >: official_syntax_tests
  ; "official type_functor-syntax" >: official_type_functor_syntax_tests
]
;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
