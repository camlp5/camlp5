(**pp -syntax camlp5r *)
(* camlp5r *)
(* q_MLast_test.ml *)

open Testutil ;
open Testutil2 ;
open OUnit2 ;
open OUnitTest ;

Pcaml.inter_phrases.val := Some (";\n") ;

value pa = PAPR.Implem.pa1 ;
value pr = PAPR.Implem.pr ;
value fmt_string s = Printf.sprintf "<<%s>>" s ;

value stripws s = Pcre2.(replace ~{pat="[ \n\t\r]"} ~{itempl=subst ""} s) ;
value cmp_string (s1 : string) (s2 : string) =
    stripws s1 = stripws s2
;

type code_t = [
    SKIP
  | CODE of string
  | ADD_SEMI
  ]
;
type instance = {
    name : string
  ; revised : code_t
  ; official : option string
  ; expect : string
}
;

value mktest ~{pa} ~{pr} ~{revised} i = 
i.name >:: (fun  [ _ ->
        let code = if revised then
            match (i.revised, i.official) with [
                (CODE s, _) -> Some s
              | (SKIP, _) -> None
              | (ADD_SEMI, Some s) -> Some (s ^";")
              | (ADD_SEMI, None) -> None
              ]
                   else i.official in
        match code with [ None -> () | Some code ->
        let msg = Printf.sprintf "%s syntax << %s >> result not equal "
                    (if revised then "revised" else "official")
                   code in
        assert_equal ~{msg=msg} ~{cmp=cmp_string} ~{printer=fmt_string}
          i.expect
          (pr (pa code))
                        ]
])
;

value shared_syntax_tests ~{pa} ~{pr} ~{revised} = "shared-syntax" >::: (List.map (mktest ~{pa} ~{pr} ~{revised})
    [
      {
        name = "prototype"
      ; revised = SKIP
      ; official = Some {foo||foo}
      ; expect = {foo||foo}
      }
      ;{
        name = "expr-simplest"
      ; revised = ADD_SEMI
      ; official = Some {foo| <:expr< 1 >> |foo}
      ; expect = {foo|MLast.ExInt loc (Ploc.VaVal "1") "";
|foo}
      }
      ;{
        name = "expr-patt-any";
        revised = ADD_SEMI;
        official = Some {foo| <:patt< _ >> |foo} ;
        expect = {foo|MLast.PaAny loc;
|foo}
      }
      ; { name = "expr-apply-1" ;
          revised = ADD_SEMI;
          official = Some {foo|<:expr< $e1$ $e2$ >>|foo} ;
          expect = {foo|MLast.ExApp loc e1 e2;
|foo}
        }
      ; { name = "expr-new-1" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:expr< new A.x >>|foo} ;
          expect = {foo|MLast.ExNew loc
  (Ploc.VaVal
     (Some (Ploc.VaVal (MLast.LiUid loc (Ploc.VaVal "A"))), Ploc.VaVal "x"));
|foo}
        }
      ; { name = "expr-new-2" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:expr< new x >>|foo} ;
          expect = {foo|MLast.ExNew loc (Ploc.VaVal (None, Ploc.VaVal "x"));
|foo} 
        }
      ; { name = "expr-new-3" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:expr< new $longid:li$ . $lid:id$ >>|foo} ;
          expect = {foo|MLast.ExNew loc (Ploc.VaVal (Some (Ploc.VaVal li), Ploc.VaVal id));
|foo}
        }
      ; { name = "expr-new-4" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:expr< new $lid:id$ >>|foo} ;
          expect = {foo|MLast.ExNew loc (Ploc.VaVal (None, Ploc.VaVal id));
|foo}
        }
      ; { name = "expr-new-5" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:expr< new $lilongid:li$ >>|foo};
          expect = {foo|MLast.ExNew loc (Ploc.VaVal li);
|foo}
        }
      ; { name = "expr-open-1" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:expr< A.( e ) >>|foo} ;
          expect = {foo|MLast.ExOpen loc (MLast.LiUid loc (Ploc.VaVal "A"))
  (MLast.ExLid loc (Ploc.VaVal "e"));
|foo}
        }
      ; { name = "expr-open-2" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:expr< $longid:li$.( $t$ ) >>|foo} ;
          expect = {foo|MLast.ExOpen loc li t;
|foo}
        }
      ; { name = "ctyp-tycls-1" ;
          revised = ADD_SEMI ;
          official = Some {foo|<:ctyp< # a >> |foo} ;
          expect = {foo|MLast.TyCls loc (Ploc.VaVal (None, Ploc.VaVal "a"));
|foo}
        }
      ; { name = "ctyp-tycls-2" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:ctyp< # A.a >>|foo} ;
          expect = {foo|MLast.TyCls loc
  (Ploc.VaVal
     (Some (Ploc.VaVal (MLast.LiUid loc (Ploc.VaVal "A"))), Ploc.VaVal "a"));
|foo}
        }
      ; { name = "ctyp-tycls-3" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:ctyp< # $longid:li$ . $lid:id$ >>|foo} ;
          expect = {foo|MLast.TyCls loc (Ploc.VaVal (Some (Ploc.VaVal li), Ploc.VaVal id));
|foo}
        }
      ; { name = "ctyp-tycls-4" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:ctyp< # $lilongid:li$ >>|foo} ;
          expect = {foo|MLast.TyCls loc (Ploc.VaVal li);
|foo}
        }
      ; { name = "ctyp-tyopen-1" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:ctyp< M.( t ) >>|foo} ;
          expect = {foo|MLast.TyOpen loc (MLast.LiUid loc (Ploc.VaVal "M"))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
        }
      ; { name = "ctyp-tyopen-2" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:ctyp< $longid:li$ . ( $t$ ) >> |foo} ;
          expect = {foo|MLast.TyOpen loc li t;
|foo}
        }
      ; { name = "class-expr-cecon-1" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:class_expr< [ b, c ] a >>|foo} ;
          expect = {foo|MLast.CeCon loc (Ploc.VaVal (None, Ploc.VaVal "a"))
  (Ploc.VaVal
     [MLast.TyLid loc (Ploc.VaVal "b"); MLast.TyLid loc (Ploc.VaVal "c")]);
|foo}
        }
      ; { name = "class-expr-cecon-2" ; 
          revised = ADD_SEMI ;
          official = Some {foo|<:class_expr< [ b, c ] A.a >>|foo} ;
          expect = {foo|MLast.CeCon loc
  (Ploc.VaVal
     (Some (Ploc.VaVal (MLast.LiUid loc (Ploc.VaVal "A"))), Ploc.VaVal "a"))
  (Ploc.VaVal
     [MLast.TyLid loc (Ploc.VaVal "b"); MLast.TyLid loc (Ploc.VaVal "c")]);
|foo}
        }
      ; { name = "class-expr-cecon-3" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:class_expr< [ b, c ] $longid:li$ . $lid:id$ >>|foo};
          expect = {foo|MLast.CeCon loc (Ploc.VaVal (Some (Ploc.VaVal li), Ploc.VaVal id))
  (Ploc.VaVal
     [MLast.TyLid loc (Ploc.VaVal "b"); MLast.TyLid loc (Ploc.VaVal "c")]);
|foo}
        }
      ; { name = "class-expr-cecon-4" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:class_expr< [ b, c ] $lilongid:li$ >> |foo};
          expect = {foo|MLast.CeCon loc (Ploc.VaVal li)
  (Ploc.VaVal
     [MLast.TyLid loc (Ploc.VaVal "b"); MLast.TyLid loc (Ploc.VaVal "c")]);
|foo}
        }

      ; { name = "class-expr-cecon-5" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:class_expr< a >>|foo};
          expect = {foo|MLast.CeCon loc (Ploc.VaVal (None, Ploc.VaVal "a")) (Ploc.VaVal []);
|foo}
        }
      ; { name = "class-expr-cecon-6" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:class_expr< A.a >>|foo};
          expect = {foo|MLast.CeCon loc
  (Ploc.VaVal
     (Some (Ploc.VaVal (MLast.LiUid loc (Ploc.VaVal "A"))), Ploc.VaVal "a"))
  (Ploc.VaVal []);
|foo}
        }
      ; { name = "class-expr-cecon-7" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:class_expr< $longid:li$ . $lid:id$ >>|foo};
          expect = {foo|MLast.CeCon loc (Ploc.VaVal (Some (Ploc.VaVal li), Ploc.VaVal id))
  (Ploc.VaVal []);
|foo}
        }
      ; { name = "class-expr-cecon-8" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:class_expr< $lilongid:li$ >>|foo};
          expect = {foo|MLast.CeCon loc (Ploc.VaVal li) (Ploc.VaVal []);
|foo}
        }
      ; { name = "attribute-1" ; 
          revised = ADD_SEMI;
          official = Some {foo| <:expr< [%a] >>|foo};
          expect = {foo|MLast.ExExten loc
  (Ploc.VaVal (Ploc.VaVal (loc, "a"), MLast.StAttr loc (Ploc.VaVal [])));
|foo}
        }
      ; { name = "attribute-2" ; 
          revised = ADD_SEMI;
          official = Some {foo| <:expr< [%a b;] >>|foo};
          expect = {foo|MLast.ExExten loc
  (Ploc.VaVal
     (Ploc.VaVal (loc, "a"),
      MLast.StAttr loc
        (Ploc.VaVal
           [MLast.StExp loc (MLast.ExLid loc (Ploc.VaVal "b"))
              (Ploc.VaVal [])])));
|foo}
        }
      ; { name = "tuple-type-antiquotation-1" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:ctyp< ( $list:l$ ) >>|foo};
          expect = {foo|MLast.TyTup loc (Ploc.VaVal l);
|foo}
        }
      ; { name = "tuple-type-antiquotation-2" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:ctyp< ( $_list:l$ ) >>|foo};
          expect = {foo|MLast.TyTup loc l;
|foo}
        }
      ; { name = "tuple-expr-antiquotation-1" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:expr< ( $list:l$ ) >>|foo};
          expect = {foo|MLast.ExTup loc (Ploc.VaVal l);
|foo}
        }
      ; { name = "tuple-expr-antiquotation-2" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:expr< ( $_list:l$ ) >>|foo};
          expect = {foo|MLast.ExTup loc l;
|foo}
        }
      ; { name = "tuple-patt-antiquotation-1" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< ( $list:l$ ) >>|foo};
          expect = {foo|MLast.PaTup loc (Ploc.VaVal l) (Ploc.VaVal True);
|foo}
        }
      ; { name = "tuple-patt-antiquotation-2" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< ( $_list:l$ ) >>|foo};
          expect = {foo|MLast.PaTup loc l (Ploc.VaVal True);
|foo}
        }
      ; { name = "tuple-patt-antiquotation-3" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< ( $list:l$, $closed:f$ ) >>|foo};
          expect = {foo|MLast.PaTup loc (Ploc.VaVal l) (Ploc.VaVal f);
|foo}
        }
      ; { name = "tuple-patt-antiquotation-4" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< ( $_list:l$, $_closed:f$ ) >>|foo};
          expect = {foo|MLast.PaTup loc l f;
|foo}
        }
      ; { name = "variants-2" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< `Foo >>|foo};
          expect = {foo|MLast.PaVrn loc (Ploc.VaVal "Foo");
|foo}
        }
      ; { name = "variants-3" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< `foo >>|foo};
          expect = {foo|MLast.PaVrn loc (Ploc.VaVal "foo");
|foo}
        }
      ; { name = "patt-empty-list" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< [] >>|foo};
          expect = {foo|MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "[]")) (Ploc.VaVal []);
|foo}
        }
      ; { name = "patt-list-1" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< [a] >>|foo};
          expect = {foo|MLast.PaApp loc
  (MLast.PaApp loc
     (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "::")) (Ploc.VaVal []))
     (MLast.PaLid loc (Ploc.VaVal "a")))
  (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "[]")) (Ploc.VaVal []));
|foo}
        }
      ; { name = "patt-list-2" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:patt< [a;b] >>|foo};
          expect = {foo|MLast.PaApp loc
  (MLast.PaApp loc
     (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "::")) (Ploc.VaVal []))
     (MLast.PaLid loc (Ploc.VaVal "a")))
  (MLast.PaApp loc
     (MLast.PaApp loc
        (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "::")) (Ploc.VaVal []))
        (MLast.PaLid loc (Ploc.VaVal "b")))
     (MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "[]")) (Ploc.VaVal [])));
|foo}
        }
      ; { name = "patt-type-0" ;
          revised = ADD_SEMI;
          official = Some {foo|<:patt< (type a) >>|foo};
          expect = {foo|MLast.PaNty loc (Ploc.VaVal "a");
|foo}
        }
      ; { name = "patt-type-1" ;
          revised = ADD_SEMI;
          official = Some {foo|<:patt< (type $lid:PM.type_id p$) >>|foo};
          expect = {foo|MLast.PaNty loc (Ploc.VaVal (PM.type_id p));
|foo}
        }
      ; { name = "expr-long-1" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:expr< A . B >>|foo};
          expect = {foo|MLast.ExLong loc
  (MLast.LiAcc loc (MLast.LiUid loc (Ploc.VaVal "A")) (Ploc.VaVal "B"));
|foo}
        }
      ; { name = "expr-acc-1d" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:expr< $uid:e1$ . $lid:m$ >>|foo};
          expect = {foo|MLast.ExFle loc (MLast.ExLong loc (MLast.LiUid loc (Ploc.VaVal e1)))
  (Ploc.VaVal (None, Ploc.VaVal m));
|foo}
        }
      ; { name = "two-level-expr-1" ;
          revised = ADD_SEMI;
          official = Some {foo|<:expr< ($lid:x$, $lid:y$) >>|foo};
          expect = {foo|MLast.ExTup loc
  (Ploc.VaVal
     [MLast.ExLid loc (Ploc.VaVal x); MLast.ExLid loc (Ploc.VaVal y)]);
|foo}
        }
      ; { name = "extended-longident-1" ; 
          revised = ADD_SEMI;
          official = Some {foo|<:extended_longident< $longid:li$ . $uid:m$ >>|foo};
          expect = {foo|MLast.LiAcc loc li (Ploc.VaVal m);
|foo}
        }
      ; {
        name = "expr-extension-type-1";
        revised = ADD_SEMI;
        official = Some {foo|<:expr< [%typ: bool] >>|foo};
        expect = {foo|MLast.ExExten loc
  (Ploc.VaVal
     (Ploc.VaVal (loc, "typ"),
      MLast.TyAttr loc (Ploc.VaVal (MLast.TyLid loc (Ploc.VaVal "bool")))));
|foo}
      }
      ; {
        name = "patt-PaLong-1";
        revised = ADD_SEMI;
        official = Some {foo|<:patt< $longid:li$ (type $_list:loc_ids$ ) >>|foo};
        expect = {foo|MLast.PaLong loc li loc_ids;
|foo}
      }
      ; {
        name = "patt-PaLong-2";
        revised = ADD_SEMI;
        official = Some {foo|<:patt< $longid:li$ >>|foo};
        expect = {foo|MLast.PaLong loc li (Ploc.VaVal []);
|foo}
      }
      ; {
        name = "patt-PaLong-3";
        revised = ADD_SEMI;
        official = Some {foo|<:patt< $longid:li$ (type a) >>|foo};
        expect = {foo|MLast.PaLong loc li (Ploc.VaVal [(loc, "a")]);
|foo}
      }
      ; {
        name = "patt-PaLong-4";
        revised = ADD_SEMI;
        official = Some {foo|<:patt< $longid:li$ (type a b c) >>|foo};
        expect = {foo|MLast.PaLong loc li (Ploc.VaVal [(loc, "a"); (loc, "b"); (loc, "c")]);
|foo}
      }
      ; {
        name = "binders-external-1";
        revised = ADD_SEMI;
        official = Some {foo|<:str_item< external $_lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>|foo};
        expect = {foo|MLast.StExt loc i ls t pd attrs;
|foo}
      }
      ; {
        name = "binders-external-2";
        revised = ADD_SEMI;
        official = Some {foo|<:sig_item< external $_lid:i$ : $t$ = $_list:pd$ $_itemattrs:attrs$ >>|foo};
        expect = {foo|MLast.SgExt loc i (Ploc.VaVal []) t pd attrs;
|foo}
      }
      ;{
        name = "patt-patt-any";
        revised = CODE {foo| match x with [ <:patt< _ >> -> 1 ]; |foo} ;
        official = Some {foo| match x with <:patt< _ >> -> 1 |foo} ;
        expect = {foo|match x with [ MLast.PaAny _ -> 1 ];
|foo}
      }
      ; { name = "expr-apply-2" ;
          revised = CODE {foo|fun [ <:expr< $_$ $e2$ >> -> 1 ];|foo};
          official = Some {foo|function <:expr< $_$ $e2$ >> -> 1|foo};
          expect = {foo|fun
[ MLast.ExApp _ _ e2 -> 1 ];
|foo}
        }
      ; { name = "variants-1" ; 
          revised = CODE {foo|<:ctyp< [= $list:l$ ] >>;|foo};
          official = Some {foo|<:ctyp< [ | $list:l$ ] >>|foo};
          expect = {foo|MLast.TyVrn loc (Ploc.VaVal l) None;
|foo}
        }
      ; { name = "type-extension" ;
          revised = CODE {foo|<:str_item< type t += [ A ] >> ;|foo};
          official = Some {foo|<:str_item< type t +=  A  >> |foo};
          expect = {foo|MLast.StTypExten loc
  {MLast.teNam = Ploc.VaVal (None, Ploc.VaVal "t");
   MLast.tePrm = Ploc.VaVal []; MLast.tePrv = Ploc.VaVal False;
   MLast.teECs =
     Ploc.VaVal
       [MLast.EcTuple loc
          (loc, Ploc.VaVal "A", Ploc.VaVal [], Ploc.VaVal [], Ploc.VaVal None,
           Ploc.VaVal [])];
   MLast.teAttributes = Ploc.VaVal []};
|foo}
        }
      ; { name = "typedecl-0" ;
          revised = CODE {foo|<:str_item< type $lid:li$ = [ A ] >>;|foo};
          official = Some {foo|<:str_item< type $lid:li$ = A >>|foo};
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
|foo}
        }
      ; { name = "typedecl-1" ;
          revised = CODE {foo|fun [ <:sig_item< type $lid:x$ $list:_$ = $priv:_$ .. $_itemattrs:_$ >> -> 1 ] ;|foo} ;
          official = Some {foo|function <:sig_item< type ( $list:_$ ) $lid:x$ = $priv:_$ .. $_itemattrs:_$ >> -> 1 |foo} ;
          expect = {foo|fun
[ MLast.SgTyp _ (Ploc.VaVal False)
    (Ploc.VaVal
       [{MLast.tdIsDecl = Ploc.VaVal True;
         MLast.tdNam = Ploc.VaVal (_, Ploc.VaVal x);
         MLast.tdPrm = Ploc.VaVal _; MLast.tdPrv = Ploc.VaVal _;
         MLast.tdDef = MLast.TyOpn _; MLast.tdCon = Ploc.VaVal [];
         MLast.tdAttributes = _}]) ->
    1 ];
|foo}
        }
      ; { name = "typedecl-2" ;
          revised = CODE {foo|<:type_decl< $tp:x$ $list:pl$ = $tk$ >>;|foo};
          official = Some {foo|<:type_decl< ( $list:pl$ ) $tp:x$ = $tk$ >>|foo};
          expect = {foo|{MLast.tdIsDecl = Ploc.VaVal True; MLast.tdNam = Ploc.VaVal x;
 MLast.tdPrm = Ploc.VaVal pl; MLast.tdPrv = Ploc.VaVal False;
 MLast.tdDef = tk; MLast.tdCon = Ploc.VaVal [];
 MLast.tdAttributes = Ploc.VaVal []};
|foo}
        }
      ; { name = "typedecl-3" ;
          revised = CODE {foo|<:type_decl< $tp:(loc,x)$ $list:pl$ = $tk$ >>;|foo};
          official = Some {foo|<:type_decl< ( $list:pl$ ) $tp:(loc,x)$ = $tk$ >>|foo};
          expect = {foo|{MLast.tdIsDecl = Ploc.VaVal True; MLast.tdNam = Ploc.VaVal (loc, x);
 MLast.tdPrm = Ploc.VaVal pl; MLast.tdPrv = Ploc.VaVal False;
 MLast.tdDef = tk; MLast.tdCon = Ploc.VaVal [];
 MLast.tdAttributes = Ploc.VaVal []};
|foo}
        }
      ; { name = "typedecl-4" ;
          revised = CODE {foo|<:type_decl< t $variance:vastr$ $var:v$ = $tk$ >>;|foo};
          official = Some {foo|<:type_decl< $variance:vastr$ $var:v$ t = $tk$ >>|foo};
          expect = {foo|{MLast.tdIsDecl = Ploc.VaVal True; MLast.tdNam = Ploc.VaVal (loc, Ploc.VaVal "t");
 MLast.tdPrm = Ploc.VaVal [(Ploc.VaVal v, Ploc.VaVal vastr)]; MLast.tdPrv = Ploc.VaVal False;
 MLast.tdDef = tk; MLast.tdCon = Ploc.VaVal [];
 MLast.tdAttributes = Ploc.VaVal []};
|foo}
        }
      ; { name = "attribute-body-1" ;
          revised = CODE {foo|fun [ <:attribute_body< "add" $stri:si$ ; >> -> si ] ;|foo};
          official = Some {foo|function <:attribute_body< add $stri:si$ >> -> si|foo};
          expect = {foo|fun
[ (Ploc.VaVal (_, "add"), MLast.StAttr _ (Ploc.VaVal [si])) -> si ];
|foo}
        }
      ; { name = "attribute-body-2" ;
          revised = CODE {foo|<:attribute_body< "add" $stri:si$ ; >> ;|foo};
          official = Some {foo|<:attribute_body< add $stri:si$ >>|foo};
          expect = {foo|(Ploc.VaVal (loc, "add"), MLast.StAttr loc (Ploc.VaVal [si]));
|foo}
        }
      ; { name = "dotop-1" ;
          revised = CODE {foo|<:expr< $e$ $dotop:s$ ( $list:le$ ) >> ;|foo};
          official = Some {foo|<:expr< $e$ $dotop:s$ ( $list:le$ ) >>|foo};
          expect = {foo|MLast.ExAre loc (Ploc.VaVal s) e (Ploc.VaVal le);
|foo}
        }
      ; { name = "two-level-patt-1" ;
          revised = CODE {foo|fun [ <:expr:< ($lid:x$, $lid:y$) >> -> 1 ] ;|foo};
          official = Some {foo|function <:expr:< ($lid:x$, $lid:y$) >> -> 1|foo};
          expect = {foo|fun
[ MLast.ExTup loc
    (Ploc.VaVal
       [MLast.ExLid _ (Ploc.VaVal x); MLast.ExLid _ (Ploc.VaVal y)]) ->
    1 ];
|foo}
        }
      ; { name = "generic-constructor-1" ;
          revised = CODE {foo|fun [ <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:l$ >> -> 1 ];|foo} ;
          official = Some {foo|function <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:l$ >> -> 1|foo} ;

          expect = {foo|fun
[ (loc, Ploc.VaVal ci, Ploc.VaVal [], Ploc.VaVal tl, Ploc.VaVal None, l) ->
    1 ];
|foo}
        }
      ; { name = "generic-constructor-2" ;
          revised = CODE {foo|fun [ <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:l$ >> as gc -> 1 ];|foo} ;
          official = Some {foo|function <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:l$ >> as gc -> 1|foo} ;

          expect = {foo|fun
[ (loc, Ploc.VaVal ci, Ploc.VaVal [], Ploc.VaVal tl, Ploc.VaVal None,
   l) as gc ->
    1 ];
|foo}
        }
      ; { name = "generic-constructor-3" ;
          revised = CODE {foo|match b with [
    <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:_$ >> as gc -> 1 ];|foo} ;
          official = Some {foo|match b with
    <:constructor:< $uid:ci$ of $list:tl$ $_algattrs:_$ >> as gc -> 1|foo} ;
          expect = {foo|match b with
[ (loc, Ploc.VaVal ci, Ploc.VaVal [], Ploc.VaVal tl, Ploc.VaVal None,
   _) as gc ->
    1 ];
|foo}

        }
      ; {
        name = "binders-constructor-1";
        revised = CODE {foo|<:constructor< $_uid:ci$ of $_list:ls$ . $_list:tl$ $_rto:rto$ $_algattrs:attrs$ >> ;|foo};
        official = None;
        expect = {foo|(loc, ci, ls, tl, rto, attrs);
|foo}
      }
    ])
 ;

value type_functor_syntax_tests ~{pa} ~{pr} ~{revised} = "type_functor-syntax" >::: (List.map (mktest ~{pa} ~{pr} ~{revised=revised})
    [
      {
        name = "prototype";
        revised = SKIP;
        official = Some {foo||foo};
        expect = {foo||foo}
      }
     ;{
        name = "type-functor-0";
        revised = CODE {foo|<:ctyp< m:(module M:MT) -> t >>;|foo};
        official = Some {foo|<:ctyp< m:(module M:MT) -> t >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-1";
        revised = CODE {foo|<:ctyp< (module M:MT) -> t >>;|foo};
        official = Some {foo|<:ctyp< (module M:MT) -> t >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal None) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-2";
        revised = CODE {foo|<:ctyp< $lid:l$:(module M:MT) -> t >>;|foo};
        official = Some {foo|<:ctyp< $lid:l$:(module M:MT) -> t >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal l))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-3";
        revised = CODE {foo|<:ctyp< $lidopt:l$:(module M:MT) -> t >>;|foo};
        official = Some {foo|<:ctyp< $lidopt:l$:(module M:MT) -> t >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal l) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-4";
        revised = CODE {foo|<:ctyp< m:(module $uid:m$:MT) -> t >>;|foo};
        official = Some {foo|<:ctyp< m:(module $uid:m$:MT) -> t >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal m)
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-5";
        revised = CODE {foo|<:ctyp< m:(module M:$mt$) -> t >>;|foo};
        official = Some {foo|<:ctyp< m:(module M:$mt$) -> t >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  mt
  (MLast.TyLid loc (Ploc.VaVal "t"));
|foo}
      }
     ;{
        name = "type-functor-6";
        revised = CODE {foo|<:ctyp< m:(module M:MT) -> $ct$ >>;|foo};
        official = Some {foo|<:ctyp< m:(module M:MT) -> $ct$ >>|foo};
        expect = {foo|
MLast.TyFun loc (Ploc.VaVal (Some (Ploc.VaVal "m"))) (Ploc.VaVal "M")
  (MLast.MtLong loc (MLast.LiUid loc (Ploc.VaVal "MT")))
  ct;
|foo}
      }
    ])
 ;

value q_MLast_parser_tests ~{pa} ~{pr} = "q_MLast parser" >::: [
    "shared syntax" >: shared_syntax_tests ~{pa} ~{pr} ~{revised=True}
  ; "type_functor-syntax" >: type_functor_syntax_tests ~{pa} ~{pr} ~{revised=True}
]
;

value revised_parser_tests ~{pa} ~{pr} = "revised parser" >::: [
    "shared syntax" >: shared_syntax_tests ~{pa} ~{pr} ~{revised=True}
  ; "type_functor-syntax" >: type_functor_syntax_tests ~{pa} ~{pr} ~{revised=True}
]
;

value official_parser_tests ~{pa} ~{pr} = "official parser" >::: [
    "shared syntax" >: shared_syntax_tests ~{pa} ~{pr} ~{revised=False}
  ; "type_functor-syntax" >: type_functor_syntax_tests ~{pa} ~{pr} ~{revised=False}
]
;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
