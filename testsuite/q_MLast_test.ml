(* camlp5r *)
(* q_MLast_test.ml *)
#load "pa_macro.cmo";

open Testutil ;
open Testutil2 ;
open OUnit2 ;
open OUnitTest ;

Pcaml.inter_phrases.val := Some (";\n") ;

value pa1 = PAPR.Implem.pa1 ;
value pr = PAPR.Implem.pr ;
value fmt_string s = Printf.sprintf "<<%s>>" s ;

type instance = {
    name : string
  ; code : string
  ; expect : string
}
;

value mktest i = 
i.name >:: (fun  [ _ ->
        assert_equal ~{msg="not equal"} ~{printer=fmt_string}
          i.expect
          (pr (pa1 i.code))
                         ])
;

value tests = "test pa_r+quotations -> pr_r" >::: (List.map mktest
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
      ;{
        name = "patt-patt-any";
        code = {foo| match x with [ <:patt< _ >> -> 1 ]; |foo} ;
        expect = {foo|match x with [ MLast.PaAny _ → 1 ];
|foo}
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
      ; { name = "variants-1" ; 
          expect = {foo|MLast.TyVrn loc (Ploc.VaVal l) None;
|foo} ;
          code = {foo|<:ctyp< [= $list:l$ ] >>; |foo}
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
          expect = {foo|MLast.PaLong loc (MLast.LiUid loc (Ploc.VaVal "[]"));
|foo} ;
          code = {foo|<:patt< [] >> ;|foo}
        }
      ; { name = "type-extension" ; 
          expect = {foo|MLast.StTypExten loc
  {MLast.teNam = Ploc.VaVal (None, Ploc.VaVal "t");
   MLast.tePrm = Ploc.VaVal []; MLast.tePrv = Ploc.VaVal False;
   MLast.teECs =
     Ploc.VaVal
       [MLast.EcTuple
          (loc, Ploc.VaVal "A", Ploc.VaVal [], None, Ploc.VaVal [])];
   MLast.teAttributes = Ploc.VaVal []};
|foo} ;
          code = {foo|<:str_item< type t += [ A ] >> ;|foo}
        }
      ; { name = "prototype" ; 
          expect = {foo||foo} ;
          code = {foo||foo}
        }
      ; { name = "prototype" ; 
          expect = {foo||foo} ;
          code = {foo||foo}
        }
    ])
 ;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main tests
else ()
;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
