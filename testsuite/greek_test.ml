(**pp -syntax camlp5r *)
(* r2r_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";\n" ;

open Papr_test_matrix ;

value test_matrix = [
    {name="greek-identifiers-1"; implem = True ;
     exclude=[];
     o_input = SKIP "" "";
     official_input = SKIP "" "" ;
     r_input = OK {foo|α;|foo} ;
     o_output = OK {foo|__alpha__|foo};
     official_output = OK {foo|;;__alpha__|foo} ;
     r_output = OK {foo|α;|foo}
    };
    {name="greek-identifiers-2"; implem = True ;
     exclude=[];
     o_input = SKIP "" "";
     official_input = SKIP "" "" ;
     r_input = OK {foo|ω₂;|foo} ;
     o_output = OK {foo|__alpha__|foo};
     official_output = OK {foo|;;__greek_cf89e28282|foo} ;
     r_output = OK {foo|ω₂;|foo}
    };
    {name="greek-identifiers-3"; implem = True ;
     exclude=[];
     o_input = SKIP "" "";
     official_input = SKIP "" "" ;
     r_input = OK {foo|αβ;|foo} ;
     o_output = OK {foo|__alpha__|foo};
     official_output = OK {foo|;;__greek_ceb1ceb2|foo} ;
     r_output = OK {foo|αβ;|foo}
    };
    {name="greek-expression-1"; implem = True ;
     exclude=[];
     o_input = SKIP "" "";
     official_input = SKIP "" "" ;
     r_input = OK {foo|α.β;|foo} ;
     o_output = SKIP "" "";
     official_output = OK {foo|;;__alpha__.__beta__|foo} ;
     r_output = OK {foo|α.β;|foo}
    };
    {name="greek-expression-2"; implem = True ;
     exclude=[];
     o_input = SKIP "" "";
     official_input = SKIP "" "" ;
     r_input = OK {foo|x.β;|foo} ;
     o_output = SKIP "" "";
     official_output = OK {foo|;;x.__beta__|foo} ;
     r_output = OK {foo|x.β;|foo}
    };
    {name="greek-pattern-1"; implem = True ;
     exclude=[];
     o_input = SKIP "" "";
     official_input = SKIP "" "" ;
     r_input = OK {foo|fun α -> 1;|foo} ;
     o_output = SKIP "" "";
     official_output = OK {foo|;;fun __alpha__ -> 1|foo} ;
     r_output = OK {foo|fun α → 1;|foo}
    };
    {name="greek-pattern-2"; implem = True ;
     exclude=[];
     o_input = SKIP "" "";
     official_input = SKIP "" "" ;
     r_input = OK {foo|fun [ A α -> 1 ];|foo} ;
     o_output = SKIP "" "";
     official_output = OK {foo|;;fun (A __alpha__) -> 1|foo} ;
     r_output = OK {foo|fun [ A α → 1 ];|foo}
    };
    {name="greek-type-variables-1"; implem = True ;
     exclude=[];
     o_input = OK {foo|type 'a succ = Succ of 'a|foo} ;
     official_input = OK {foo|type 'a succ = Succ of 'a|foo} ;
     r_input = OK {foo|type succ α = [ Succ of α ];|foo} ;
     o_output = OK {foo|type 'a succ =
    Succ of 'a;;
|foo};
     official_output = OK {foo|type 'a succ =
  | Succ of 'a |foo} ;
     r_output = OK {foo|type succ α =
  [ Succ of α ];
|foo}
    };
    {name="greek-type-variables-2"; implem = True ;
     exclude=[];
     o_input = OK {foo|let magic : 'a 'b. 'a -> 'b = ()
|foo} ;
     official_input = OK {foo|let magic : 'a 'b. 'a -> 'b = ()|foo} ;
     r_input = OK {foo|value magic : ! α β . α -> β = ();|foo} ;
     o_output = OK {foo|let magic : 'a 'b . 'a -> 'b = ();;
|foo} ;
     official_output = OK {foo|let magic : 'a 'b . 'a -> 'b = ()|foo} ;
     r_output = OK {foo|value magic : ! α β . α → β = ();
|foo}
    }
]
;

module PAPR = PAPRGen(MLParsers.RP.Base)(MLPrinters.RP.Base.Printers) ;

value r2r pa pp opa () = List.map (i2test ~{kind="r2r"} pa pp opa r_input KIND_Revised ) test_matrix ;

value revised_tests = "revised" >::: (r2r PAPR.both_pa1 PAPR.both_pr None ()) ;

module Official = struct
module Implem = struct
value pr l =
  Pr_official.(with_buffer_formatter pp_implem (l, Ploc.dummy))
;
end ;
module Interf = struct
value pr l =
  Pr_official.(with_buffer_formatter pp_interf (l, Ploc.dummy))
;
end ;
value both_pr = (Implem.pr, Interf.pr) ;
end ;

value r2official pa pp opa () = List.map (i2test ~{kind="r2official"} pa pp opa r_input KIND_Official ) test_matrix ;
value official_tests = "official" >::: (r2official PAPR.both_pa1 Official.both_pr (Some Testutil.Official.both_pa) ()) ;

value tests = "greek" >::: [ revised_tests; official_tests ] ;

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
