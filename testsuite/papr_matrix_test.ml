(* camlp5r *)
(* papr_patrix_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

type instance_t = {
  name : string ;
  r_input : string ;
  o_input : string ;
  r_output : string ;
  o_output : string
}
;

value test_matrix = [
    {name="simplest";
     o_input = "(1; 2);; 3 ;; let x = 1 ;;" ;
     o_output = {foo|let _ = 1; 2;;
let _ = 3;;
let x = 1;;
|foo} ;
     r_output = {foo|do { 1; 2 };
3;
value x = 1;
|foo} ;
     r_input = "do { 1; 2}; 3 ; value x = 1 ;"
    };
    {name="infix1";
     o_input = "(a + b) c;;" ;
     o_output = {foo|let _ = (a + b) c;;
|foo} ;
     r_output = {foo|(a + b) c;
|foo} ;
     r_input = "(a + b) c;"
    };
    {name="infix2";
     o_input = "(a --> b) c;;" ;
     o_output = {foo|let _ = (a --> b) c;;
|foo} ;
     r_output = {foo|(a --> b) c;
|foo} ;
     r_input = "(a --> b) c;"
    };
    {name="prefix1";
     o_input = "(!!!a) c;;" ;
     o_output = {foo|let _ = !!!a c;;
|foo} ;
     r_output = {foo|!!!a c;
|foo} ;
     r_input = "(!!!a) c;"
    }
]
;

value i2test input output i =
  i.name >:: (fun [ _ ->
        assert_equal ~{printer=(fun (x:string) -> x)}
          (output i)
          (wrap_err pr (wrap_err pa1 (input i)))
                        ])
;

value r_input i = i.r_input ;
value r_output i = i.r_output ;
value o_input i = i.o_input ;
value o_output i = i.o_output ;

value r2r () = List.map (i2test r_input r_output ) test_matrix ;
value r2o () = List.map (i2test r_input o_output ) test_matrix ;
value o2r () = List.map (i2test o_input r_output ) test_matrix ;
value o2o () = List.map (i2test o_input o_output ) test_matrix ;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
