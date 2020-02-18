(* camlp5r *)
(* papr_patrix_test.ml *)

open Testutil;
open Testutil2;

open OUnit2;
open OUnitTest;

value smart_exn_eq e1 e2 =
  let rec eqrec e1 e2 =
  match (e1, e2) with [
    (Ploc.Exc _ e1, Ploc.Exc _ e2) -> eqrec e1 e2
  | (Stream.Error msg1, Stream.Error msg2) -> msg1 = msg2
  | _ -> e1 = e2
  ]
  in eqrec e1 e2
;

type instance_t = {
  name : string ;
  r_input : (string * option exn);
  o_input : (string * option exn) ;
  r_output : (string * option exn) ;
  o_output : (string * option exn)
}
;

value test_matrix = [
    {name="simplest";
     o_input = ("(1; 2);; 3 ;; let x = 1 ;;", None) ;
     o_output = ({foo|let _ = 1; 2;;
let _ = 3;;
let x = 1;;
|foo}, None) ;
     r_output = ({foo|do { 1; 2 };
3;
value x = 1;
|foo}, None) ;
     r_input = ("do { 1; 2}; 3 ; value x = 1 ;", None)
    };
    {name="infix1";
     o_input = ("(a + b) c;;", None) ;
     o_output = ({foo|let _ = (a + b) c;;
|foo}, None) ;
     r_output = ({foo|(a + b) c;
|foo}, None) ;
     r_input = ("(a + b) c;", None)
    };
    {name="infix2";
     o_input = ("(a --> b) c;;", None) ;
     o_output = ({foo|let _ = (a --> b) c;;
|foo}, None) ;
     r_output = ({foo|(a --> b) c;
|foo}, None) ;
     r_input = ("(a --> b) c;", None)
    };
    {name="prefix1";
     o_input = ("(!!!a) c;;", None) ;
     o_output = ({foo|let _ = !!!a c;;
|foo}, None) ;
     r_output = ({foo|!!!a c;
|foo}, None) ;
     r_input = ("(!!!a) c;", None)
    };
    {name="dollar";
     o_input = ("a $ c;;", None) ;
     o_output = ({foo|let _ = a $ c;;
|foo}, None) ;
     r_output = ({foo|\$  a c;
|foo}, None) ;
     r_input = ("a $ c;", Some (Ploc.Exc Ploc.dummy (Stream.Error "';' expected after [str_item] (in [str_item_semi])")))
    }
]
;

value i2test inputf outputf i =
  i.name >:: (fun _ ->
    match (inputf i, outputf i) with [
      ((inputs, None), (outputs, None)) ->
        assert_equal ~{printer=(fun (x:string) -> x)}
          outputs (pr (pa1 inputs))
    | ((inputs, Some exn), _) ->
        assert_raises_exn_pred ~{msg=i.name} ~{exnmsg="msg"} (smart_exn_eq exn)
          (fun () -> pa1 inputs)
    | _ -> assert False
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
