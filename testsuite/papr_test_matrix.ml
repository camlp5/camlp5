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

type input_desc_t = [
  OK of string
| EXN of string and exn
| SKIP of string and string
]
;

type instance_t = {
  name : string ;
  implem : bool ;
  r_input : input_desc_t;
  o_input : input_desc_t ;
  official_input : input_desc_t ;
  r_output : option (string * option exn) ;
  o_output : option (string * option exn) ;
  official_output : option (string * option exn)
}
;

value test_matrix = [
    {name="simplest"; implem = True ;
     o_input = OK "(1; 2);; 3 ;; let x = 1 ;;" ;
     official_input = OK "(1; 2);; 3 ;; let x = 1 ;;" ;
     r_input = OK "do { 1; 2}; 3 ; value x = 1 ;" ;
     o_output = Some ({foo|let _ = 1; 2;;
let _ = 3;;
let x = 1;;
|foo}, None) ;
     official_output = None ;
     r_output = Some ({foo|do { 1; 2 };
3;
value x = 1;
|foo}, None)
    };
    {name="infix1"; implem = True ;
     o_input = OK"(a + b) c;;" ;
     official_input = OK"(+) a b c;;" ;
     r_input = OK"(a + b) c;" ;
     o_output = Some ({foo|let _ = (a + b) c;;
|foo}, None) ;
     official_output = Some ({foo|;;(+) a b c|foo}, None) ;
     r_output = Some ({foo|(a + b) c;
|foo}, None)
    };
    {name="infix2"; implem = True ;
     o_input = OK "(a --> b) c;;" ;
     official_input = OK "(-->) a b c;;" ;
     r_input = OK"(a --> b) c;" ;
     o_output = Some ({foo|let _ = (a --> b) c;;
|foo}, None) ;
     official_output = Some ({foo|;;(-->) a b c|foo}, None) ;
     r_output = Some ({foo|(a --> b) c;
|foo}, None)
    };
    {name="prefix1"; implem = True ;
     o_input = OK"(!!!a) c;;" ;
     official_input = OK"(!!!) a c;;" ;
     r_input = OK"(!!!a) c;" ;
     o_output = Some ({foo|let _ = !!!a c;;
|foo}, None) ;
     official_output = Some ({foo|;;(!!!) a c|foo}, None) ;
     r_output = Some ({foo|!!!a c;
|foo}, None)
    };
    (* original syntax accepts "$" as an infix symbol; revised syntax DOES NOT *)
    {name="dollar"; implem = True ;
     o_input = OK"a $ c;;" ;
     official_input = OK"a $ c;;" ;
     r_input = EXN "a $ c;" (Ploc.Exc Ploc.dummy (Stream.Error "';' expected after [str_item] (in [str_item_semi])")) ;
     o_output = Some ({foo|let _ = a $ c;;
|foo}, None) ;
     official_output = Some ({foo|;;a $ c|foo}, None) ;
     r_output = Some ({foo|\$  a c;
|foo}, None)
    };
    {name="alg_attribute1"; implem = True ;
     o_input = OK"a[@foo];;" ;
     official_input = OK"a[@foo];;" ;
     r_input = OK"a [@foo];" ;
     o_output = Some ({foo|let _ = a[@foo];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ])|foo}, None) ;
     r_output = Some ({foo|a[@foo];
|foo}, None)
    };
    {name="alg_attribute2"; implem = True ;
     o_input = OK"a + b[@foo];;" ;
     official_input = OK"a + b[@foo];;" ;
     r_input = OK"a + b [@foo];" ;
     o_output = Some ({foo|let _ = a + b[@foo];;
|foo}, None) ;
     official_output = Some ({foo|;;((a + b)[@foo ])|foo}, None) ;
     r_output = Some ({foo|a + b[@foo];
|foo}, None)
    };
    {name="alg_attribute3"; implem = True ;
     o_input = OK"(a [@foo])[@bar];;" ;
     official_input = OK"(a [@foo])[@bar];;" ;
     r_input = OK"a[@foo][@bar];" ;
     o_output = Some ({foo|let _ = a[@foo][@bar];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ][@bar ])|foo}, None) ;
     r_output = Some ({foo|a[@foo][@bar];
|foo}, None)
    };
    {name="alg_attribute4"; implem = True ;
     o_input = OK"a [@foo :type t = int];;" ;
     official_input = OK"a [@foo :type t = int];;" ;
     r_input = OK"a[@foo :type t = int;];" ;
     o_output = Some ({foo|let _ = a[@foo: type t = int;;];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo :type t = int])|foo}, None) ;
     r_output = Some ({foo|a[@foo: type t = int;];
|foo}, None)
    };
    {name="alg_attribute5"; implem = True ;
     o_input = OK"a [@foo :int];;" ;
     official_input = OK"a [@foo :int];;" ;
     r_input = OK"a[@foo :int];" ;
     o_output = Some ({foo|let _ = a[@foo: int];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo :int])|foo}, None) ;
     r_output = Some ({foo|a[@foo: int];
|foo}, None)
    };
    {name="alg_attribute6"; implem = True ;
     o_input = OK"a [@foo ? (_,_)];;" ;
     official_input = OK"a [@foo ? (_,_)];;" ;
     r_input = OK"a[@foo ? (_,_)];" ;
     o_output = Some ({foo|let _ = a[@foo? _, _];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ?(_, _)])|foo}, None) ;
     r_output = Some ({foo|a[@foo? (_, _)];
|foo}, None)
    };
    {name="alg_attribute7"; implem = True ;
     o_input = OK"a [@foo ? (_,_) when true];;" ;
     official_input = OK"a [@foo ? (_,_) when true];;" ;
     r_input = OK"a[@foo ? (_,_) when True];" ;
     o_output = Some ({foo|let _ = a[@foo? _, _ when true];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ?(_, _) when true])|foo}, None) ;
     r_output = Some ({foo|a[@foo? (_, _) when True];
|foo}, None)
    };
    {name="alg_attribute8"; implem = True ;
     o_input = OK"a [@foo ? _,_ when true];;" ;
     official_input = OK"a [@foo ? _,_ when true];;" ;
     r_input = OK"a[@foo ? (_,_) when True];" ;
     o_output = Some ({foo|let _ = a[@foo? _, _ when true];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ?(_, _) when true])|foo}, None) ;
     r_output = None
    };
    {name="alg_attribute9"; implem = True ;
     o_input = OK"type t = int [@foo]" ;
     official_input = OK"type t = int [@foo]" ;
     r_input = OK"type t = int [@foo];" ;
     o_output = Some ({foo|type t = int[@foo];;
|foo}, None) ;
     official_output = Some ({foo|type t = ((int)[@foo ])|foo}, None) ;
     r_output = Some ({foo|type t = int[@foo];
|foo}, None)
    };
    {name="alg_attribute10"; implem = True ;
     o_input = OK"type t = int [@foo][@bar]" ;
     official_input = OK"type t = int [@foo][@bar]" ;
     r_input = OK"type t = int [@foo][@bar];" ;
     o_output = Some ({foo|type t = int[@foo][@bar];;
|foo}, None) ;
     official_output = Some ({foo|type t = ((int)[@foo ][@bar ])|foo}, None) ;
     r_output = Some ({foo|type t = int[@foo][@bar];
|foo}, None)
    };
    {name="alg_attribute11"; implem = True ;
     o_input = OK"function x|y[@foo] -> 1" ;
     official_input = SKIP "function x|y[@foo] -> 1" "this test is problematic but probably not an error" ;
     r_input = OK"fun [ (x|y[@foo]) -> 1 ];" ;
     o_output = Some ({foo|let _ =
  function
    x | y[@foo] -> 1;;
|foo}, None) ;
     official_output = Some ({foo|;;fun (x|((y)[@foo ])) -> 1|foo}, None) ;
     r_output = Some ({foo|fun
[ x | y[@foo] → 1 ];
|foo}, None)
    };
    {name="alg_attribute12"; implem = True ;
     o_input = OK"module M = struct end [@foo]" ;
     official_input = OK"module M = struct end [@foo]" ;
     r_input = OK"module M = struct end [@foo];" ;
     o_output = Some ({foo|module M = struct  end[@foo];;
|foo}, None) ;
     official_output = Some ({foo|module M = ((struct  end)[@foo ])|foo}, None) ;
     r_output = Some ({foo|module M = struct  end[@foo];
|foo}, None)
    };
    {name="alg_attribute13"; implem = True ;
     o_input = OK"class t = object end [@foo]" ;
     official_input = OK"class t = object end [@foo]" ;
     r_input = OK"class t = object end [@foo];" ;
     o_output = Some ({foo|class t = object  end[@foo];;
|foo}, None) ;
     official_output = Some ({foo|class t = ((object  end)[@foo ])|foo}, None) ;
     r_output = Some ({foo|class t = object  end[@foo];
|foo}, None)
    };
    {name="alg_attribute13"; implem = True ;
     o_input = OK"class type ['a ] t = object end [@foo]" ;
     official_input = OK"class type ['a ] t = object end [@foo]" ;
     r_input = OK"class type t ['a] = object end [@foo];" ;
     o_output = Some ({foo|class type ['a] t = object  end[@foo];;
|foo}, None) ;
     official_output = Some ({foo|class type ['a] t = object  end[@foo ]|foo}, None) ;
     r_output = Some ({foo|class type t ['a] = object  end[@foo];
|foo}, None)
    };
    {name="alg_attribute14"; implem = True ;
     o_input = OK"type t = { a : int [@foo] }" ;
     official_input = OK"type t = { a : int [@foo] }" ;
     r_input = OK"type t = { a : int [@foo] };" ;
     o_output = Some ({foo|type t = { a : int[@foo] };;
|foo}, None) ;
     official_output = Some ({foo|type t = {
  a: int [@foo ]}|foo}, None) ;
     r_output = Some ({foo|type t = { a : int[@foo] };
|foo}, None)
    };
    {name="alg_attribute15"; implem = True ;
     o_input = OK"type t = { a : (int [@bar]) [@foo] }" ;
     official_input = OK"type t = { a : (int [@bar]) [@foo] }" ;
     r_input = OK"type t = { a : (int [@bar]) [@foo] };" ;
     o_output = Some ({foo|type t = { a : (int[@bar])[@foo] };;
|foo}, None) ;
     official_output = Some ({foo|type t = {
  a: ((int)[@bar ]) [@foo ]}|foo}, None) ;
     r_output = Some ({foo|type t = { a : (int[@bar])[@foo] };
|foo}, None)
    };
    {name="alg_attribute16"; implem = True ;
     o_input = OK"type t = a * (b[@bar])" ;
     official_input = OK"type t = a * (b[@bar])" ;
     r_input = OK"type t = (a * b[@bar]);" ;
     o_output = Some ({foo|type t = a * (b[@bar]);;
|foo}, None) ;
     official_output = Some ({foo|type t = (a * ((b)[@bar ]))|foo}, None) ;
     r_output = Some ({foo|type t = (a * b[@bar]);
|foo}, None)
    };
    {name="alg_attribute17"; implem = True ;
     o_input = OK"type t = a * b[@bar]" ;
     official_input = OK"type t = a * b[@bar]" ;
     r_input = OK"type t = (a * b)[@bar];" ;
     o_output = Some ({foo|type t = a * b[@bar];;
|foo}, None) ;
     official_output = Some ({foo|type t = (((a * b))[@bar ])|foo}, None) ;
     r_output = Some ({foo|type t = (a * b)[@bar];
|foo}, None)
    };

    {name="alg_attribute19"; implem = True ;
     o_input = OK"type t = { a : ((int * bool)[@bar]) [@foo] }" ;
     official_input = OK"type t = { a : ((int * bool)[@bar]) [@foo] }" ;
     r_input = OK"type t = { a : ((int * bool)[@bar]) [@foo] };" ;
     o_output = Some ({foo|type t = { a : (int * bool[@bar])[@foo] };;
|foo}, None) ;
     official_output = Some ({foo|type t = {
  a: (((int * bool))[@bar ]) [@foo ]}|foo}, None) ;
     r_output = Some ({foo|type t = { a : ((int * bool)[@bar])[@foo] };
|foo}, None)
    };

    {name="simple-interf"; implem = False ;
     o_input = OK"val x : int" ;
     official_input = OK"val x : int" ;
     r_input = OK"value x : int;" ;
     o_output = Some ({foo|val x : int;;
|foo}, None) ;
     official_output = Some ({foo|val x : int|foo}, None) ;
     r_output = Some ({foo|value x : int;
|foo}, None)
    };
    {name="item_attribute1"; implem = False ;
     o_input = OK"val x : int [@@foo]" ;
     official_input = OK"val x : int [@@foo]" ;
     r_input = OK"value x : int[@@foo];" ;
     o_output = Some ({foo|val x : int[@@foo];;
|foo}, None) ;
     official_output = Some ({foo|val x : int[@@foo ]|foo}, None) ;
     r_output = Some ({foo|value x : int[@@foo];
|foo}, None)
    };
    {name="item_attribute2"; implem = True ;
     o_input = OK"1 [@@foo]" ;
     official_input = OK"1 [@@foo]" ;
     r_input = OK"do { 1 } [@@foo];" ;
     o_output = Some ({foo|let _ = 1[@@foo];;
|foo}, None) ;
     official_output = Some ({foo|;;1[@@foo ]|foo}, None) ;
     r_output = Some ({foo|1[@@foo];
|foo}, None)
    };
    {name="item_attribute3"; implem = True ;
     o_input = OK"type nonrec t1 = int [@@bar] and t2 = bool [@@foo]" ;
     official_input = OK"type nonrec t1 = int [@@bar] and t2 = bool [@@foo]" ;
     r_input = OK"type nonrec t1 = int [@@bar] and t2 = bool [@@foo];" ;
     o_output = Some ({foo|type nonrec t1 = int[@@bar]
and t2 = bool[@@foo];;
|foo}, None) ;
     official_output = Some ({foo|type nonrec t1 = int[@@bar ]
and t2 = bool[@@foo ]|foo}, None) ;
     r_output = Some ({foo|type nonrec t1 = int[@@bar]
and t2 = bool[@@foo];
|foo}, None)
    };
    {name="exception-decl-attributes1"; implem = True ;
     o_input = OK"exception Foo of int [@@foo]" ;
     official_input = OK"exception Foo of int [@@foo]" ;
     r_input = OK"exception Foo of int [@@foo];" ;
     o_output = Some ({foo|exception Foo of int[@@foo];;
|foo}, None) ;
     official_output = Some ({foo|exception Foo of int [@@foo ]|foo}, None) ;
     r_output = Some ({foo|exception Foo of int[@@foo];
|foo}, None)
    };
    {name="exception-decl-attributes2"; implem = True ;
     o_input = OK"exception T of (int [@alg_foo]) [@alg_bar] [@@item_bar]" ;
     official_input = OK"exception T of (int [@alg_foo]) [@alg_bar] [@@item_bar]" ;
     r_input = OK"exception T of (int [@alg_foo]) [@alg_bar] [@@item_bar] ;" ;
     o_output = Some ({foo|exception T of (int[@alg_foo])[@alg_bar][@@item_bar];;
|foo}, None) ;
     official_output = Some ({foo|exception T of ((int)[@alg_foo ]) [@alg_bar ][@@item_bar ]|foo}, None) ;
     r_output = Some ({foo|exception T of (int[@alg_foo])[@alg_bar][@@item_bar];
|foo}, None)
    }
]
;

value fmt_string s = Printf.sprintf "<<%s>>" s ;

value i2test (pa_implem,pa_interf)  (pp_implem, pp_interf) inputf outputf i =
  i.name >:: (fun _ ->
    match (i.implem, inputf i, outputf i) with [

      (_,SKIP inputs msg, _) ->
        todo i.name   

    | (True,OK inputs, None) ->
        ignore(pa_implem inputs)

    | (False,OK inputs, None) ->
        ignore(pa_interf inputs)

    | (True, OK inputs, Some (outputs, None)) ->
        assert_equal ~{printer=fmt_string}
          outputs (wrap_err pp_implem (wrap_err pa_implem inputs))

    | (False, OK inputs, Some (outputs, None)) ->
        assert_equal ~{printer=fmt_string}
          outputs (wrap_err pp_interf (wrap_err pa_interf inputs))

    | (True,EXN inputs exn, _) ->
        assert_raises_exn_pred ~{msg=i.name} ~{exnmsg="msg"} (smart_exn_eq exn)
          (fun () -> pa_implem inputs)

    | (False,EXN inputs exn, _) ->
        assert_raises_exn_pred ~{msg=i.name} ~{exnmsg="msg"} (smart_exn_eq exn)
          (fun () -> pa_interf inputs)

    | _ -> assert False
    ])
;

value r_input i = i.r_input ;
value r_output i = i.r_output ;
value o_input i = i.o_input ;
value o_output i = i.o_output ;
value official_output i = i.official_output ;
value official_input i = i.official_input ;

value r2r pa pp () = List.map (i2test pa pp r_input r_output ) test_matrix ;
value r2o pa pp () = List.map (i2test pa pp r_input o_output ) test_matrix ;
value o2r pa pp () = List.map (i2test pa pp o_input r_output ) test_matrix ;
value o2o pa pp () = List.map (i2test pa pp o_input o_output ) test_matrix ;
value o2official pa pp () = List.map (i2test pa pp o_input official_output ) test_matrix ;
value official2official pa pp () = List.map (i2test pa pp official_input official_output ) test_matrix ;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
