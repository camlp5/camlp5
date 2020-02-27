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
  | (Failure msg1, Failure msg2) -> msg1 = msg2
  | (Syntaxerr.Error (Other _), Syntaxerr.Error (Other _)) -> True
  | _ -> e1 = e2
  ]
  in eqrec e1 e2
;

type step_desc_t = [
  OK of string
| EXN of string and exn
| SKIP of string and string
| TODO of string
]
;

type instance_t = {
  name : string ;
  implem : bool ;
  r_input : step_desc_t;
  o_input : step_desc_t ;
  official_input : step_desc_t ;
  r_output : step_desc_t ;
  o_output : step_desc_t ;
  official_output : step_desc_t
}
;

value test_matrix = [
    {name="test-prototype"; implem = True ;
     o_input = OK {foo||foo} ;
     official_input = OK {foo||foo} ;
     r_input = OK {foo||foo} ;
     o_output = OK {foo||foo};
     official_output = OK {foo||foo} ;
     r_output = OK {foo||foo}
    };
    {name="simplest"; implem = True ;
     o_input = OK "(1; 2);; 3 ;; let x = 1 ;;" ;
     official_input = OK "(1; 2);; 3 ;; let x = 1 ;;" ;
     r_input = OK "do { 1; 2}; 3 ; value x = 1 ;" ;
     o_output = OK {foo|let _ = 1; 2;;
let _ = 3;;
let x = 1;;
|foo} ;
     official_output = OK {foo|;;1; 2
;;3
let x = 1|foo};
     r_output = OK {foo|do { 1; 2 };
3;
value x = 1;
|foo}
    };
    {name="infix1"; implem = True ;
     o_input = OK"(a + b) c;;" ;
     official_input = OK"(+) a b c;;" ;
     r_input = OK"(a + b) c;" ;
     o_output = OK {foo|let _ = (a + b) c;;
|foo} ;
     official_output = OK {foo|;;(+) a b c|foo} ;
     r_output = OK{foo|(a + b) c;
|foo}
    };
    {name="infix2"; implem = True ;
     o_input = OK "(a --> b) c;;" ;
     official_input = OK "(-->) a b c;;" ;
     r_input = OK"(a --> b) c;" ;
     o_output = OK {foo|let _ = (a --> b) c;;
|foo} ;
     official_output = OK {foo|;;(-->) a b c|foo} ;
     r_output = OK {foo|(a --> b) c;
|foo}
    };
    {name="prefix1"; implem = True ;
     o_input = OK"(!!!a) c;;" ;
     official_input = OK"(!!!) a c;;" ;
     r_input = OK"(!!!a) c;" ;
     o_output = OK {foo|let _ = !!!a c;;
|foo} ;
     official_output = OK {foo|;;(!!!) a c|foo} ;
     r_output = OK {foo|!!!a c;
|foo}
    };
    (* original syntax accepts "$" as an infix symbol; revised syntax DOES NOT *)
    {name="dollar"; implem = True ;
     o_input = OK"a $ c;;" ;
     official_input = OK"a $ c;;" ;
     r_input = EXN "a $ c;" (Ploc.Exc Ploc.dummy (Stream.Error "';' expected after [str_item] (in [str_item_semi])")) ;
     o_output = OK {foo|let _ = a $ c;;
|foo} ;
     official_output = OK {foo|;;a $ c|foo} ;
     r_output = OK {foo|\$  a c;
|foo}
    };
    {name="alg_attribute1"; implem = True ;
     o_input = OK"a[@foo];;" ;
     official_input = OK"a[@foo];;" ;
     r_input = OK"a [@foo];" ;
     o_output = OK {foo|let _ = a[@foo];;
|foo} ;
     official_output = OK {foo|;;((a)[@foo ])|foo} ;
     r_output = OK {foo|a[@foo];
|foo}
    };
    {name="alg_attribute2"; implem = True ;
     o_input = OK"a + b[@foo];;" ;
     official_input = OK"a + b[@foo];;" ;
     r_input = OK"a + b [@foo];" ;
     o_output = OK {foo|let _ = a + b[@foo];;
|foo} ;
     official_output = OK {foo|;;((a + b)[@foo ])|foo} ;
     r_output = OK {foo|a + b[@foo];
|foo}
    };
    {name="alg_attribute3"; implem = True ;
     o_input = OK"(a [@foo])[@bar];;" ;
     official_input = OK"(a [@foo])[@bar];;" ;
     r_input = OK"a[@foo][@bar];" ;
     o_output = OK {foo|let _ = a[@foo][@bar];;
|foo} ;
     official_output = OK {foo|;;((a)[@foo ][@bar ])|foo} ;
     r_output = OK {foo|a[@foo][@bar];
|foo}
    };
    {name="alg_attribute4"; implem = True ;
     o_input = OK"a [@foo :type t = int];;" ;
     official_input = OK"a [@foo :type t = int];;" ;
     r_input = OK"a[@foo :type t = int;];" ;
     o_output = OK {foo|let _ = a[@foo: type t = int;;];;
|foo} ;
     official_output = OK {foo|;;((a)[@foo :type t = int])|foo} ;
     r_output = OK{foo|a[@foo: type t = int;];
|foo}
    };
    {name="alg_attribute5"; implem = True ;
     o_input = OK"a [@foo :int];;" ;
     official_input = OK"a [@foo :int];;" ;
     r_input = OK"a[@foo :int];" ;
     o_output = OK {foo|let _ = a[@foo: int];;
|foo} ;
     official_output = OK {foo|;;((a)[@foo :int])|foo} ;
     r_output = OK {foo|a[@foo: int];
|foo}
    };
    {name="alg_attribute6"; implem = True ;
     o_input = OK"a [@foo ? (_,_)];;" ;
     official_input = OK"a [@foo ? (_,_)];;" ;
     r_input = OK"a[@foo ? (_,_)];" ;
     o_output = OK {foo|let _ = a[@foo? _, _];;
|foo} ;
     official_output = OK {foo|;;((a)[@foo ?(_, _)])|foo} ;
     r_output = OK {foo|a[@foo? (_, _)];
|foo}
    };
    {name="alg_attribute7"; implem = True ;
     o_input = OK"a [@foo ? (_,_) when true];;" ;
     official_input = OK"a [@foo ? (_,_) when true];;" ;
     r_input = OK"a[@foo ? (_,_) when True];" ;
     o_output = OK {foo|let _ = a[@foo? _, _ when true];;
|foo} ;
     official_output = OK {foo|;;((a)[@foo ?(_, _) when true])|foo} ;
     r_output = OK {foo|a[@foo? (_, _) when True];
|foo}
    };
    {name="alg_attribute8"; implem = True ;
     o_input = OK"a [@foo ? _,_ when true];;" ;
     official_input = OK"a [@foo ? _,_ when true];;" ;
     r_input = OK"a[@foo ? (_,_) when True];" ;
     o_output = OK {foo|let _ = a[@foo? _, _ when true];;
|foo} ;
     official_output = OK {foo|;;((a)[@foo ?(_, _) when true])|foo} ;
     r_output = OK "a[@foo? (_, _) when True];
"
    };
    {name="alg_attribute9"; implem = True ;
     o_input = OK"type t = int [@foo]" ;
     official_input = OK"type t = int [@foo]" ;
     r_input = OK"type t = int [@foo];" ;
     o_output = OK {foo|type t = int[@foo];;
|foo} ;
     official_output = OK {foo|type t = ((int)[@foo ])|foo} ;
     r_output = OK {foo|type t = int[@foo];
|foo}
    };
    {name="alg_attribute10"; implem = True ;
     o_input = OK"type t = int [@foo][@bar]" ;
     official_input = OK"type t = int [@foo][@bar]" ;
     r_input = OK"type t = int [@foo][@bar];" ;
     o_output = OK {foo|type t = int[@foo][@bar];;
|foo} ;
     official_output = OK {foo|type t = ((int)[@foo ][@bar ])|foo} ;
     r_output = OK {foo|type t = int[@foo][@bar];
|foo}
    };
    {name="alg_attribute11"; implem = True ;
     o_input = OK"function x|y[@foo] -> 1" ;
     official_input = SKIP "function x|y[@foo] -> 1" "this test is problematic but probably not an error" ;
     r_input = OK"fun [ (x|y[@foo]) -> 1 ];" ;
     o_output = OK {foo|let _ =
  function
    x | y[@foo] -> 1;;
|foo} ;
     official_output = OK {foo|;;fun (x|((y)[@foo ])) -> 1|foo} ;
     r_output = OK {foo|fun
[ x | y[@foo] → 1 ];
|foo}
    };
    {name="alg_attribute12"; implem = True ;
     o_input = OK"module M = struct end [@foo]" ;
     official_input = OK"module M = struct end [@foo]" ;
     r_input = OK"module M = struct end [@foo];" ;
     o_output = OK {foo|module M = struct  end[@foo];;
|foo} ;
     official_output = OK {foo|module M = ((struct  end)[@foo ])|foo} ;
     r_output = OK {foo|module M = struct  end[@foo];
|foo}
    };
    {name="alg_attribute13"; implem = True ;
     o_input = OK"class t = object end [@foo]" ;
     official_input = OK"class t = object end [@foo]" ;
     r_input = OK"class t = object end [@foo];" ;
     o_output = OK {foo|class t = object  end[@foo];;
|foo} ;
     official_output = OK {foo|class t = ((object  end)[@foo ])|foo} ;
     r_output = OK {foo|class t = object  end[@foo];
|foo}
    };
    {name="alg_attribute13"; implem = True ;
     o_input = OK"class type ['a ] t = object end [@foo]" ;
     official_input = OK"class type ['a ] t = object end [@foo]" ;
     r_input = OK"class type t ['a] = object end [@foo];" ;
     o_output = OK {foo|class type ['a] t = object  end[@foo];;
|foo} ;
     official_output = OK {foo|class type ['a] t = object  end[@foo ]|foo} ;
     r_output = OK {foo|class type t ['a] = object  end[@foo];
|foo}
    };
    {name="alg_attribute14"; implem = True ;
     o_input = OK"type t = { a : int [@foo] }" ;
     official_input = OK"type t = { a : int [@foo] }" ;
     r_input = OK"type t = { a : int [@foo] };" ;
     o_output = OK {foo|type t = { a : int[@foo] };;
|foo} ;
     official_output = OK {foo|type t = {
  a: int [@foo ]}|foo} ;
     r_output = OK {foo|type t = { a : int[@foo] };
|foo}
    };
    {name="alg_attribute15"; implem = True ;
     o_input = OK"type t = { a : (int [@bar]) [@foo] }" ;
     official_input = OK"type t = { a : (int [@bar]) [@foo] }" ;
     r_input = OK"type t = { a : (int [@bar]) [@foo] };" ;
     o_output = OK {foo|type t = { a : (int[@bar])[@foo] };;
|foo} ;
     official_output = OK {foo|type t = {
  a: ((int)[@bar ]) [@foo ]}|foo} ;
     r_output = OK {foo|type t = { a : (int[@bar])[@foo] };
|foo}
    };
    {name="alg_attribute16"; implem = True ;
     o_input = OK"type t = a * (b[@bar])" ;
     official_input = OK"type t = a * (b[@bar])" ;
     r_input = OK"type t = (a * b[@bar]);" ;
     o_output = OK {foo|type t = a * (b[@bar]);;
|foo} ;
     official_output = OK {foo|type t = (a * ((b)[@bar ]))|foo} ;
     r_output = OK {foo|type t = (a * b[@bar]);
|foo}
    };
    {name="alg_attribute17"; implem = True ;
     o_input = OK"type t = a * b[@bar]" ;
     official_input = OK"type t = a * b[@bar]" ;
     r_input = OK"type t = (a * b)[@bar];" ;
     o_output = OK {foo|type t = a * b[@bar];;
|foo} ;
     official_output = OK {foo|type t = (((a * b))[@bar ])|foo} ;
     r_output = OK {foo|type t = (a * b)[@bar];
|foo}
    };
    {name="alg_attribute19"; implem = True ;
     o_input = OK"type t = { a : ((int * bool)[@bar]) [@foo] }" ;
     official_input = OK"type t = { a : ((int * bool)[@bar]) [@foo] }" ;
     r_input = OK"type t = { a : ((int * bool)[@bar]) [@foo] };" ;
     o_output = OK {foo|type t = { a : (int * bool[@bar])[@foo] };;
|foo} ;
     official_output = OK {foo|type t = {
  a: (((int * bool))[@bar ]) [@foo ]}|foo} ;
     r_output = OK {foo|type t = { a : ((int * bool)[@bar])[@foo] };
|foo}
    };
    {name="poly-variant-alg-attribute1"; implem = True ;
     o_input = OK {foo|type t = [ `Foo [@alg_foo] ]|foo} ;
     official_input = OK {foo|type t = [ `Foo [@alg_foo] ]|foo} ;
     r_input = OK {foo|type t = [= `Foo [@alg_foo] ];|foo} ;
     o_output = OK {foo|type t = [ `Foo[@alg_foo] ];;
|foo} ;
     official_output = OK {foo|type t = [ `Foo [@alg_foo ]]|foo} ;
     r_output = OK {foo|type t = [ = `Foo[@alg_foo] ];
|foo}
    };
    {name="poly-variant-alg-attribute2"; implem = True ;
     o_input = OK {foo|type t = [ `Foo of (int [@alg_bar]) [@alg_foo] ]|foo} ;
     official_input = OK {foo|type t = [ `Foo of (int [@alg_bar]) [@alg_foo] ]|foo} ;
     r_input = OK {foo|type t = [= `Foo of (int [@alg_bar])[@alg_foo] ];|foo} ;
     o_output = OK {foo|type t = [ `Foo of int[@alg_bar][@alg_foo] ];;
|foo} ;
     official_output = OK {foo|type t = [ `Foo of ((int)[@alg_bar ]) [@alg_foo ]]|foo} ;
     r_output = OK {foo|type t = [ = `Foo of int[@alg_bar][@alg_foo] ];
|foo}
    };

    {name="simple-interf"; implem = False ;
     o_input = OK"val x : int" ;
     official_input = OK"val x : int" ;
     r_input = OK"value x : int;" ;
     o_output = OK {foo|val x : int;;
|foo} ;
     official_output = OK {foo|val x : int|foo} ;
     r_output = OK {foo|value x : int;
|foo}
    };
    {name="item_attribute1"; implem = False ;
     o_input = OK"val x : int [@@foo]" ;
     official_input = OK"val x : int [@@foo]" ;
     r_input = OK"value x : int[@@foo];" ;
     o_output = OK {foo|val x : int[@@foo];;
|foo} ;
     official_output = OK {foo|val x : int[@@foo ]|foo} ;
     r_output = OK {foo|value x : int[@@foo];
|foo}
    };
    {name="item_attribute2"; implem = True ;
     o_input = OK"1 [@@foo]" ;
     official_input = OK"1 [@@foo]" ;
     r_input = OK"do { 1 } [@@foo];" ;
     o_output = OK {foo|let _ = 1[@@foo];;
|foo} ;
     official_output = OK {foo|;;1[@@foo ]|foo} ;
     r_output = OK {foo|1[@@foo];
|foo}
    };
    {name="item_attribute3"; implem = True ;
     o_input = OK"type nonrec t1 = int [@@bar] and t2 = bool [@@foo]" ;
     official_input = OK"type nonrec t1 = int [@@bar] and t2 = bool [@@foo]" ;
     r_input = OK"type nonrec t1 = int [@@bar] and t2 = bool [@@foo];" ;
     o_output = OK {foo|type nonrec t1 = int[@@bar]
and t2 = bool[@@foo];;
|foo} ;
     official_output = OK {foo|type nonrec t1 = int[@@bar ]
and t2 = bool[@@foo ]|foo} ;
     r_output = OK {foo|type nonrec t1 = int[@@bar]
and t2 = bool[@@foo];
|foo}
    };
    {name="exception-decl-attributes1"; implem = True ;
     o_input = OK"exception Foo of int [@@foo]" ;
     official_input = OK"exception Foo of int [@@foo]" ;
     r_input = OK"exception Foo of int [@@foo];" ;
     o_output = OK {foo|exception Foo of int[@@foo];;
|foo} ;
     official_output = OK {foo|exception Foo of int [@@foo ]|foo} ;
     r_output = OK {foo|exception Foo of int[@@foo];
|foo}
    };
    {name="exception-decl-attributes2"; implem = True ;
     o_input = OK"exception T of (int [@alg_foo]) [@alg_bar] [@@item_bar]" ;
     official_input = OK"exception T of (int [@alg_foo]) [@alg_bar] [@@item_bar]" ;
     r_input = OK"exception T of (int [@alg_foo]) [@alg_bar] [@@item_bar] ;" ;
     o_output = OK {foo|exception T of (int[@alg_foo])[@alg_bar][@@item_bar];;
|foo} ;
     official_output = OK {foo|exception T of ((int)[@alg_foo ]) [@alg_bar ][@@item_bar ]|foo} ;
     r_output = OK {foo|exception T of (int[@alg_foo])[@alg_bar][@@item_bar];
|foo}
    };
    {name="constructor-decl-attributes1"; implem = True ;
     o_input = OK"type t = A of int * bool [@alg_foo] | B of bool * string [@alg_bar] [@@item_bar]" ;
     official_input = OK"type t = A of int * bool [@alg_foo] | B of bool * string [@alg_bar] [@@item_bar]" ;
     r_input = OK"type t = [ A of int and bool [@alg_foo] | B of bool and string [@alg_bar] ] [@@item_bar];" ;
     o_output = OK {foo|type t =
    A of int * bool[@alg_foo]
  | B of bool * string[@alg_bar][@@item_bar];;
|foo} ;
     official_output = OK {foo|type t =
  | A of int * bool [@alg_foo ]
  | B of bool * string [@alg_bar ][@@item_bar ]|foo} ;
     r_output = OK {foo|type t =
  [ A of int and bool[@alg_foo]
  | B of bool and string[@alg_bar] ][@@item_bar];
|foo}
    };
    {name="module-expr-item-attributes1"; implem = True ;
     o_input = OK{foo|module M = struct end [@alg_foo] [@@item_bar]|foo} ;
     official_input = OK{foo|module M = struct end [@alg_foo] [@@item_bar]|foo} ;
     r_input = OK{foo|module M = struct end [@alg_foo] [@@item_bar];|foo} ;
     o_output = OK {foo|module M = struct  end[@alg_foo][@@item_bar];;
|foo} ;
     official_output = OK {foo|module M = ((struct  end)[@alg_foo ])[@@item_bar ]|foo} ;
     r_output = OK {foo|module M = struct  end[@alg_foo][@@item_bar];
|foo}
    };
    {name="module-expr-item-attributes2"; implem = True ;
     o_input = OK{foo|module M = N [@alg_foo] [@@item_bar]|foo} ;
     official_input = OK{foo|module M = N [@alg_foo] [@@item_bar]|foo} ;
     r_input = OK{foo|module M = N [@alg_foo] [@@item_bar];|foo} ;
     o_output = OK {foo|module M = N[@alg_foo][@@item_bar];;
|foo} ;
     official_output = OK {foo|module M = ((N)[@alg_foo ])[@@item_bar ]|foo} ;
     r_output = OK {foo|module M = N[@alg_foo][@@item_bar];
|foo}
    };
    {name="method-class-sig-item-attributes1"; implem = True ;
     o_input = OK {foo|class type ct = object method m : int [@@argle] end |foo} ;
     official_input = OK {foo|class type ct = object method m : int [@@argle] end |foo} ;
     r_input = OK {foo|class type ct = object method m : int  [@@argle] ; end;|foo} ;
     o_output = OK {foo|class type ct = object method m : int[@@argle] end;;
|foo} ;
     official_output = OK {foo|class type ct = object method  m : int[@@argle ] end|foo} ;
     r_output = OK {foo|class type ct = object method m : int[@@argle]; end;
|foo}
    };
    {name="method-class-struct-item-attributes1"; implem = True ;
     o_input = OK {foo|class c = object method foo = 1 [@@argle] end |foo} ;
     official_input = OK {foo|class c = object method foo = 1 [@@argle] end |foo} ;
     r_input = OK {foo|class c = object method foo = 1[@@argle]; end; |foo} ;
     o_output = OK {foo|class c = object method foo = 1[@@argle] end;;
|foo} ;
     official_output = OK {foo|class c = object method foo = 1[@@argle ] end|foo} ;
     r_output = OK {foo|class c = object method foo = 1[@@argle]; end;
|foo}
    };
    {name="class-decl-item-attributes1"; implem = True ;
     o_input = OK {foo|class c = object end [@@argle] |foo} ;
     official_input = OK {foo|class c = object end [@@argle] |foo} ;
     r_input = OK {foo|class c = object end [@@argle] ;|foo} ;
     o_output = OK {foo|class c = object  end[@@argle];;
|foo} ;
     official_output = OK {foo|class c = object  end[@@argle ]|foo} ;
     r_output = OK {foo|class c = object  end[@@argle];
|foo}
    };
    {name="let-binding-item-attributes1"; implem = True ;
     o_input = OK {foo|let x = 1 [@@argle] in 2|foo} ;
     official_input = OK {foo|let x = 1 [@@argle] in 2|foo} ;
     r_input = OK {foo|let x = 1 [@@argle] in 2;|foo} ;
     o_output = OK {foo|let _ = let x = 1[@@argle] in 2;;
|foo};
     official_output = OK {foo|;;let x = 1[@@argle ] in 2|foo};
     r_output = OK {foo|let x = 1[@@argle] in
2;
|foo}
    };
    {name="let-binding-item-attributes2"; implem = True ;
     o_input = OK {foo|let [@argle] x = 1 in 2|foo} ;
     official_input = OK {foo|let [@argle] x = 1 in 2|foo} ;
     r_input = SKIP {foo|let [@argle] x = 1 in 2;|foo} "this isn't allowed in revised syntax (and won't be)";
     o_output = OK {foo|let _ = let x = 1[@@argle] in 2;;
|foo};
     official_output = OK {foo|;;let x = 1[@@argle ] in 2|foo};
     r_output = OK {foo|let x = 1[@@argle] in
2;
|foo}
    };
    {name="letop-binding-item-attributes1-FAILS"; implem = True ;
     o_input = EXN {foo|let|| x = 1 [@@argle] in 2|foo}
                   (Ploc.Exc Ploc.dummy (Stdlib.Stream.Error
                    "[andop_binding] expected after [letop_binding] (in [expr])")) ;
     official_input = EXN {foo|let|| x = 1 [@@argle] in 2|foo}
                   (Syntaxerr.Error (Syntaxerr.Other Location.none)) ;
     r_input = EXN {foo|let|| x = 1 [@@argle] in 2;|foo}
                   (Ploc.Exc Ploc.dummy (Stdlib.Stream.Error
                    "[andop_binding] expected after [letop_binding] (in [expr])")) ;
     o_output = OK "should never get here";
     official_output = OK "should never get here";
     r_output = OK "should never get here"
    };
    {name="open-item-attributes1"; implem = True ;
     o_input = OK {foo|open Foo [@@argle]|foo} ;
     official_input = OK {foo|open Foo [@@argle]|foo} ;
     r_input = OK {foo|open Foo [@@argle];|foo} ;
     o_output = OK {foo|open Foo[@@argle];;
|foo};
     official_output = OK {foo|open Foo[@@argle ]|foo};
     r_output = OK {foo|open Foo[@@argle];
|foo}
    };
    {name="floating-attributes1"; implem = True ;
     o_input = OK {foo|[@@@argle]|foo} ;
     official_input = OK {foo|[@@@argle]|foo} ;
     r_input = OK {foo|[@@@argle];|foo} ;
     o_output = OK {foo|[@@@argle];;
|foo};
     official_output = OK {foo|[@@@argle ]|foo};
     r_output = OK {foo|[@@@argle];
|foo}
    };
    {name="floating-attributes2"; implem = False ;
     o_input = OK {foo|[@@@argle]|foo} ;
     official_input = OK {foo|[@@@argle]|foo} ;
     r_input = OK {foo|[@@@argle];|foo} ;
     o_output = OK {foo|[@@@argle];;
|foo};
     official_output = OK {foo|[@@@argle ]|foo};
     r_output = OK {foo|[@@@argle];
|foo}
    };
    {name="let-exception1"; implem = True ;
     o_input = OK {foo|let exception E [@algattr] in 1 [@@itemattr]|foo} ;
     official_input = OK {foo|let exception E[@algattr] in 1 [@@itemattr]|foo} ;
     r_input = OK {foo|let exception E[@algattr] in 1 [@@itemattr];|foo} ;
     o_output = OK {foo|let _ = let exception E[@algattr] in 1[@@itemattr];;
|foo};
     official_output = OK {foo|;;let exception E [@algattr ] in 1[@@itemattr ]|foo};
     r_output = OK {foo|let exception E[@algattr] in 1[@@itemattr];
|foo}
    };
    {name="let-exception2"; implem = True ;
     o_input = OK {foo|let exception E of (int [@algattr2])[@algattr] in 1 [@@itemattr]|foo} ;
     official_input = OK {foo|let exception E of (int [@algattr2])[@algattr] in 1 [@@itemattr]|foo} ;
     r_input = OK {foo|let exception E of (int [@algattr2])[@algattr] in 1 [@@itemattr];|foo} ;
     o_output = OK {foo|let _ = let exception E of (int[@algattr2])[@algattr] in 1[@@itemattr];;
|foo};
     official_output = OK {foo|;;let exception E of ((int)[@algattr2 ]) [@algattr ] in 1[@@itemattr ]|foo};
     r_output = OK {foo|let exception E of (int[@algattr2])[@algattr] in 1[@@itemattr];
|foo}
    };
    {name="pat-exception1"; implem = True ;
     o_input = OK {foo|match x with exception E -> 1|foo} ;
     official_input = OK {foo|match x with exception E -> 1|foo} ;
     r_input = OK {foo|match x with [ exception E -> 1 ];|foo} ;
     o_output = OK {foo|let _ = match x with exception E -> 1;;
|foo};
     official_output = OK {foo|;;match x with | exception E -> 1|foo};
     r_output = OK {foo|match x with [ exception E → 1 ];
|foo}
    };
    {name="pat-exception1"; implem = True ;
     o_input = OK {foo|match x with exception E.F -> 1|foo} ;
     official_input = OK {foo|match x with exception E.F -> 1|foo} ;
     r_input = OK {foo|match x with [ exception E.F -> 1 ];|foo} ;
     o_output = OK {foo|let _ = match x with exception E.F -> 1;;
|foo};
     official_output = OK {foo|;;match x with | exception E.F -> 1|foo};
     r_output = OK {foo|match x with [ exception E.F → 1 ];
|foo}
    };
    {name="pat-exception2"; implem = True ;
     o_input = OK {foo|match x with exception E.F _ -> 1|foo} ;
     official_input = OK {foo|match x with exception E.F _ -> 1|foo} ;
     r_input = OK {foo|match x with [ exception E.F _ -> 1 ];|foo} ;
     o_output = OK {foo|let _ = match x with exception E.F _ -> 1;;
|foo};
     official_output = OK {foo|;;match x with | exception E.F _ -> 1|foo};
     r_output = OK {foo|match x with [ exception E.F _ → 1 ];
|foo}
    };
    {name="unary-plus1"; implem = True ;
     o_input = OK {foo|+ 1|foo} ;
     official_input = OK {foo|+ 1|foo} ;
     r_input = OK {foo|+ 1;|foo} ;
     o_output = OK {foo|let _ = 1;;
|foo};
     official_output = OK {foo|;;1|foo} ;
     r_output = OK {foo|1;
|foo}
    };
    {name="unary-plus2"; implem = True ;
     o_input = OK {foo|+. 1.|foo} ;
     official_input = OK {foo|+. 1.|foo} ;
     r_input = OK {foo|+. 1.;|foo} ;
     o_output = OK {foo|let _ = 1.;;
|foo};
     official_output = OK {foo|;;1.|foo} ;
     r_output = OK {foo|1.;
|foo}
    };
    {name="unary-plus3"; implem = True ;
     o_input = OK {foo|+ x|foo} ;
     official_input = OK {foo|+ x|foo} ;
     r_input = OK {foo|+ x;|foo} ;
     o_output = OK {foo|let _ = +x;;
|foo};
     official_output = OK {foo|;;+ x|foo} ;
     r_output = OK {foo|+x;
|foo}
    };
    {name="unary-plus4"; implem = True ;
     o_input = OK {foo|+ + x|foo} ;
     official_input = OK {foo|+ + x|foo} ;
     r_input = OK {foo|+ +x;|foo} ;
     o_output = OK {foo|let _ = +(+x);;
|foo};
     official_output = OK {foo|;;+ (+ x)|foo} ;
     r_output = OK {foo|+(+x);
|foo}
    };
    {name="module-record1"; implem = True ;
     o_input = OK {foo|M.{a = b}|foo} ;
     official_input = OK {foo|M.{a = b}|foo} ;
     r_input = OK {foo|M.({a = b});|foo} ;
     o_output = OK {foo|let _ = M.({a = b});;
|foo};
     official_output = OK {foo|;;let open M in { a = b }|foo} ;
     r_output = OK {foo|M.({a = b});
|foo}
    };
    {name="module-record2"; implem = True ;
     o_input = OK {foo|M.N.{a = b}|foo} ;
     official_input = OK {foo|M.N.{a = b}|foo} ;
     r_input = OK {foo|M.N.({a = b});|foo} ;
     o_output = OK {foo|let _ = M.N.({a = b});;
|foo};
     official_output = OK {foo|;;let open M.N in { a = b }|foo} ;
     r_output = OK {foo|M.N.({a = b});
|foo}
    };
    {name="module-record3"; implem = True ;
     o_input = OK {foo|M.N.{e with a = b}|foo} ;
     official_input = OK {foo|M.N.{e with a = b}|foo} ;
     r_input = OK {foo|M.N.({(e) with a = b});|foo} ;
     o_output = OK {foo|let _ = M.N.({e with a = b});;
|foo};
     official_output = OK {foo|;;let open M.N in { e with a = b }|foo} ;
     r_output = OK {foo|M.N.({(e) with a = b});
|foo}
    };
    {name="module-alias1"; implem = False ;
     o_input = OK {foo|module T = A.B.C|foo} ;
     official_input = OK {foo|module T = A.B.C|foo} ;
     r_input = OK {foo|module alias T = A.B.C;|foo} ;
     o_output = OK {foo|module T = A.B.C;;
|foo};
     official_output = OK {foo|module T = A.B.C|foo} ;
     r_output = OK {foo|module alias T = A.B.C;
|foo}
    };
    {name="labeled-field-alg-attribute1"; implem = True ;
     o_input = OK {foo|type t = { a : int [@attr] ; }|foo} ;
     official_input = OK {foo|type t = { a : int [@attr] ; }|foo} ;
     r_input = OK {foo|type t = { a : int[@attr] };|foo} ;
     o_output = OK {foo|type t = { a : int[@attr] };;
|foo};
     official_output = OK {foo|type t = {
  a: int [@attr ]}|foo} ;
     r_output = OK {foo|type t = { a : int[@attr] };
|foo}
    };
    {name="labeled-field-alg-attribute2"; implem = True ;
     o_input = OK {foo|type t = { a : int [@attr] ; [@attr2] }|foo} ;
     official_input = OK {foo|type t = { a : int [@attr] ;  [@attr2]}|foo} ;
     r_input = OK {foo|type t = { a : int[@attr] [@attr2] };|foo} ;
     o_output = OK {foo|type t = { a : int[@attr] [@attr2] };;
|foo};
     official_output = OK {foo|type t = {
  a: int [@attr ][@attr2 ]}|foo} ;
     r_output = OK {foo|type t = { a : int[@attr] [@attr2] };
|foo}
    };
    {name="val-attributes1"; implem = False ;
     o_input = OK {foo|val x : int [@@attr2]|foo} ;
     official_input = OK {foo|val x : int [@@attr2]|foo} ;
     r_input = OK {foo|value x : int [@@attr2];|foo} ;
     o_output = OK {foo|val x : int[@@attr2];;
|foo};
     official_output = OK {foo|val x : int[@@attr2 ]|foo} ;
     r_output = OK {foo|value x : int[@@attr2];
|foo}
    };
    {name="val-attributes2"; implem = False ;
     o_input = OK {foo|val[@attr1] x : int [@@attr2]|foo} ;
     official_input = OK {foo|val[@attr1] x : int [@@attr2]|foo} ;
     r_input = OK {foo|value x : int [@@attr1][@@attr2];|foo} ;
     o_output = OK {foo|val x : int[@@attr1] [@@attr2];;
|foo};
     official_output = OK {foo|val x : int[@@attr1 ][@@attr2 ]|foo} ;
     r_output = OK {foo|value x : int[@@attr1] [@@attr2];
|foo}
    };
    {name="external-operator-sig-item"; implem = False ;
     o_input = OK {foo|external ( & ) : bool -> bool -> bool = "%sequand"
  [@@a "msg"]|foo} ;
     official_input = OK {foo|external ( & ) : bool -> bool -> bool = "%sequand"
  [@@a "msg"]|foo} ;
     r_input = OK {foo|external ( & ) : bool -> bool -> bool = "%sequand"
  [@@a "msg";];|foo} ;
     o_output = OK {foo|external (&) : bool -> bool -> bool = "%sequand"[@@a "msg"];;
|foo};
     official_output = OK {foo|external (&) : bool -> bool -> bool = "%sequand"[@@a "msg"]|foo} ;
     r_output = OK {foo|external ( & ) : bool → bool → bool = "%sequand"[@@a "msg";];
|foo}
    };
    {name="external-operator-str-item"; implem = True ;
     o_input = OK {foo|external ( & ) : bool -> bool -> bool = "%sequand"
  [@@a "msg"]|foo} ;
     official_input = OK {foo|external ( & ) : bool -> bool -> bool = "%sequand"
  [@@a "msg"]|foo} ;
     r_input = OK {foo|external ( & ) : bool -> bool -> bool = "%sequand"
  [@@a "msg";];|foo} ;
     o_output = OK {foo|external (&) : bool -> bool -> bool = "%sequand"[@@a "msg"];;
|foo};
     official_output = OK {foo|external (&) : bool -> bool -> bool = "%sequand"[@@a "msg"]|foo} ;
     r_output = OK {foo|external ( & ) : bool → bool → bool = "%sequand"[@@a "msg";];
|foo}
    };
    {name="expr-1"; implem = True ;
     o_input = OK {foo|let () = (f [@inlined never]) ()|foo} ;
     official_input = OK {foo|let () = (f [@inlined never]) ()|foo} ;
     r_input = OK {foo|value () = (f[@inlined never;]) ();|foo} ;
     o_output = OK {foo|let () = (f[@inlined never]) ();;
|foo};
     official_output = OK {foo|let () = ((f)[@inlined never]) ()|foo} ;
     r_output = OK {foo|value () = (f[@inlined never;]) ();
|foo}
    };
    {name="anon-module-argumet"; implem = True ;
     o_input = OK {foo|let f (module _ : S) = ()|foo} ;
     official_input = OK {foo|let f (module _ : S) = ()|foo} ;
     r_input = OK {foo|value f (module _ : S) = ();|foo} ;
     o_output = OK {foo|let f (module _ : S) = ();;
|foo};
     official_output = OK {foo|let f ((module _)  : (module S)) = ()|foo} ;
     r_output = OK {foo|value f (module _ : S) = ();
|foo}
    };
    {name="named-module-argumet"; implem = True ;
     o_input = OK {foo|let f (module M : S) = ()|foo} ;
     official_input = OK {foo|let f (module M : S) = ()|foo} ;
     r_input = OK {foo|value f (module M : S) = ();|foo} ;
     o_output = OK {foo|let f (module M : S) = ();;
|foo};
     official_output = OK {foo|let f ((module M)  : (module S)) = ()|foo} ;
     r_output = OK {foo|value f (module M : S) = ();
|foo}
    }
]
;

value fmt_string s = Printf.sprintf "<<%s>>" s ;

value i2test (pa_implem,pa_interf) (pp_implem, pp_interf) pa_official_opt inputf outputf i =
  i.name >:: (fun _ ->
    let official_reparse0 implem s = match (implem,pa_official_opt) with [
      (_,None) -> ()
    | (True,Some (f,_)) -> ignore(f s)
    | (False,Some (_,f)) -> ignore(f s)
    ] in
    let official_reparse implem s =
    try official_reparse0 implem s
    with exn -> do {
      Printf.fprintf stderr "Exception during reparse of <<%s>>:\n\t" s ;
      flush stderr ;
      Testutil.report_error exn ;
      raise exn
    } in

    match (i.implem, inputf i, outputf i) with [

      (_,TODO msg, _) ->
        todo msg   

    | (_,_,TODO msg) ->
        todo msg   

    | (_,SKIP _ _ , _) -> ()

    | (True, OK inputs, OK outputs) -> do {
        assert_equal ~{msg=Printf.sprintf "on input <<%s>>" inputs} ~{printer=fmt_string}
          outputs (wrap_err pp_implem (wrap_err pa_implem inputs)) ;
          official_reparse True outputs
      }

    | (False, OK inputs, OK outputs) -> do {
        assert_equal ~{msg=Printf.sprintf "on input <<%s>>" inputs} ~{printer=fmt_string}
          outputs (wrap_err pp_interf (wrap_err pa_interf inputs)) ;
          official_reparse False outputs
      }

    | (True,EXN inputs exn, _) ->
        assert_raises_exn_pred ~{msg=i.name} (smart_exn_eq exn)
          (fun () -> pa_implem inputs)

    | (False,EXN inputs exn, _) ->
        assert_raises_exn_pred ~{msg=i.name} (smart_exn_eq exn)
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

value r2r pa pp opa () = List.map (i2test pa pp opa r_input r_output ) test_matrix ;
value r2o pa pp opa () = List.map (i2test pa pp opa r_input o_output ) test_matrix ;
value o2r pa pp opa () = List.map (i2test pa pp opa o_input r_output ) test_matrix ;
value o2o pa pp opa () = List.map (i2test pa pp opa o_input o_output ) test_matrix ;
value o2official pa pp opa () = List.map (i2test pa pp opa o_input official_output ) test_matrix ;
value official2official pa pp opa () = List.map (i2test pa pp opa official_input official_output ) test_matrix ;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
