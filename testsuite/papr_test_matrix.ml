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
  exclude : list string ;
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
     exclude=[];
     o_input = OK {foo||foo} ;
     official_input = OK {foo||foo} ;
     r_input = OK {foo||foo} ;
     o_output = OK {foo||foo};
     official_output = OK {foo||foo} ;
     r_output = OK {foo||foo}
    };
    {name="simplest"; implem = True ;
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
    {name="item_attribute4"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t [@@a]|foo} ;
     official_input = OK {foo|type t [@@a]|foo} ;
     r_input = OK {foo|type t = 'a [@@a];|foo} ;
     o_output = OK {foo|type t[@@a];;
|foo};
     official_output = OK {foo|type t[@@a ]|foo} ;
     r_output = OK {foo|type t = α[@@a];
|foo}
    };
    {name="exception-decl-attributes1"; implem = True ;
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=["r2official"];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
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
     exclude=[];
     o_input = OK {foo|let f (module M : S) = ()|foo} ;
     official_input = OK {foo|let f (module M : S) = ()|foo} ;
     r_input = OK {foo|value f (module M : S) = ();|foo} ;
     o_output = OK {foo|let f (module M : S) = ();;
|foo};
     official_output = OK {foo|let f ((module M)  : (module S)) = ()|foo} ;
     r_output = OK {foo|value f (module M : S) = ();
|foo}
    };
    {name="abstract-module-type-str-item"; implem = True ;
     exclude=[];
     o_input = OK {foo|module type S|foo} ;
     official_input = OK {foo|module type S|foo} ;
     r_input = OK {foo|module type S;|foo} ;
     o_output = OK {foo|module type S;;
|foo};
     official_output = OK {foo|module type S|foo} ;
     r_output = OK {foo|module type S;
|foo}
    };
    {name="alg-extension-ctyp"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t = int * [%a]|foo} ;
     official_input = OK {foo|type t = int * [%a]|foo} ;
     r_input = OK {foo|type t = (int * [%a]);|foo} ;
     o_output = OK {foo|type t = int * [%a];;
|foo};
     official_output = OK {foo|type t = (int * [%a ])|foo} ;
     r_output = OK {foo|type t = (int * [%a]);
|foo}
    };
    {name="alg-extension-patt"; implem = True ;
     exclude=[];
     o_input = OK {foo|match x with (x, [%a]) -> 1|foo} ;
     official_input = OK {foo|match x with (x, [%a]) -> 1|foo} ;
     r_input = OK {foo|match x with [ (x, [%a]) -> 1 ];|foo} ;
     o_output = OK {foo|let _ = match x with x, [%a] -> 1;;
|foo};
     official_output = OK {foo|;;match x with | (x, [%a ]) -> 1|foo} ;
     r_output = OK {foo|match x with [ (x, [%a]) → 1 ];
|foo}
    };
    {name="alg-extension-expr"; implem = True ;
     exclude=[];
     o_input = OK {foo|let x = 1 + [%a]|foo} ;
     official_input = OK {foo|let x = 1 + [%a]|foo} ;
     r_input = OK {foo|value x = 1 + [%a];|foo} ;
     o_output = OK {foo|let x = 1 + [%a];;
|foo};
     official_output = OK {foo|let x = 1 + ([%a ])|foo} ;
     r_output = OK {foo|value x = 1 + [%a];
|foo}
    };
    {name="alg-extension-module-type"; implem = True ;
     exclude=[];
     o_input = OK {foo|module type S = sig module M : [%a] end|foo} ;
     official_input = OK {foo|module type S = sig module M : [%a] end|foo} ;
     r_input = OK {foo|module type S = sig module M : [%a]; end;|foo} ;
     o_output = OK {foo|module type S = sig module M : [%a] end;;
|foo};
     official_output = OK {foo|module type S  = sig module M : [%a ] end|foo} ;
     r_output = OK {foo|module type S = sig module M : [%a]; end;
|foo}
    };
    {name="alg-extension-sig-item"; implem = True ;
     exclude=[];
     o_input = OK {foo|module type S = sig [%%a] type t end|foo} ;
     official_input = OK {foo|module type S = sig [%%a] type t end|foo} ;
     r_input = OK {foo|module type S = sig [%%a]; type t = 'a; end;|foo} ;
     o_output = OK {foo|module type S = sig [%%a] type t end;;
|foo};
     official_output = OK {foo|module type S  = sig [%%a ] type t end|foo} ;
     r_output = OK {foo|module type S = sig [%%a]; type t = α; end;
|foo}
    };
    {name="alg-extension-module-expr"; implem = True ;
     exclude=[];
     o_input = OK {foo|module M = F([%a])|foo} ;
     official_input = OK {foo|module M = F([%a])|foo} ;
     r_input = OK {foo|module M = F([%a]);|foo} ;
     o_output = OK {foo|module M = F ([%a]);;
|foo};
     official_output = OK {foo|module M = (F)([%a ])|foo} ;
     r_output = OK {foo|module M = F [%a];
|foo}
    };
    {name="alg-extension-str-item"; implem = True ;
     exclude=[];
     o_input = OK {foo|module S = struct [%%a] type t end|foo} ;
     official_input = OK {foo|module S = struct [%%a] type t end|foo} ;
     r_input = OK {foo|module S = struct [%%a]; type t = 'a; end;|foo} ;
     o_output = OK {foo|module S = struct [%%a] type t end;;
|foo};
     official_output = OK {foo|module S = struct [%%a ]
                  type t end|foo} ;
     r_output = OK {foo|module S = struct [%%a]; type t = α; end;
|foo}
    };
    {name="alg-extension-class-sig-item"; implem = True ;
     exclude=[];
     o_input = OK {foo|class type ct = object val x : int [%%a] end|foo} ;
     official_input = OK {foo|class type ct = object val x : int [%%a] end|foo} ;
     r_input = OK {foo|class type ct = object value x : int; [%%a]; end;|foo} ;
     o_output = OK {foo|class type ct = object val x : int [%%a] end;;
|foo};
     official_output = OK {foo|class type ct = object val  x : int [%%a ] end|foo} ;
     r_output = OK {foo|class type ct = object value x : int; [%%a]; end;
|foo}
    };
    {name="alg-extension-class-str-item"; implem = True ;
     exclude=[];
     o_input = OK {foo|class ct = object val x = 1 [%%a] end|foo} ;
     official_input = OK {foo|class ct = object val x = 1 [%%a] end|foo} ;
     r_input = OK {foo|class ct = object value x = 1; [%%a]; end;|foo} ;
     o_output = OK {foo|class ct = object val x = 1 [%%a] end;;
|foo};
     official_output = OK {foo|class ct = object val x = 1 [%%a ] end|foo} ;
     r_output = OK {foo|class ct = object value x = 1; [%%a]; end;
|foo}
    };
    {name="alg-extension-class-expr"; implem = True ;
     exclude=[];
     o_input = OK {foo|class c = ([%a]) 1 |foo} ;
     official_input = OK {foo|class c = ([%a]) 1 |foo} ;
     r_input = OK {foo|class c = ([%a]) 1 ;|foo} ;
     o_output = OK {foo|class c = ([%a]) 1;;
|foo};
     official_output = OK {foo|class c = (([%a ]) 1)|foo} ;
     r_output = OK {foo|class c = ([%a]) 1;
|foo}
    };
    {name="alg-extension-class-str-item"; implem = True ;
     exclude=[];
     o_input = OK {foo|class type ct = object val x : int [%%a] end|foo} ;
     official_input = OK {foo|class type ct = object val x : int [%%a] end|foo} ;
     r_input = OK {foo|class type ct = object value x : int; [%%a]; end;|foo} ;
     o_output = OK {foo|class type ct = object val x : int [%%a] end;;
|foo};
     official_output = OK {foo|class type ct = object val  x : int [%%a ] end|foo} ;
     r_output = OK {foo|class type ct = object value x : int; [%%a]; end;
|foo}
    };
    {name="for-loop-index-var1"; implem = True ;
     exclude=[];
     o_input = OK {foo|for i = 1 to 10 do () done|foo} ;
     official_input = OK {foo|for i = 1 to 10 do () done|foo} ;
     r_input = OK {foo|for i = 1 to 10 do { () };|foo} ;
     o_output = OK {foo|let _ = for i = 1 to 10 do () done;;
|foo};
     official_output = OK {foo|;;for i = 1 to 10 do () done|foo} ;
     r_output = OK {foo|for i = 1 to 10 do { () };
|foo}
    };
    {name="for-loop-index-var2"; implem = True ;
     exclude=[];
     o_input = OK {foo|for (+) = 1 to 10 do () done|foo} ;
     official_input = OK {foo|for (+) = 1 to 10 do () done|foo} ;
     r_input = OK {foo|for (+) = 1 to 10 do { () };|foo} ;
     o_output = OK {foo|let _ = for (+) = 1 to 10 do () done;;
|foo};
     official_output = OK {foo|;;for (+) = 1 to 10 do () done|foo} ;
     r_output = OK {foo|for ( + ) = 1 to 10 do { () };
|foo}
    };
    {name="for-loop-index-var3"; implem = True ;
     exclude=[];
     o_input = OK {foo|for _ = 1 to 10 do () done|foo} ;
     official_input = OK {foo|for _ = 1 to 10 do () done|foo} ;
     r_input = OK {foo|for _ = 1 to 10 do { () };|foo} ;
     o_output = OK {foo|let _ = for _ = 1 to 10 do () done;;
|foo};
     official_output = OK {foo|;;for _ = 1 to 10 do () done|foo} ;
     r_output = OK {foo|for _ = 1 to 10 do { () };
|foo}
    };
    {name="record-label-patterns1"; implem = True ;
     exclude=[];
     o_input = OK {foo|let get_int { contents : int } = contents|foo} ;
     official_input = OK {foo|let get_int { contents : int } = contents|foo} ;
     r_input = OK {foo|value get_int { contents = (contents : int) } = contents;|foo} ;
     o_output = OK {foo|let get_int {contents = (contents : int)} = contents;;
|foo};
     official_output = OK {foo|let get_int { contents = (contents : int) } = contents|foo} ;
     r_output = OK {foo|value get_int {contents = (contents : int)} = contents;
|foo}
    };
    {name="record-label-patterns2"; implem = True ;
     exclude=[];
     o_input = OK {foo|let get_int { M.N.contents : int } = contents|foo} ;
     official_input = OK {foo|let get_int { M.N.contents : int } = contents|foo} ;
     r_input = OK {foo|value get_int { M.N.contents = (contents : int) } = contents;|foo} ;
     o_output = OK {foo|let get_int {M.N.contents = (contents : int)} = contents;;
|foo};
     official_output = OK {foo|let get_int { M.N.contents = (contents : int) } = contents|foo} ;
     r_output = OK {foo|value get_int {M.N.contents = (contents : int)} = contents;
|foo}
    };
    {name="record-label-patterns3"; implem = True ;
     exclude=[];
     o_input = OK {foo|let get_int { M.N.contents : int = c } = c|foo} ;
     official_input = OK {foo|let get_int { M.N.contents : int = c } = c|foo} ;
     r_input = OK {foo|value get_int { M.N.contents = (c : int) } = c;|foo} ;
     o_output = OK {foo|let get_int {M.N.contents = (c : int)} = c;;
|foo};
     official_output = OK {foo|let get_int { M.N.contents = (c : int) } = c|foo} ;
     r_output = OK {foo|value get_int {M.N.contents = (c : int)} = c;
|foo}
    };
    {name="record-label-expression1"; implem = True ;
     exclude=[];
     o_input = OK {foo|let set_int contents = { contents : int }|foo} ;
     official_input = OK {foo|let set_int contents = { contents : int }|foo} ;
     r_input = OK {foo|value set_int contents = { contents = (contents : int) };|foo} ;
     o_output = OK {foo|let set_int contents = {contents = (contents : int)};;
|foo};
     official_output = OK {foo|let set_int contents = { contents = (contents : int) }|foo} ;
     r_output = OK {foo|value set_int contents = {contents = (contents : int)};
|foo}
    };
    {name="record-label-expression2"; implem = True ;
     exclude=[];
     o_input = OK {foo|let set_int2 c = { contents : int = c }|foo} ;
     official_input = OK {foo|let set_int2 c = { contents : int = c }|foo} ;
     r_input = OK {foo|value set_int2 c = { contents = (c : int) };|foo} ;
     o_output = OK {foo|let set_int2 c = {contents = (c : int)};;
|foo};
     official_output = OK {foo|let set_int2 c = { contents = (c : int) }|foo} ;
     r_output = OK {foo|value set_int2 c = {contents = (c : int)};
|foo}
    };
    {name="module-expr-unpack-module1"; implem = True ;
     exclude=[];
     o_input = OK {foo|module M = F(val string)|foo} ;
     official_input = OK {foo|module M = F(val string)|foo} ;
     r_input = OK {foo|module M = F(value string);|foo} ;
     o_output = OK {foo|module M = F ((val string));;
|foo};
     official_output = OK {foo|module M = (F)((val string))|foo} ;
     r_output = OK {foo|module M = F (value string);
|foo}
    };
    {name="module-expr-unpack-module2"; implem = True ;
     exclude=[];
     o_input = OK {foo|module M = F(val string : MT)|foo} ;
     official_input = OK {foo|module M = F(val string : MT)|foo} ;
     r_input = OK {foo|module M = F(value string : MT);|foo} ;
     o_output = OK {foo|module M = F ((val string : MT));;
|foo};
     official_output = OK {foo|module M = (F)((val (string : (module MT))))|foo} ;
     r_output = OK {foo|module M = F (value string : MT);
|foo}
    };
    {name="module-expr-unpack-module3"; implem = True ;
     exclude=[];
     o_input = OK {foo|module M = F(val string : MT :> MT2)|foo} ;
     official_input = OK {foo|module M = F(val string : MT :> MT2)|foo} ;
     r_input = OK {foo|module M = F(value string : MT :> MT2);|foo} ;
     o_output = OK {foo|module M = F ((val string : MT :> MT2));;
|foo};
     official_output = OK {foo|module M = (F)((val (string : (module MT)  :> (module MT2))))|foo} ;
     r_output = OK {foo|module M = F (value string : MT :> MT2);
|foo}
    };
    {name="simplest-raw-strings-1"; implem = True ;
     exclude=[];
     o_input = OK {foo|{|argle|}|foo} ;
     official_input = OK {foo|{|argle|}|foo} ;
     r_input = EXN {foo|{|argle|}|foo}
                   (Ploc.Exc Ploc.dummy
                              (Stdlib.Stream.Error "'(' or [label_expr] expected after '{' (in [expr])"));
     o_output = OK {foo|let _ = "argle";;
|foo};
     official_output = SKIP "meh" "meh" ;
     r_output = OK {foo|"argle";
|foo}
    };
    {name="simplest-raw-strings-2"; implem = True ;
     exclude=[];
     o_input = OK {foo|{|argle|}|foo} ;
     official_input = SKIP "meh" "meh";
     r_input = SKIP "meh" "meh" ;
     o_output = SKIP "meh" "meh" ;
     official_output = OK {foo|;;"argle"|foo} ;
     r_output = SKIP "meh" "meh" 
    };
    {name="simplest-raw-strings-3"; implem = True ;
     exclude=[];
     o_input = SKIP "meh" "meh";
     official_input = OK {foo|{|argle|}|foo} ;
     r_input = SKIP "meh" "meh" ;
     o_output = SKIP "meh" "meh" ;
     official_output = OK {foo|;;{|argle|}|foo} ;
     r_output = SKIP "meh" "meh" 
    };
    {name="poly-type-1"; implem = True ;
     exclude=[];
     o_input = OK {foo|type tlist = { x: 'a. 'a list }|foo} ;
     official_input = OK {foo|type tlist = { x: 'a. 'a list }|foo} ;
     r_input = OK {foo|type tlist = { x : ! 'a . list 'a };|foo} ;
     o_output = OK {foo|type tlist = { x : 'a . 'a list };;
|foo};
     official_output = OK {foo|type tlist = {
  x: 'a . 'a list }|foo} ;
     r_output = OK {foo|type tlist = { x : ! α . list α };
|foo}
    };
    {name="unreachable-1"; implem = True ;
     exclude=[];
     o_input = OK {foo|match x with pat -> .|foo} ;
     official_input = OK {foo|match x with pat -> .|foo} ;
     r_input = OK {foo|match x with [ pat -> . ];|foo} ;
     o_output = OK {foo|let _ = match x with pat -> .;;
|foo};
     official_output = OK {foo|;;match x with | pat -> .|foo} ;
     r_output = OK {foo|match x with pat → .;
|foo}
    };
    {name="unreachable-2"; implem = True ;
     exclude=[];
     o_input = EXN {foo|.|foo} (Ploc.Exc Ploc.dummy (Stdlib.Stream.Error "illegal begin of implem")) ;
     official_input = EXN {foo|.|foo} (Syntaxerr.Error (Syntaxerr.Other Location.none)) ;
     r_input = OK {foo| . ;|foo} ;
     o_output = EXN "" (Ploc.Exc Ploc.dummy
                        (Failure "pr_expr of (PaUnr _) not allowed except at rhs of match-case"));
     official_output = EXN ""
       (Ploc.Exc Ploc.dummy
          (Failure "bad ast ExUnr (parses as '.'; cannot have an ExUnr except at the rhs of match-case)")) ;
     r_output = OK {foo|.;
|foo}
    };
    {name="inline-record-types1"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t = A of { a : int }|foo} ;
     official_input = OK {foo|type t = A of { a : int }|foo} ;
     r_input = OK {foo|type t = [ A of { a : int } ];|foo} ;
     o_output = OK {foo|type t =
    A of { a : int };;
|foo};
     official_output = OK {foo|type t =
  | A of {
  a: int } |foo} ;
     r_output = OK {foo|type t =
  [ A of { a : int } ];
|foo}
    };
    {name="inline-record-types2"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t = A of int * string | B of { a : int } | C of bool|foo} ;
     official_input = OK {foo|type t = A of int * string | B of { a : int } | C of bool|foo} ;
     r_input = OK {foo|type t = [ A of int and string | B of { a : int } | C of bool ];|foo} ;
     o_output = OK {foo|type t =
    A of int * string
  | B of { a : int }
  | C of bool;;
|foo};
     official_output = OK {foo|type t =
  | A of int * string 
  | B of {
  a: int } 
  | C of bool |foo} ;
     r_output = OK {foo|type t =
  [ A of int and string
  | B of { a : int }
  | C of bool ];
|foo}
    };
    {name="exception-record-type"; implem = True ;
     exclude=[];
     o_input = OK {foo|exception E of { a : int }|foo} ;
     official_input = OK {foo|exception E of { a : int }|foo} ;
     r_input = OK {foo|exception E of { a : int };|foo} ;
     o_output = OK {foo|exception E of { a : int };;
|foo};
     official_output = OK {foo|exception E of {
  a: int } |foo} ;
     r_output = OK {foo|exception E of { a : int };
|foo}
    };
    {name="exception-rebind1"; implem = True ;
     exclude=[];
     o_input = OK {foo|exception E = A.B|foo} ;
     official_input = OK {foo|exception E = A.B|foo} ;
     r_input = OK {foo|exception E = A.B;|foo} ;
     o_output = OK {foo|exception E = A.B;;
|foo};
     official_output = OK {foo|exception E = A.B|foo} ;
     r_output = OK {foo|exception E = A.B;
|foo}
    };
    {name="type-extension-str-item1"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t += A of int | B of { a : int }|foo} ;
     official_input = OK {foo|type t += A of int | B of { a : int }|foo} ;
     r_input = OK {foo|type t += [ A of int | B of { a : int } ];|foo} ;
     o_output = OK {foo|type t += A of int | B of { a : int };;
|foo};
     official_output = OK {foo|type t +=  
  | A of int 
  | B of {
  a: int } |foo} ;
     r_output = OK {foo|type t += [ A of int | B of { a : int } ];
|foo}
    };
    {name="type-extension-str-item2"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t = exn = ..|foo} ;
     official_input = OK {foo|type t = exn = ..|foo} ;
     r_input = OK {foo|type t = exn == ..;|foo} ;
     o_output = OK {foo|type t = exn = ..;;
|foo};
     official_output = OK {foo|type t = exn = ..|foo} ;
     r_output = OK {foo|type t = exn == ..;
|foo}
    };
    {name="type-extension-str-item3"; implem = True ;
     exclude=[];
     o_input = OK {foo|type M.t += A of int | B of { a : int }|foo} ;
     official_input = OK {foo|type M.t += A of int | B of { a : int }|foo} ;
     r_input = OK {foo|type M.t += [ A of int | B of { a : int } ];|foo} ;
     o_output = OK {foo|type M.t += A of int | B of { a : int };;
|foo};
     official_output = OK {foo|type M.t +=  
  | A of int 
  | B of {
  a: int } |foo} ;
     r_output = OK {foo|type M.t += [ A of int | B of { a : int } ];
|foo}
    };
    {name="type-extension-sig-item1"; implem = False ;
     exclude=[];
     o_input = OK {foo|type t += A of int | B of { a : int }|foo} ;
     official_input = OK {foo|type t += A of int | B of { a : int }|foo} ;
     r_input = OK {foo|type t += [ A of int | B of { a : int } ];|foo} ;
     o_output = OK {foo|type t += A of int | B of { a : int };;
|foo};
     official_output = OK {foo|type t +=  
  | A of int 
  | B of {
  a: int } |foo} ;
     r_output = OK {foo|type t += [ A of int | B of { a : int } ];
|foo}
    };
    {name="list-type-def1"; implem = True ;
     exclude=[];
     o_input = OK {foo|type 'a t = 'a list = [] | (::) of 'a * 'a list|foo} ;
     official_input = OK {foo|type 'a t = 'a list = [] | (::) of 'a * 'a list|foo} ;
     r_input = OK {foo|type t 'a = list 'a == [ [] | (::) of 'a and list 'a ];|foo} ;
     o_output = OK {foo|type 'a t =
  'a list =
      []
    | ( :: ) of 'a * 'a list;;
|foo};
     official_output = OK {foo|type 'a t = 'a list =
  | [] 
  | (::) of 'a * 'a list |foo} ;
     r_output = OK {foo|type t α =
  list α ==
    [ []
    | ( :: ) of α and list α ];
|foo}
    };
    {name="extend-types-with-reference1"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t += A = A.A | B = A.B|foo} ;
     official_input = OK {foo|type t += A = A.A | B = A.B|foo} ;
     r_input = OK {foo|type t += [ A = A.A | B = A.B ];|foo} ;
     o_output = OK {foo|type t += A = A.A | B = A.B;;
|foo};
     official_output = OK {foo|type t +=  
  | A = A.A
  | B = A.B|foo} ;
     r_output = OK {foo|type t += [ A = A.A | B = A.B ];
|foo}
    };
    {name="lowercase-module-type1"; implem = True ;
     exclude=[];
     o_input = OK {foo|module type S = sig module type t module M: t end|foo} ;
     official_input = OK {foo|module type S = sig module type t module M: t end|foo} ;
     r_input = OK {foo|module type S = sig module type t; module M: t; end;|foo} ;
     o_output = OK {foo|module type S = sig module type t module M : t end;;
|foo};
     official_output = OK {foo|module type S  = sig module type t module M : t end|foo} ;
     r_output = OK {foo|module type S = sig module type t; module M : t; end;
|foo}
    };
    {name="extended-module-path1"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t = A.B.D.t|foo} ;
     official_input = OK {foo|type t = A.B.D.t|foo} ;
     r_input = OK {foo|type t = A.B.D.t ;|foo} ;
     o_output = OK {foo|type t = A.B.D.t;;
|foo};
     official_output = OK {foo|type t = A.B.D.t|foo} ;
     r_output = OK {foo|type t = A.B.D.t;
|foo}
    };
    {name="extended-module-path2"; implem = True ;
     exclude=[];
     o_input = OK {foo|type t = A.B(C).D.t|foo} ;
     official_input = OK {foo|type t = A.B(C).D.t|foo} ;
     r_input = OK {foo|type t = A.B(C).D.t ;|foo} ;
     o_output = OK {foo|type t = A.B(C).D.t;;
|foo};
     official_output = OK {foo|type t = A.B(C).D.t|foo} ;
     r_output = OK {foo|type t = A.B(C).D.t;
|foo}
    };
    {name="module-type-longident1"; implem = True ;
     exclude=[];
     o_input = OK {foo|module type S = M.N.S|foo} ;
     official_input = OK {foo|module type S = M.N.S|foo} ;
     r_input = OK {foo|module type S = M.N.S;|foo} ;
     o_output = OK {foo|module type S = M.N.S;;
|foo};
     official_output = OK {foo|module type S  = M.N.S|foo} ;
     r_output = OK {foo|module type S = M.N.S;
|foo}
    };
    {name="module-type-longident2"; implem = True ;
     exclude=[];
     o_input = OK {foo|module type s = M.N.s|foo} ;
     official_input = OK {foo|module type s = M.N.s|foo} ;
     r_input = OK {foo|module type s = M.N.s;|foo} ;
     o_output = OK {foo|module type s = M.N.s;;
|foo};
     official_output = OK {foo|module type s  = M.N.s|foo} ;
     r_output = OK {foo|module type s = M.N.s;
|foo}
    };
    {name="module-type-longident3"; implem = True ;
     exclude=[];
     o_input = OK {foo|module type s = s|foo} ;
     official_input = OK {foo|module type s = s|foo} ;
     r_input = OK {foo|module type s = s;|foo} ;
     o_output = OK {foo|module type s = s;;
|foo};
     official_output = OK {foo|module type s  = s|foo} ;
     r_output = OK {foo|module type s = s;
|foo}
    };
    {name="module-type-longident4"; implem = True ;
     exclude=[];
     o_input = OK {foo|module type S = M.N(P).S|foo} ;
     official_input = OK {foo|module type S = M.N(P).S|foo} ;
     r_input = OK {foo|module type S = M.N(P).S;|foo} ;
     o_output = OK {foo|module type S = M.N(P).S;;
|foo};
     official_output = OK {foo|module type S  = M.N(P).S|foo} ;
     r_output = OK {foo|module type S = M.N(P).S;
|foo}
    };
    {name="-type-constr-longident1"; implem = True ;
     exclude=[];
     o_input = OK {foo|type ('a, 'b) s = ('b, 'a) M.N(P).t|foo} ;
     official_input = OK {foo|type ('a, 'b) s = ('b, 'a) M.N(P).t|foo} ;
     r_input = OK {foo|type s 'a 'b = M.N(P).t 'b 'a;|foo} ;
     o_output = OK {foo|type ('a, 'b) s = ('b, 'a) M.N(P).t;;
|foo};
     official_output = OK {foo|type ('a, 'b) s = ('b, 'a) M.N(P).t|foo} ;
     r_output = OK {foo|type s α β = M.N(P).t β α;
|foo}
    };
    {name="sig-open1"; implem = False ;
     exclude=[];
     o_input = OK {foo|open A.B(C)|foo} ;
     official_input = OK {foo|open A.B(C)|foo} ;
     r_input = OK {foo|open A.B(C);|foo} ;
     o_output = OK {foo|open A.B(C);;
|foo};
     official_output = OK {foo|open A.B(C)|foo} ;
     r_output = OK {foo|open A.B(C);
|foo}
    };
    {name="sig-item-type-nonrec"; implem = False ;
     exclude=[];
     o_input = OK {foo|module type S = sig type nonrec t = t end|foo} ;
     official_input = OK {foo|module type S = sig type nonrec t = t end|foo} ;
     r_input = OK {foo|module type S = sig type nonrec t = t ; end;|foo} ;
     o_output = OK {foo|module type S = sig type nonrec t = t end;;
|foo};
     official_output = OK {foo|module type S  = sig type nonrec t = t end|foo} ;
     r_output = OK {foo|module type S = sig type nonrec t = t; end;
|foo}
    };
    {name="sig-item-type-rec"; implem = False ;
     exclude=[];
     o_input = OK {foo|module type S = sig type t = t end|foo} ;
     official_input = OK {foo|module type S = sig type t = t end|foo} ;
     r_input = OK {foo|module type S = sig type t = t ; end;|foo} ;
     o_output = OK {foo|module type S = sig type t = t end;;
|foo};
     official_output = OK {foo|module type S  = sig type t = t end|foo} ;
     r_output = OK {foo|module type S = sig type t = t; end;
|foo}
    };
    {name="printing-letop1"; implem = True ;
     exclude=[];
     o_input = OK {foo|let (let+) = 1|foo} ;
     official_input = OK {foo|let (let+) = 1|foo} ;
     r_input = OK {foo|value (let+) = 1;|foo} ;
     o_output = OK {foo|let (let+) = 1;;
|foo};
     official_output = OK {foo|let (let+) = 1|foo} ;
     r_output = OK {foo|value ( let+ ) = 1;
|foo}
    };
    {name="printing-letop2"; implem = True ;
     exclude=[];
     o_input = OK {foo|let (let+) f x = 1|foo} ;
     official_input = OK {foo|let (let+) f x = 1|foo} ;
     r_input = OK {foo|value (let+) f x = 1;|foo} ;
     o_output = OK {foo|let (let+) f x = 1;;
|foo};
     official_output = OK {foo|let (let+) f x = 1|foo} ;
     r_output = OK {foo|value ( let+ ) f x = 1;
|foo}
    };
    {name="printing-letop3"; implem = True ;
     exclude=[];
     o_input = OK {foo|let x = let (let+) f x = 1 in ()|foo} ;
     official_input = OK {foo|let x = let (let+) f x = 1 in ()|foo} ;
     r_input = OK {foo|value x = let (let+) f x = 1 in ();|foo} ;
     o_output = OK {foo|let x = let (let+) f x = 1 in ();;
|foo};
     official_output = OK {foo|let x = let (let+) f x = 1 in ()|foo} ;
     r_output = OK {foo|value x =
  let ( let+ ) f x = 1 in
  ();
|foo}
    }
]
;

value fmt_string s = Printf.sprintf "<<%s>>" s ;

value i2test ~{kind} (pa_implem,pa_interf) (pp_implem, pp_interf) pa_official_opt inputf outputf i =
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

    if List.mem kind i.exclude then () else
    match (i.implem, inputf i, outputf i) with [

      (_,TODO msg, _) ->
        todo msg   

    | (_,_,TODO msg) ->
        todo msg   

    | (_,SKIP _ _ , _) -> ()
    | (_,OK _, SKIP _ _ ) -> ()

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

    | (True, OK inputs, EXN outputs exn) -> do {
        let ast = wrap_err pa_implem inputs in
        assert_raises_exn_pred ~{msg=i.name} (smart_exn_eq exn)
          (fun () -> pp_implem ast)
      }

    | (False, OK inputs, EXN outputs exn) -> do {
        let ast = wrap_err pa_interf inputs in
        assert_raises_exn_pred ~{msg=i.name} (smart_exn_eq exn)
          (fun () -> pp_interf ast)
      }

    | (True,EXN inputs exn, _) ->
        assert_raises_exn_pred ~{msg=i.name} (smart_exn_eq exn)
          (fun () -> pa_implem inputs)

    | (False,EXN inputs exn, _) ->
        assert_raises_exn_pred ~{msg=i.name} (smart_exn_eq exn)
          (fun () -> pa_interf inputs)

    ])
;

value r_input i = i.r_input ;
value r_output i = i.r_output ;
value o_input i = i.o_input ;
value o_output i = i.o_output ;
value official_output i = i.official_output ;
value official_input i = i.official_input ;

value r2r pa pp opa () = List.map (i2test ~{kind="r2r"} pa pp opa r_input r_output ) test_matrix ;
value r2o pa pp opa () = List.map (i2test ~{kind="r2o"} pa pp opa r_input o_output ) test_matrix ;
value o2r pa pp opa () = List.map (i2test ~{kind="o2r"} pa pp opa o_input r_output ) test_matrix ;
value o2o pa pp opa () = List.map (i2test ~{kind="o2o"} pa pp opa o_input o_output ) test_matrix ;
value o2official pa pp opa () = List.map (i2test ~{kind="o2official"} pa pp opa o_input official_output ) test_matrix ;
value r2official pa pp opa () = List.map (i2test ~{kind="r2official"} pa pp opa r_input official_output ) test_matrix ;
value official2official pa pp opa () = List.map (i2test ~{kind="official2official"} pa pp opa official_input official_output ) test_matrix ;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
