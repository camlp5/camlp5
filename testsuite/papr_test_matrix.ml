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
  implem : bool ;
  r_input : (string * option exn);
  o_input : (string * option exn) ;
  r_output : option (string * option exn) ;
  o_output : option (string * option exn) ;
  official_output : option (string * option exn)
}
;

value test_matrix = [
    {name="simplest"; implem = True ;
     o_input = ("(1; 2);; 3 ;; let x = 1 ;;", None) ;
     o_output = Some ({foo|let _ = 1; 2;;
let _ = 3;;
let x = 1;;
|foo}, None) ;
     official_output = None ;
     r_output = Some ({foo|do { 1; 2 };
3;
value x = 1;
|foo}, None) ;
     r_input = ("do { 1; 2}; 3 ; value x = 1 ;", None)
    };
    {name="infix1"; implem = True ;
     o_input = ("(a + b) c;;", None) ;
     o_output = Some ({foo|let _ = (a + b) c;;
|foo}, None) ;
     official_output = Some ({foo|;;(+) a b c|foo}, None) ;
     r_output = Some ({foo|(a + b) c;
|foo}, None) ;
     r_input = ("(a + b) c;", None)
    };
    {name="infix2"; implem = True ;
     o_input = ("(a --> b) c;;", None) ;
     o_output = Some ({foo|let _ = (a --> b) c;;
|foo}, None) ;
     official_output = Some ({foo|;;(-->) a b c|foo}, None) ;
     r_output = Some ({foo|(a --> b) c;
|foo}, None) ;
     r_input = ("(a --> b) c;", None)
    };
    {name="prefix1"; implem = True ;
     o_input = ("(!!!a) c;;", None) ;
     o_output = Some ({foo|let _ = !!!a c;;
|foo}, None) ;
     official_output = Some ({foo|;;(!!!) a c|foo}, None) ;
     r_output = Some ({foo|!!!a c;
|foo}, None) ;
     r_input = ("(!!!a) c;", None)
    };
    (* original syntax accepts "$" as an infix symbol; revised syntax DOES NOT *)
    {name="dollar"; implem = True ;
     o_input = ("a $ c;;", None) ;
     o_output = Some ({foo|let _ = a $ c;;
|foo}, None) ;
     official_output = Some ({foo|;;a $ c|foo}, None) ;
     r_output = Some ({foo|\$  a c;
|foo}, None) ;
     r_input = ("a $ c;", Some (Ploc.Exc Ploc.dummy (Stream.Error "';' expected after [str_item] (in [str_item_semi])")))
    };
    {name="alg_attribute1"; implem = True ;
     o_input = ("a[@foo];;", None) ;
     o_output = Some ({foo|let _ = a[@foo];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ])|foo}, None) ;
     r_output = Some ({foo|a[@foo];
|foo}, None) ;
     r_input = ("a [@foo];", None)
    };
    {name="alg_attribute2"; implem = True ;
     o_input = ("a + b[@foo];;", None) ;
     o_output = Some ({foo|let _ = a + b[@foo];;
|foo}, None) ;
     official_output = Some ({foo|;;((a + b)[@foo ])|foo}, None) ;
     r_output = Some ({foo|a + b[@foo];
|foo}, None) ;
     r_input = ("a + b [@foo];", None)
    };
    {name="alg_attribute3"; implem = True ;
     o_input = ("(a [@foo])[@bar];;", None) ;
     o_output = Some ({foo|let _ = a[@foo][@bar];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ][@bar ])|foo}, None) ;
     r_output = Some ({foo|a[@foo][@bar];
|foo}, None) ;
     r_input = ("a[@foo][@bar];", None)
    };
    {name="alg_attribute4"; implem = True ;
     o_input = ("a [@foo :type t = int];;", None) ;
     o_output = Some ({foo|let _ = a[@foo: type t = int;;];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo :type t = int])|foo}, None) ;
     r_output = Some ({foo|a[@foo: type t = int;];
|foo}, None) ;
     r_input = ("a[@foo :type t = int;];", None)
    };
    {name="alg_attribute5"; implem = True ;
     o_input = ("a [@foo :int];;", None) ;
     o_output = Some ({foo|let _ = a[@foo: int];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo :int])|foo}, None) ;
     r_output = Some ({foo|a[@foo: int];
|foo}, None) ;
     r_input = ("a[@foo :int];", None)
    };
    {name="alg_attribute6"; implem = True ;
     o_input = ("a [@foo ? (_,_)];;", None) ;
     o_output = Some ({foo|let _ = a[@foo? _, _];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ?(_, _)])|foo}, None) ;
     r_output = Some ({foo|a[@foo? (_, _)];
|foo}, None) ;
     r_input = ("a[@foo ? (_,_)];", None)
    };
    {name="alg_attribute7"; implem = True ;
     o_input = ("a [@foo ? (_,_) when true];;", None) ;
     o_output = Some ({foo|let _ = a[@foo? _, _ when true];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ?(_, _) when true])|foo}, None) ;
     r_output = Some ({foo|a[@foo? (_, _) when True];
|foo}, None) ;
     r_input = ("a[@foo ? (_,_) when True];", None)
    };
    {name="alg_attribute8"; implem = True ;
     o_input = ("a [@foo ? _,_ when true];;", None) ;
     o_output = Some ({foo|let _ = a[@foo? _, _ when true];;
|foo}, None) ;
     official_output = Some ({foo|;;((a)[@foo ?(_, _) when true])|foo}, None) ;
     r_output = None ;
     r_input = ("a[@foo ? (_,_) when True];", None)
    };
    {name="alg_attribute9"; implem = True ;
     o_input = ("type t = int [@foo]", None) ;
     o_output = Some ({foo|type t = int[@foo];;
|foo}, None) ;
     official_output = Some ({foo|type t = ((int)[@foo ])|foo}, None) ;
     r_output = Some ({foo|type t = int[@foo];
|foo}, None) ;
     r_input = ("type t = int [@foo];", None)
    };
    {name="alg_attribute10"; implem = True ;
     o_input = ("type t = int [@foo][@bar]", None) ;
     o_output = Some ({foo|type t = int[@foo][@bar];;
|foo}, None) ;
     official_output = Some ({foo|type t = ((int)[@foo ][@bar ])|foo}, None) ;
     r_output = Some ({foo|type t = int[@foo][@bar];
|foo}, None) ;
     r_input = ("type t = int [@foo][@bar];", None)
    };
    {name="alg_attribute11"; implem = True ;
     o_input = ("function x|y[@foo] -> 1", None) ;
     o_output = Some ({foo|let _ =
  function
    x | y[@foo] -> 1;;
|foo}, None) ;
     official_output = Some ({foo|;;fun (x|((y)[@foo ])) -> 1|foo}, None) ;
     r_output = Some ({foo|fun
[ x | y[@foo] → 1 ];
|foo}, None) ;
     r_input = ("fun [ (x|y[@foo]) -> 1 ];", None)
    };
    {name="alg_attribute12"; implem = True ;
     o_input = ("module M = struct end [@foo]", None) ;
     o_output = Some ({foo|module M = struct  end[@foo];;
|foo}, None) ;
     official_output = Some ({foo|module M = ((struct  end)[@foo ])|foo}, None) ;
     r_output = Some ({foo|module M = struct  end[@foo];
|foo}, None) ;
     r_input = ("module M = struct end [@foo];", None)
    };
    {name="alg_attribute13"; implem = True ;
     o_input = ("class t = object end [@foo]", None) ;
     o_output = Some ({foo|class t = object  end[@foo];;
|foo}, None) ;
     official_output = Some ({foo|class t = ((object  end)[@foo ])|foo}, None) ;
     r_output = Some ({foo|class t = object  end[@foo];
|foo}, None) ;
     r_input = ("class t = object end [@foo];", None)
    };
    {name="alg_attribute13"; implem = True ;
     o_input = ("class type ['a ] t = object end [@foo]", None) ;
     o_output = Some ({foo|class type ['a] t = object  end[@foo];;
|foo}, None) ;
     official_output = Some ({foo|class type ['a] t = object  end[@foo ]|foo}, None) ;
     r_output = Some ({foo|class type t ['a] = object  end[@foo];
|foo}, None) ;
     r_input = ("class type t ['a] = object end [@foo];", None)
    };
    {name="alg_attribute14"; implem = True ;
     o_input = ("type t = { a : int [@foo] }", None) ;
     o_output = Some ({foo|type t = { a : int[@foo] };;
|foo}, None) ;
     official_output = Some ({foo|type t = {
  a: int [@foo ]}|foo}, None) ;
     r_output = Some ({foo|type t = { a : int[@foo] };
|foo}, None) ;
     r_input = ("type t = { a : int [@foo] };", None)
    };
    {name="alg_attribute15"; implem = True ;
     o_input = ("type t = { a : (int [@bar]) [@foo] }", None) ;
     o_output = Some ({foo|type t = { a : (int[@bar])[@foo] };;
|foo}, None) ;
     official_output = Some ({foo|type t = {
  a: (int [@bar ]) [@foo ] }|foo}, None) ;
     r_output = Some ({foo|type t = { a : (int[@bar])[@foo] };
|foo}, None) ;
     r_input = ("type t = { a : (int [@bar]) [@foo] };", None)
    };
    {name="alg_attribute16"; implem = True ;
     o_input = ("type t = a * (b[@bar])", None) ;
     r_input = ("type t = (a * b[@bar]);", None) ;
     o_output = Some ({foo|type t = a * (b[@bar]);;
|foo}, None) ;
     official_output = Some ({foo|type t = (a * ((b)[@bar ]))|foo}, None) ;
     r_output = Some ({foo|type t = (a * b[@bar]);
|foo}, None)
    };
    {name="alg_attribute17"; implem = True ;
     o_input = ("type t = a * b[@bar]", None) ;
     r_input = ("type t = (a * b)[@bar];", None) ;
     o_output = Some ({foo|type t = a * b[@bar];;
|foo}, None) ;
     official_output = Some ({foo|type t = (((a * b))[@bar ])|foo}, None) ;
     r_output = Some ({foo|type t = (a * b)[@bar];
|foo}, None)
    };

    {name="alg_attribute19"; implem = True ;
     o_input = ("type t = { a : ((int * bool)[@bar]) [@foo] }", None) ;
     r_input = ("type t = { a : ((int * bool)[@bar]) [@foo] };", None) ;
     o_output = Some ({foo|type t = { a : (int * bool[@bar])[@foo] };;
|foo}, None) ;
     official_output = Some ({foo|type t = {
  a: (int * bool [@bar ]) [@foo ] }|foo}, None) ;
     r_output = Some ({foo|type t = { a : ((int * bool)[@bar])[@foo] };
|foo}, None)
    };

    {name="simple-interf"; implem = False ;
     o_input = ("val x : int", None) ;
     o_output = Some ({foo|val x : int;;
|foo}, None) ;
     official_output = Some ({foo|val x : int|foo}, None) ;
     r_output = Some ({foo|value x : int;
|foo}, None) ;
     r_input = ("value x : int;", None)
    };
    {name="item_attribute1"; implem = False ;
     o_input = ("val x : int [@@foo]", None) ;
     o_output = Some ({foo|val x : int[@@foo];;
|foo}, None) ;
     official_output = Some ({foo|val x : int[@@foo ]|foo}, None) ;
     r_output = Some ({foo|value x : int[@@foo];
|foo}, None) ;
     r_input = ("value x : int[@@foo];", None)
    };
    {name="item_attribute2"; implem = True ;
     o_input = ("1 [@@foo]", None) ;
     o_output = Some ({foo|let _ = 1[@@foo];;
|foo}, None) ;
     official_output = Some ({foo|;;1[@@foo ]|foo}, None) ;
     r_output = Some ({foo|1[@@foo];
|foo}, None) ;
     r_input = ("do { 1 } [@@foo];", None)
    };
    {name="item_attribute3"; implem = True ;
     o_input = ("type nonrec t1 = int [@@bar] and t2 = bool [@@foo]", None) ;
     o_output = Some ({foo|type nonrec t1 = int[@@bar]
and t2 = bool[@@foo];;
|foo}, None) ;
     official_output = Some ({foo|type nonrec t1 = int[@@bar ]
and t2 = bool[@@foo ]|foo}, None) ;
     r_output = Some ({foo|type nonrec t1 = int[@@bar]
and t2 = bool[@@foo];
|foo}, None) ;
     r_input = ("type nonrec t1 = int [@@bar] and t2 = bool [@@foo];", None)
    };
    {name="exception-decl-attributes1"; implem = True ;
     o_input = ("exception Foo of int [@@foo]", None) ;
     o_output = Some ({foo|exception Foo of int[@@foo];;
|foo}, None) ;
     official_output = Some ({foo|exception Foo of int [@@foo ]|foo}, None) ;
     r_output = Some ({foo|exception Foo of int[@@foo];
|foo}, None) ;
     r_input = ("exception Foo of int [@@foo];", None)
    };
    {name="exception-decl-attributes2"; implem = True ;
     o_input = ("exception T of (int [@alg_foo]) [@alg_bar] [@@item_bar]", None) ;
     r_input = ("exception T of (int [@alg_foo]) [@alg_bar] [@@item_bar] ;", None) ;
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

      (True,(inputs, None), None) ->
        ignore(pa_implem inputs)

    | (False,(inputs, None), None) ->
        ignore(pa_interf inputs)

    | (True,(inputs, None), Some (outputs, None)) ->
        assert_equal ~{printer=fmt_string}
          outputs (wrap_err pp_implem (wrap_err pa_implem inputs))

    | (False,(inputs, None), Some (outputs, None)) ->
        assert_equal ~{printer=fmt_string}
          outputs (wrap_err pp_interf (wrap_err pa_interf inputs))

    | (True,(inputs, Some exn), _) ->
        assert_raises_exn_pred ~{msg=i.name} ~{exnmsg="msg"} (smart_exn_eq exn)
          (fun () -> pa_implem inputs)

    | (False,(inputs, Some exn), _) ->
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

value r2r pa pp () = List.map (i2test pa pp r_input r_output ) test_matrix ;
value r2o pa pp () = List.map (i2test pa pp r_input o_output ) test_matrix ;
value o2r pa pp () = List.map (i2test pa pp o_input r_output ) test_matrix ;
value o2o pa pp () = List.map (i2test pa pp o_input o_output ) test_matrix ;
value o2official pa pp () = List.map (i2test pa pp o_input official_output ) test_matrix ;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
