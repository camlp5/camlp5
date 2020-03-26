(* camlp5r *)
(* asttools.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "q_MLast.cmo";

type choice 'a 'b =
  [ Left of 'a
  | Right of 'b ]
;

value option_map f x =
  match x with
  | Some x -> Some (f x)
  | None -> None
  end
;
value mustSome symbol = fun [
  Some x -> x
| None -> failwith ("Some: "^symbol)
]
;

value mustLeft symbol = fun [
  Left x -> x
| Right _ -> failwith ("choice: "^symbol)
]
;

value mustRight symbol = fun [
  Left _ -> failwith ("choice: "^symbol)
| Right x -> x
]
;

value stream_npeek n s = (Stream.npeek n s : list (string * string)) ;

value longid_concat li1 li2 =
  let rec crec = fun [
    <:extended_longident:< $longid:a$ . $_uid:b$ >> ->
      <:extended_longident< $longid:(crec a)$ . $_uid:b$ >>
  | <:extended_longident:< $longid:a$ ( $longid:b$ ) >> ->
      <:extended_longident< $longid:(crec a)$ ( $longid:b$ ) >>
  | <:extended_longident:< $_uid:b$ >> ->
      <:extended_longident< $longid:li1$ . $_uid:b$ >>
  ] in
  crec li2
;

value rec longid_last = fun [
  <:extended_longident< $uid:_$ >> as z -> z
| <:extended_longident:< $longid:_$ . $uid:uid$ >> -> <:extended_longident< $uid:uid$ >>
| _ -> failwith "longid_last"
]
;

value module_type_unwrap_attrs mt =
  let rec arec acc = fun [
    <:module_type< $mt$ [@ $_attribute:attr$ ] >> -> arec [ attr :: acc ] mt
  | mt -> (mt, List.rev acc)
  ] in
  arec [] mt
;

value rec sep_last = fun [
    [] -> failwith "sep_last"
  | [ hd ] -> (hd,[])
  | [ hd::tl ] ->
      let (l,tl) = sep_last tl in (l,[ hd::tl ])
  ]
;

value expr_to_path_module_expr e =
  let rec erec = fun [
    <:expr:< $uid:i$ >> -> <:module_expr< $uid:i$ >>
  | <:expr:< $a$ . $b$ >> -> <:module_expr< $erec a$ . $erec b$ >>
  | _ -> failwith "caught"
  ] in
  try Some (erec e) with Failure _ -> None
;

value expr_last_is_uid e =
  let rec erec = fun [
    <:expr< $uid:_$ >> -> True
  | <:expr< $_$ . $e$ >> -> erec e
  | _ -> False
  ]
  in erec e
;

value expr_first_is_id e =
  let rec erec = fun [
    <:expr< $uid:_$ >> -> True
  | <:expr< $lid:_$ >> -> True
  | <:expr< $e$ . $_$ >> -> erec e
  | _ -> False
  ]
  in erec e
;

value expr_is_module_path e =
 let rec erec = fun [
   <:expr< $uid:_$ >> -> True
 | <:expr< $a$ . $b$ >> -> erec a && erec b
 | _ -> False
 ] in erec e
;

value patt_is_module_path e =
 let rec erec = fun [
   <:patt< $uid:_$ >> -> True
 | <:patt< $a$ . $b$ >> -> erec a && erec b
 | _ -> False
 ] in erec e
;
 
value expr_left_assoc_acc e =
  let rec arec = fun [
    <:expr:< $e1$ . $e2$ >> as z ->
      match e2 with [
        <:expr< $e2$  . $e3$ >> -> arec <:expr< ( $e1$ . $e2$ ) . $e3$ >>
      | _ -> z ]
  | e -> e
  ] in arec e
;
 
value patt_left_assoc_acc e =
  let rec arec = fun [
    <:patt:< $e1$ . $e2$ >> as z ->
      match e2 with [
        <:patt< $e2$  . $e3$ >> -> arec <:patt< ( $e1$ . $e2$ ) . $e3$ >>
      | _ -> z ]
  | e -> e
  ] in arec e
;
