(* camlp5r *)
(* asttools.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "q_MLast.cmo";

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

value expr_left_assoc_acc e =
  let rec arec = fun [
    <:expr:< $e1$ . ( $e2$  . $e3$ ) >> ->
      arec <:expr< ( $e1$ . $e2$ ) . $e3$ >>
  | e -> e
  ] in arec e
;
