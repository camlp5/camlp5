(* camlp5r *)
(* asttools.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "q_MLast.cmo";

value longid_concat li1 li2 =
  let rec crec = fun [
    <:extended_longident:< $longid:a$ . $uid:b$ >> ->
      <:extended_longident< $longid:(crec a)$ . $uid:b$ >>
  | <:extended_longident:< $longid:a$ ( $longid:b$ ) >> ->
      <:extended_longident< $longid:(crec a)$ ( $longid:b$ ) >>
  | <:extended_longident:< $uid:b$ >> ->
      <:extended_longident< $longid:li1$ . $uid:b$ >>
  | _ -> failwith "longid_concat"
  ] in
  crec li2
;
