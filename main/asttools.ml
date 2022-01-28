(* camlp5r *)
(* asttools.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "q_MLast.cmo";

value fst3 (a, b, c) = a ;
value snd3 (a, b, c) = b ;
value third3 (a, b, c) = c ;

value prefix_eq s0 s1 =
  let s0len = String.length s0 in
  s0len <= String.length s1 && s0 = (String.sub s1 0 s0len)
;

type choice 'a 'b =
  [ Left of 'a
  | Right of 'b ]
;

value isLeft = fun [ Left _ -> True | Right _ -> False ] ;
value isRight = fun [ Left _ -> False | Right _ -> True ] ;

value outLeft = fun [ Left x -> x | _ -> failwith "outLeft" ] ;
value outRight = fun [ Right x -> x | _ -> failwith "outRight" ] ;

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
  | MLast.LiXtr loc _ _ -> Ploc.raise loc (Failure "longid_concat: LiXtr forbidden here")
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
  | mt -> (mt, acc)
  ] in
  arec [] mt
;

value module_expr_unwrap_attrs mt =
  let rec arec acc = fun [
    <:module_expr< $mt$ [@ $_attribute:attr$ ] >> -> arec [ attr :: acc ] mt
  | mt -> (mt, acc)
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

value try_find f = 
 let rec try_find_f = fun [
     [] -> failwith "try_find"
   | [h::t] -> try f h with [ Failure _ -> try_find_f t ]
 ] in try_find_f
;

value longid_to_path_module_expr li =
  let rec lirec = fun [
    <:longident:< $uid:i$ >> -> <:module_expr< $uid:i$ >>
  | <:longident:< $longid:li$ . $uid:i$ >> -> <:module_expr< $lirec li$ . $uid:i$ >>
  | _ -> assert False
  ] in
  lirec li
;

value expr_to_path_module_expr e =
  let rec erec = fun [
    <:expr:< $longid:li$ >> -> longid_to_path_module_expr li
  | _ -> failwith "caught"
  ] in
  try Some (erec e) with Failure _ -> None
;

value expr_last_is_uid e =
  let rec erec = fun [
    <:expr< $longid:_$ >> -> True
  | _ -> False
  ]
  in erec e
;

value expr_first_is_id e =
  let rec erec = fun [
    <:expr< $longid:_$ >> -> True
  | <:expr< $exp:e$ . $lilongid:_$ >> -> erec e
  | _ -> False
  ]
  in erec e
;

value expr_is_module_path e =
 let rec erec = fun [
   <:expr< $longid:_$ >> -> True
 | _ -> False
 ] in erec e
;

value check_stream ?{avoid_tokens=[]} matchers strm =
  let avoid_tokens = [("EOI","") ; ("",";;") :: avoid_tokens] in
  let rec crec i = fun [
    [ (n,_) :: _ ] as ml when i < n ->
      let l = stream_npeek i strm in
      let last = fst (sep_last l) in
      if List.mem last avoid_tokens then raise Stream.Failure
      else crec (i+1) ml
  | [ (n, Left f) :: t ] ->
      match f (stream_npeek n strm) with [
        None -> crec i t
      | Some tok -> (n,tok)
     ]
  | [ (n, Right f) :: t ] ->
      if f (stream_npeek n strm) then
        raise Stream.Failure
      else crec i t
  | [] -> raise Stream.Failure
  ] in
  crec 1 matchers
;

type fsm 'a = { start : 'a ; accept : 'a ; fail : 'a ; delta : list ('a * (string * string) -> 'a) } ;
value check_fsm { start=start_st ; accept=accept_st ; fail=fail_st ; delta=delta } strm =
  let rec exec st n =
    let l = Stream.npeek n strm in
    if List.length l < n then False else
    let tok = fst (sep_last l) in
    let f = List.assoc st delta in
    try
      match f tok with [
          st' ->
          if st' = fail_st then False
          else if st' = accept_st then True
          else exec st' (n+1)
        ]
    with [ Failure _ -> False ]
  in
  exec start_st 1
;

value type_binder_delta = [
    ("START",fun [
                 ("","'") -> "QUO"
               | ("GIDENT",_) -> "IDS"
               | ("ANTIQUOT", s) when Some "list" = (s |> Plexer.parse_antiquot |> option_map fst) -> "PREDOT"
               | ("ANTIQUOT", s) when Some "_list" = (s |> Plexer.parse_antiquot |> option_map fst) -> "PREDOT"
               | ("ANTIQUOT_LOC", s) when Some "list" = (s |> Plexer.parse_antiloc |> option_map snd3) -> "PREDOT"
               | ("ANTIQUOT_LOC", s) when Some "_list" = (s |> Plexer.parse_antiloc |> option_map snd3) -> "PREDOT"
               | _ -> failwith "START"
    ])
   ;("PREDOT",fun [
               ("",".") -> "ACCEPT"
               | _ -> failwith "PREDOT"
    ])
   ;("IDS",fun [
               ("","'") -> "QUO"
             | ("GIDENT",_) -> "IDS"
             | ("",".") -> "ACCEPT"
               | _ -> failwith "IDS"
    ])
   ;("QUO",fun [
               ("LIDENT",_) -> "IDS"
             | ("UIDENT",_) -> "IDS"
               | _ -> failwith "QUO"
    ])
(*
   ;("ANTILIST",fun [
    ])
 *)
  ]
;
value type_binder_fsm = {start="START";accept="ACCEPT";fail="FAIL";delta=type_binder_delta} ;

value expr_wrap_attrs loc e l =
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:expr< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value expr_to_inline e ext attrs =
  let loc = MLast.loc_of_expr e in
  let e = expr_wrap_attrs loc e attrs in
  match ext with [ None -> e
  | Some attrid ->
   <:expr< [% $attrid:attrid$ $exp:e$ ; ] >>
  ]
;


value ctyp_wrap_attrs e l =
let loc = MLast.loc_of_ctyp e in
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:ctyp< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value ctyp_to_inline e ext attrs =
  let loc = MLast.loc_of_ctyp e in
  let e = ctyp_wrap_attrs e attrs in
  match ext with [ None -> e
  | Some attrid ->
   <:ctyp< [% $attrid:attrid$ : $type:e$ ] >>
  ]
;

value patt_wrap_attrs e l =
let loc = MLast.loc_of_patt e in
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:patt< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value patt_to_inline p ext attrs =
  let loc = MLast.loc_of_patt p in
  let p = patt_wrap_attrs p attrs in
  match ext with [ None -> p
  | Some attrid ->
   <:patt< [% $attrid:attrid$ ? $patt:p$ ] >>
  ]
;

value class_expr_wrap_attrs e l =
let loc = MLast.loc_of_class_expr e in
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:class_expr< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value class_type_wrap_attrs e l =
let loc = MLast.loc_of_class_type e in
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:class_type< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value module_type_wrap_attrs e l =
let loc = MLast.loc_of_module_type e in
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:module_type< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value module_expr_wrap_attrs e l =
let loc = MLast.loc_of_module_expr e in
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:module_expr< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value str_item_to_inline si ext =
let loc = MLast.loc_of_str_item si in
  match ext with [ None -> si
  | Some attrid ->
   <:str_item< [%% $attrid:attrid$ $stri:si$ ; ] >>
  ]
;

value sig_item_to_inline si ext =
let loc = MLast.loc_of_sig_item si in
  match ext with [ None -> si
  | Some attrid ->
   <:sig_item< [%% $attrid:attrid$ : $sigi:si$ ; ] >>
  ]
;

value longident_of_string_list loc = fun [
  [] -> failwith "longident_of_string_list"
| [h :: t] ->
  List.fold_left (fun li s -> <:extended_longident:< $longid:li$ . $uid:s$ >>) 
    <:extended_longident< $uid:h$ >> t
]
;
  
value string_list_of_longident li =
  let rec lirec = fun [
    <:longident< $uid:uid$ >> -> [uid]
  | <:longident< $longid:li$ . $uid:uid$ >> -> (lirec li) @ [uid]
  | <:extended_longident< $longid:_$ ( $longid:_$ ) >> ->
    failwith "string_list_of_longident: LiApp not allowed here"
  | _ ->
    failwith "[internal error] string_list_of_longident: called with invalid longid"
  ] in
  lirec li
;

value longident_lident_of_string_list loc = fun [
  [] -> assert False
| [h] -> (None, <:vala< h >>)
| l ->
  let (clsna, path) = sep_last l in
  let li = longident_of_string_list loc path in
  (Some <:vala< li >>, <:vala< clsna >>)
]
;

value string_list_of_longident_lident = fun [
  (None, <:vala< s >>) -> [s]
| (Some <:vala< li >>, <:vala<  s >>) -> (string_list_of_longident li)@[s]
| _ -> assert False
]
;

value is_uident s =
  match s.[0] with
  [ 'A'..'Z' → True
  | _ → False ]
;

value consume_longident loc l =
  let rec consrec acc = fun [
    [h :: t] when is_uident h -> consrec [h::acc] t
  | rest ->
    if acc = [] then (None, rest)
    else (Some (longident_of_string_list loc (List.rev acc)), rest)
  ] in
  consrec [] l
;

value consume_longident_lident loc l =
  match consume_longident loc l with [
    (None, [h :: t]) -> (Some (None, <:vala< h >>), t)
  | (Some li, [h :: t]) -> (Some (Some <:vala< li >>, <:vala< h >>), t)
  | (_, []) -> Ploc.raise loc (Failure "consume_longident_lident: no lident found")
  ]
;

value expr_of_string_list loc l =
  let rec exrec acc l =
    if l = [] then acc else
    match consume_longident_lident loc l with [
      (None, []) -> acc
    | (Some lili, rest) ->
      exrec <:expr< $acc$ . $lilongid:lili$ >> rest
    | _ -> assert False
    ] in
  match l with [
    [] -> Ploc.raise loc (Failure "expr_of_string_list: empty string list")

  | [h :: t] when not (is_uident h) ->
    exrec <:expr< $lid:h$ >> t

  | [h :: _] ->
    match consume_longident loc l with [
      (None, _) -> assert False
    | (Some li, rest) ->
      exrec <:expr< $longid:li$ >> rest
    ]
  ]
;

value rec expr_concat e1 e2 =
  let loc = MLast.loc_of_expr e1 in
  match (e1, e2) with [
    (<:expr< $longid:li1$ >>, <:expr< $longid:li2$ >>) -> <:expr< $longid:longid_concat li1 li2$ >>

  | (_, <:expr< $lid:id$ >>) -> <:expr< $e1$ . $lid:id$ >>

  | (_, <:expr< $e$ . $lilongid:lili$ >>) -> <:expr< $expr_concat e1 e$ . $lilongid:lili$ >>

  | _ -> Ploc.raise (MLast.loc_of_expr e1) (Failure "expr_concat: invalid arguments")

  ]
;
