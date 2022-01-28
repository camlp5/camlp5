(* camlp5r *)
(* asttools.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "q_MLast.cmo" *)

let fst3 (a, b, c) = a;;
let snd3 (a, b, c) = b;;
let third3 (a, b, c) = c;;

let prefix_eq s0 s1 =
  let s0len = String.length s0 in
  s0len <= String.length s1 && s0 = String.sub s1 0 s0len
;;

type ('a, 'b) choice =
    Left of 'a
  | Right of 'b
;;

let isLeft =
  function
    Left _ -> true
  | Right _ -> false
;;
let isRight =
  function
    Left _ -> false
  | Right _ -> true
;;

let outLeft =
  function
    Left x -> x
  | _ -> failwith "outLeft"
;;
let outRight =
  function
    Right x -> x
  | _ -> failwith "outRight"
;;

let option_map f x =
  match x with
    Some x -> Some (f x)
  | None -> None
;;
let mustSome symbol =
  function
    Some x -> x
  | None -> failwith ("Some: " ^ symbol)
;;

let mustLeft symbol =
  function
    Left x -> x
  | Right _ -> failwith ("choice: " ^ symbol)
;;

let mustRight symbol =
  function
    Left _ -> failwith ("choice: " ^ symbol)
  | Right x -> x
;;

let stream_npeek n s : (string * string) list = Stream.npeek n s;;

let longid_concat li1 li2 =
  let rec crec =
    function
      MLast.LiAcc (loc, a, b) -> MLast.LiAcc (loc, crec a, b)
    | MLast.LiApp (loc, a, b) -> MLast.LiApp (loc, crec a, b)
    | MLast.LiUid (loc, b) -> MLast.LiAcc (loc, li1, b)
    | MLast.LiXtr (loc, _, _) ->
        Ploc.raise loc (Failure "longid_concat: LiXtr forbidden here")
  in
  crec li2
;;

let rec longid_last =
  function
    MLast.LiUid (_, _) as z -> z
  | MLast.LiAcc (loc, _, uid) -> MLast.LiUid (loc, uid)
  | _ -> failwith "longid_last"
;;

let module_type_unwrap_attrs mt =
  let rec arec acc =
    function
      MLast.MtAtt (_, mt, attr) -> arec (attr :: acc) mt
    | mt -> mt, acc
  in
  arec [] mt
;;

let module_expr_unwrap_attrs mt =
  let rec arec acc =
    function
      MLast.MeAtt (_, mt, attr) -> arec (attr :: acc) mt
    | mt -> mt, acc
  in
  arec [] mt
;;

let rec sep_last =
  function
    [] -> failwith "sep_last"
  | [hd] -> hd, []
  | hd :: tl -> let (l, tl) = sep_last tl in l, hd :: tl
;;

let try_find f =
  let rec try_find_f =
    function
      [] -> failwith "try_find"
    | h :: t -> try f h with Failure _ -> try_find_f t
  in
  try_find_f
;;

let longid_to_path_module_expr li =
  let rec lirec =
    function
      MLast.LiUid (loc, i) -> MLast.MeUid (loc, i)
    | MLast.LiAcc (loc, li, i) ->
        MLast.MeAcc (loc, lirec li, MLast.MeUid (loc, i))
    | _ -> assert false
  in
  lirec li
;;

let expr_to_path_module_expr e =
  let rec erec =
    function
      MLast.ExLong (loc, li) -> longid_to_path_module_expr li
    | _ -> failwith "caught"
  in
  try Some (erec e) with Failure _ -> None
;;

let expr_last_is_uid e =
  let rec erec =
    function
      MLast.ExLong (_, _) -> true
    | _ -> false
  in
  erec e
;;

let expr_first_is_id e =
  let rec erec =
    function
      MLast.ExLong (_, _) -> true
    | MLast.ExFle (_, e, _) -> erec e
    | _ -> false
  in
  erec e
;;

let expr_is_module_path e =
  let rec erec =
    function
      MLast.ExLong (_, _) -> true
    | _ -> false
  in
  erec e
;;

let check_stream ?(avoid_tokens = []) matchers strm =
  let avoid_tokens = ("EOI", "") :: ("", ";;") :: avoid_tokens in
  let rec crec i =
    function
      (n, _) :: _ as ml when i < n ->
        let l = stream_npeek i strm in
        let last = fst (sep_last l) in
        if List.mem last avoid_tokens then raise Stream.Failure
        else crec (i + 1) ml
    | (n, Left f) :: t ->
        begin match f (stream_npeek n strm) with
          None -> crec i t
        | Some tok -> n, tok
        end
    | (n, Right f) :: t ->
        if f (stream_npeek n strm) then raise Stream.Failure else crec i t
    | [] -> raise Stream.Failure
  in
  crec 1 matchers
;;

type 'a fsm =
  { start : 'a;
    accept : 'a;
    fail : 'a;
    delta : ('a * (string * string -> 'a)) list }
;;
let check_fsm
    {start = start_st; accept = accept_st; fail = fail_st; delta = delta}
    strm =
  let rec exec st n =
    let l = Stream.npeek n strm in
    if List.length l < n then false
    else
      let tok = fst (sep_last l) in
      let f = List.assoc st delta in
      try
        match f tok with
          st' ->
            if st' = fail_st then false
            else if st' = accept_st then true
            else exec st' (n + 1)
      with Failure _ -> false
  in
  exec start_st 1
;;

let type_binder_delta =
  ["START",
   (function
      "", "'" -> "QUO"
    | "GIDENT", _ -> "IDS"
    | "ANTIQUOT", s
      when Some "list" = ((s |> Plexer.parse_antiquot) |> option_map fst) ->
        "PREDOT"
    | "ANTIQUOT", s
      when Some "_list" = ((s |> Plexer.parse_antiquot) |> option_map fst) ->
        "PREDOT"
    | "ANTIQUOT_LOC", s
      when Some "list" = ((s |> Plexer.parse_antiloc) |> option_map snd3) ->
        "PREDOT"
    | "ANTIQUOT_LOC", s
      when Some "_list" = ((s |> Plexer.parse_antiloc) |> option_map snd3) ->
        "PREDOT"
    | _ -> failwith "START");
   "PREDOT",
   (function
      "", "." -> "ACCEPT"
    | _ -> failwith "PREDOT");
   "IDS",
   (function
      "", "'" -> "QUO"
    | "GIDENT", _ -> "IDS"
    | "", "." -> "ACCEPT"
    | _ -> failwith "IDS");
   "QUO",
   (function
      "LIDENT", _ -> "IDS"
    | "UIDENT", _ -> "IDS"
    | _ -> failwith "QUO")]
;;
let type_binder_fsm =
  {start = "START"; accept = "ACCEPT"; fail = "FAIL";
   delta = type_binder_delta}
;;

let expr_wrap_attrs loc e l =
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.ExAtt (loc, e, h)) t
  in
  wrec e l
;;

let expr_to_inline e ext attrs =
  let loc = MLast.loc_of_expr e in
  let e = expr_wrap_attrs loc e attrs in
  match ext with
    None -> e
  | Some attrid ->
      MLast.ExExten
        (loc, (attrid, MLast.StAttr (loc, [MLast.StExp (loc, e, [])])))
;;


let ctyp_wrap_attrs e l =
  let loc = MLast.loc_of_ctyp e in
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.TyAtt (loc, e, h)) t
  in
  wrec e l
;;

let ctyp_to_inline e ext attrs =
  let loc = MLast.loc_of_ctyp e in
  let e = ctyp_wrap_attrs e attrs in
  match ext with
    None -> e
  | Some attrid -> MLast.TyExten (loc, (attrid, MLast.TyAttr (loc, e)))
;;

let patt_wrap_attrs e l =
  let loc = MLast.loc_of_patt e in
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.PaAtt (loc, e, h)) t
  in
  wrec e l
;;

let patt_to_inline p ext attrs =
  let loc = MLast.loc_of_patt p in
  let p = patt_wrap_attrs p attrs in
  match ext with
    None -> p
  | Some attrid -> MLast.PaExten (loc, (attrid, MLast.PaAttr (loc, p, None)))
;;

let class_expr_wrap_attrs e l =
  let loc = MLast.loc_of_class_expr e in
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.CeAtt (loc, e, h)) t
  in
  wrec e l
;;

let class_type_wrap_attrs e l =
  let loc = MLast.loc_of_class_type e in
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.CtAtt (loc, e, h)) t
  in
  wrec e l
;;

let module_type_wrap_attrs e l =
  let loc = MLast.loc_of_module_type e in
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.MtAtt (loc, e, h)) t
  in
  wrec e l
;;

let module_expr_wrap_attrs e l =
  let loc = MLast.loc_of_module_expr e in
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.MeAtt (loc, e, h)) t
  in
  wrec e l
;;

let str_item_to_inline si ext =
  let loc = MLast.loc_of_str_item si in
  match ext with
    None -> si
  | Some attrid -> MLast.StExten (loc, (attrid, MLast.StAttr (loc, [si])), [])
;;

let sig_item_to_inline si ext =
  let loc = MLast.loc_of_sig_item si in
  match ext with
    None -> si
  | Some attrid -> MLast.SgExten (loc, (attrid, MLast.SiAttr (loc, [si])), [])
;;

let longident_of_string_list loc =
  function
    [] -> failwith "longident_of_string_list"
  | h :: t ->
      List.fold_left (fun li s -> MLast.LiAcc (loc, li, s))
        (MLast.LiUid (loc, h)) t
;;
  
let string_list_of_longident li =
  let rec lirec =
    function
      MLast.LiUid (_, uid) -> [uid]
    | MLast.LiAcc (_, li, uid) -> lirec li @ [uid]
    | MLast.LiApp (_, _, _) ->
        failwith "string_list_of_longident: LiApp not allowed here"
    | _ ->
        failwith
          "[internal error] string_list_of_longident: called with invalid longid"
  in
  lirec li
;;

let longident_lident_of_string_list loc =
  function
    [] -> assert false
  | [h] -> None, h
  | l ->
      let (clsna, path) = sep_last l in
      let li = longident_of_string_list loc path in Some li, clsna
;;

let string_list_of_longident_lident =
  function
    None, s -> [s]
  | Some li, s -> string_list_of_longident li @ [s]
  | _ -> assert false
;;

let is_uident s =
  match s.[0] with
    'A'..'Z' -> true
  | _ -> false
;;

let consume_longident loc l =
  let rec consrec acc =
    function
      h :: t when is_uident h -> consrec (h :: acc) t
    | rest ->
        if acc = [] then None, rest
        else Some (longident_of_string_list loc (List.rev acc)), rest
  in
  consrec [] l
;;

let consume_longident_lident loc l =
  match consume_longident loc l with
    None, h :: t -> Some (None, h), t
  | Some li, h :: t -> Some (Some li, h), t
  | _, [] ->
      Ploc.raise loc (Failure "consume_longident_lident: no lident found")
;;

let expr_of_string_list loc l =
  let rec exrec acc l =
    if l = [] then acc
    else
      match consume_longident_lident loc l with
        None, [] -> acc
      | Some lili, rest -> exrec (MLast.ExFle (loc, acc, lili)) rest
      | _ -> assert false
  in
  match l with
    [] -> Ploc.raise loc (Failure "expr_of_string_list: empty string list")
  | h :: t when not (is_uident h) -> exrec (MLast.ExLid (loc, h)) t
  | h :: _ ->
      match consume_longident loc l with
        None, _ -> assert false
      | Some li, rest -> exrec (MLast.ExLong (loc, li)) rest
;;

let rec expr_concat e1 e2 =
  let loc = MLast.loc_of_expr e1 in
  match e1, e2 with
    MLast.ExLong (_, li1), MLast.ExLong (_, li2) ->
      MLast.ExLong (loc, longid_concat li1 li2)
  | _, MLast.ExLid (_, id) -> MLast.ExFle (loc, e1, (None, id))
  | _, MLast.ExFle (_, e, lili) -> MLast.ExFle (loc, expr_concat e1 e, lili)
  | _ ->
      Ploc.raise (MLast.loc_of_expr e1)
        (Failure "expr_concat: invalid arguments")
;;
