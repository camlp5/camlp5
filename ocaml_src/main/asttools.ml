(* camlp5r *)
(* asttools.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "q_MLast.cmo" *)

let prefix_eq s0 s1 =
  let s0len = String.length s0 in
  s0len <= String.length s1 && s0 = String.sub s1 0 s0len
;;

type ('a, 'b) choice =
    Left of 'a
  | Right of 'b
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
    | mt -> mt, List.rev acc
  in
  arec [] mt
;;

let rec sep_last =
  function
    [] -> failwith "sep_last"
  | [hd] -> hd, []
  | hd :: tl -> let (l, tl) = sep_last tl in l, hd :: tl
;;

let expr_to_path_module_expr e =
  let rec erec =
    function
      MLast.ExUid (loc, i) -> MLast.MeUid (loc, i)
    | MLast.ExAcc (loc, a, b) -> MLast.MeAcc (loc, erec a, erec b)
    | _ -> failwith "caught"
  in
  try Some (erec e) with Failure _ -> None
;;

let expr_last_is_uid e =
  let rec erec =
    function
      MLast.ExUid (_, _) -> true
    | MLast.ExAcc (_, _, e) -> erec e
    | _ -> false
  in
  erec e
;;

let expr_first_is_id e =
  let rec erec =
    function
      MLast.ExUid (_, _) -> true
    | MLast.ExLid (_, _) -> true
    | MLast.ExAcc (_, e, _) -> erec e
    | _ -> false
  in
  erec e
;;

let expr_is_module_path e =
  let rec erec =
    function
      MLast.ExUid (_, _) -> true
    | MLast.ExAcc (_, a, b) -> erec a && erec b
    | _ -> false
  in
  erec e
;;

let patt_is_module_path e =
  let rec erec =
    function
      MLast.PaLong (_, MLast.LiUid (_, _)) -> true
    | MLast.PaAcc (_, a, b) -> erec a && erec b
    | _ -> false
  in
  erec e
;;
 
let expr_left_assoc_acc e =
  let rec arec =
    function
      MLast.ExAcc (loc, e1, e2) as z ->
        begin match e2 with
          MLast.ExAcc (_, e2, e3) ->
            arec (MLast.ExAcc (loc, MLast.ExAcc (loc, e1, e2), e3))
        | _ -> z
        end
    | e -> e
  in
  arec e
;;
 
let patt_left_assoc_acc e =
  let rec arec =
    function
      MLast.PaAcc (_, e1, e2) as z ->
        begin match e2 with
          MLast.PaAcc (loc, e2, e3) ->
            arec (MLast.PaAcc (loc, MLast.PaAcc (loc, e1, e2), e3))
        | _ -> z
        end
    | e -> e
  in
  arec e
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
  | Some attrid -> MLast.StExten (loc, (attrid, MLast.StAttr (loc, [si])))
;;

let sig_item_to_inline si ext =
  let loc = MLast.loc_of_sig_item si in
  match ext with
    None -> si
  | Some attrid -> MLast.SgExten (loc, (attrid, MLast.SiAttr (loc, [si])))
;;
