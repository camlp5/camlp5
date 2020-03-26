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
      MLast.PaUid (_, _) -> true
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
      MLast.PaAcc (loc, e1, e2) as z ->
        begin match e2 with
          MLast.PaAcc (_, e2, e3) ->
            arec (MLast.PaAcc (loc, MLast.PaAcc (loc, e1, e2), e3))
        | _ -> z
        end
    | e -> e
  in
  arec e
;;
