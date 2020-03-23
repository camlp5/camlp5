(* camlp5r *)
(* asttools.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "q_MLast.cmo" *)

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
