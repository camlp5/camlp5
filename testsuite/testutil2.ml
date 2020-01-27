
open Printf;;
open Fmt;;
open Testutil ;;

let car = List.hd
let cdr = List.tl
let rec sep_last = function
    [] -> failwith "sep_last"
  | hd::[] -> (hd,[])
  | hd::tl ->
      let (l,tl) = sep_last tl in (l,hd::tl)

let invoked_with ?flag cmdna =
  let variant_names = [cmdna; cmdna^".byte"; cmdna^".native"; cmdna^".opt"] in

  let argv = Array.to_list Sys.argv in
  let path = Pcre.split ~rex:(Pcre.regexp "/") (car argv) in
  let fname, _ = sep_last path in

  List.exists ((=) fname) variant_names &&
  match flag with None -> true | Some flag ->
    let flag' = "-"^flag in
    let flag'' = "--"^flag in
    List.exists ((=) flag') (cdr argv) ||
      List.exists ((=) flag'') (cdr argv)

let exn_wrap_result ?msg f arg =
  let (actf, actarg) = match msg with
      None -> Fmt.string, "<unknown>"
    | Some x -> x in
  let open Rresult.R in
  try
    f arg
  with e ->
    let rbt = Printexc.get_raw_backtrace() in
    report_error e ;
    Fmt.(pf stderr "[during %a] %a@."
           actf actarg
           exn_backtrace (e, rbt)
    ) ;
    raise e
;;


  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
