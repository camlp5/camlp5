
open Printf;;
open Fmt;;
open Testutil ;;

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
