
(*

  This is the source of the function below: it is processed by pa_ppx_regexp.

  Much simpler to do that than try to maintain the code by hand.

let unpack_qe = [%match {x|^{(%|%%)([^%| \n\t]+)([ \n\t]+[^| \n\t]+)?\|(.*)\|([^|}]*)}$|x} /exc pcre2 strings (!1, !2, 3, !4) s]
*)

let __re__ =
  Pcre2.regexp ~flags:[`DOTALL]
    "^{(%|%%)([^%| \\n\\t]+)([ \\n\\t]+[^| \\n\\t]+)?\\|(.*)\\|([^|}]*)}$"

let unpack_qe =
  fun __subj__ ->
    (fun __g__ ->
       Pcre2.get_substring __g__ 1, Pcre2.get_substring __g__ 2,
       (try Some (Pcre2.get_substring __g__ 3) with Not_found -> None),
       Pcre2.get_substring __g__ 4)
      (Pcre2.exec ~rex:__re__ __subj__)

let make_string kind loc s =
  let (percents, attrid, ws_delim_opt, payload) = unpack_qe s in
  if percents <> kind then
    failwith (Printf.sprintf "Quotedext.make_string: kind %s was not found (saw <<%s>> instead)" kind percents) ;
  (* '(' '%' <attrid> <ws+delim> + '|' *)
  let payload_shift = 1 + (String.length percents) + (String.length attrid) +
                        (match ws_delim_opt with None -> 0 | Some s -> String.length s) +
                        1 in
  let payload_len = String.length payload in
  let payload_loc = Ploc.(sub loc payload_shift payload_len) in
  let attrid_loc = Ploc.(sub loc (1 + (String.length percents)) (String.length attrid)) in
  ((attrid_loc, attrid),(payload_loc,payload))
