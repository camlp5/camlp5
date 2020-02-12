(* camlp5r *)
(* papr_official.ml,v *)

value rec sep_last = fun [
    [] -> failwith "sep_last"
  | [ hd ] -> (hd,[])
  | [ hd::tl ] ->
      let (l,tl) = sep_last tl in (l,[ hd::tl ])
  ]
;

value invoked_with ?{flag} cmdna =
  let variant_names = [cmdna; cmdna^".byte"; cmdna^".native"; cmdna^".opt"] in

  let argv = Array.to_list Sys.argv in
  let path = Pcre.split ~{rex=(Pcre.regexp "/")} (List.hd argv) in
  let (fname, _) = sep_last path in

  List.exists ((=) fname) variant_names &&
  match flag with [
    None -> True
  | Some flag ->
    let flag' = "-"^flag in
    let flag'' = "--"^flag in
    List.exists ((=) flag') (List.tl argv) ||
      List.exists ((=) flag'') (List.tl argv) ]
;

value files = ref [] ;
value filetype = ref None ;

value set_impl s = filetype.val := Some "-impl" ;
value set_intf s = filetype.val := Some "-intf" ;

value papr_official () = do {
    Arg.(parse [
             ("-impl", Unit set_impl , " implementation");
             ("-intf", Unit set_intf , " interface")
      ]
      (fun s -> files.val := [ s :: files.val ])
      "papr_official: usage") ;
      let open_or opener ifminus = fun [
        "-" -> ifminus | f -> opener f
      ] in
      let (ic, oc) = match List.rev files.val with [
        [] -> (stdin, stdout)
      | [ifile] -> (open_or open_in stdin ifile,
                    stdout)
      | [ifile; ofile] -> (open_or open_in stdin ifile,
                           open_or open_out stdout ofile)
      | _ -> failwith "too many filenames provided"
      ] in
    let ofmt = Format.formatter_of_out_channel oc in
      match filetype.val with [
        None -> failwith "must specify filetype (-impl or -intf)"
      | Some "-impl" ->
        ic |> Lexing.from_channel |> Parse.implementation |> Pprintast.structure ofmt
      | Some "-intf" ->
        ic |> Lexing.from_channel |> Parse.interface |> Pprintast.signature ofmt
      | _ -> failwith "unrecognized filetype"
      ] ;
      Format.pp_print_flush ofmt () ;
    close_out oc ;
    close_in ic
  }
;

value _ =
if invoked_with "papr_official" then
  papr_official ()
else ()
;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
