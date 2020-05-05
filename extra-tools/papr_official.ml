(* camlp5r *)
(* papr_official.ml,v *)

value rec sep_last = fun [
    [] -> failwith "sep_last"
  | [ hd ] -> (hd,[])
  | [ hd::tl ] ->
      let (l,tl) = sep_last tl in (l,[ hd::tl ])
  ]
;

value input_magic ic magic = do {
  let maglen = String.length magic in
  let b = Bytes.create maglen in
  really_input ic b 0 maglen ;
  Bytes.to_string b
}
;

value input_implem ic = do {
  if Config.ast_impl_magic_number <> input_magic ic Config.ast_impl_magic_number then
    failwith "input_implem: bad magic number"
  else
    let _ = input_value ic in
    (input_value ic : Parsetree.structure)
}
;

value input_interf ic = do {
  if Config.ast_intf_magic_number <> input_magic ic Config.ast_intf_magic_number then
    failwith "input_interf: bad magic number"
  else
    let _ = input_value ic in
    (input_value ic : Parsetree.signature)
}
;

value output_magic oc magic =
  output_string oc magic
;

value output_interf fname oc (pt : Parsetree.signature) = do {
  output_string oc Config.ast_intf_magic_number;
  output_value oc fname;
  output_value oc pt;
  flush oc;
};

value output_implem fname oc (pt : Parsetree.structure) = do {
  output_string oc Config.ast_impl_magic_number;
  output_value oc fname;
  output_value oc pt;
  flush oc;
};

value parse_interf fname ic = do {
  let lb = Lexing.from_channel ic in
  Location.init lb fname ;
  Parse.interface lb
}
;

value parse_implem fname ic = do {
  let lb = Lexing.from_channel ic in
  Location.init lb fname ;
  Parse.implementation lb
}
;

value print_interf oc v = do {
  let ofmt = Format.formatter_of_out_channel oc in
  Pprintast.signature ofmt v ;
  Format.pp_print_flush ofmt ()
};

value print_implem oc v = do {
  let ofmt = Format.formatter_of_out_channel oc in
  Pprintast.structure ofmt v ;
  Format.pp_print_flush ofmt ()
};

value binary_input = ref False ;
value binary_output = ref False ;
value files = ref [] ;
value filetype = ref None ;

value set_impl s = filetype.val := Some "-impl" ;
value set_intf s = filetype.val := Some "-intf" ;

value passthru paf prf ic oc =
  ic |> paf |> prf oc
;

value papr_official () = do {
    Arg.(parse [
             ("-binary-input",Set binary_input," binary input");
             ("-binary-output",Set binary_output," binary output");
             ("-impl", Unit set_impl , " implementation");
             ("-intf", Unit set_intf , " interface")
      ]
      (fun s -> files.val := [ s :: files.val ])
      "papr_official: usage") ;
      let open_or opener ifminus = fun [
        "-" -> (ifminus, "") | f -> (opener f, f)
      ] in
      let ((ic, ifile), (oc, _)) = match List.rev files.val with [
        [] -> ((stdin, ""), (stdout, ""))
      | [ifile] -> do {
        (open_or open_in stdin ifile, (stdout, ""))
      }
      | [ifile; ofile] -> do {
        (open_or open_in stdin ifile,
         open_or open_out stdout ofile)
      }
      | _ -> failwith "too many filenames provided"
      ] in
    match (filetype.val, binary_input.val, binary_output.val) with [
      (Some "-impl", True, True) ->
      failwith "cannot have both binary input and output"
    | (Some "-impl", True, False) ->
      passthru input_implem print_implem ic oc
    | (Some "-impl", False, True) ->
      passthru (parse_implem ifile) (output_implem file) ic oc
    | (Some "-impl", False, False) ->
      passthru (parse_implem ifile) print_implem ic oc

    | (Some "-intf", True, True) ->
      failwith "cannot have both binary input and output"
    | (Some "-intf", True, False) ->
      passthru input_interf print_interf ic oc
    | (Some "-intf", False, True) ->
      passthru (parse_interf ifile) (output_interf ifile) ic oc
    | (Some "-intf", False, False) ->
      passthru (parse_interf ifile) print_interf ic oc

    | _ -> failwith "unrecognized filetype"
    ] ;
    close_out oc ;
    close_in ic
  }
;

papr_official () ;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
