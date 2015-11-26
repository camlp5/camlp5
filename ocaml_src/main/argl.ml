(* camlp5r *)
(* argl.ml,v *)

open Printf;;
open Versdep;;

let action_arg s sl =
  function
    Arg.Set r -> if s = "" then begin r := true; Some sl end else None
  | Arg.Clear r -> if s = "" then begin r := false; Some sl end else None
  | Arg.String f ->
      if s = "" then
        match sl with
          s :: sl -> f s; Some sl
        | [] -> None
      else begin f s; Some sl end
  | Arg.Int f ->
      if s = "" then
        match sl with
          s :: sl -> (try f (int_of_string s); Some sl with Failure _ -> None)
        | [] -> None
      else (try f (int_of_string s); Some sl with Failure _ -> None)
  | Arg.Float f ->
      if s = "" then
        match sl with
          s :: sl -> f (float_of_string s); Some sl
        | [] -> None
      else begin f (float_of_string s); Some sl end
  | a ->
      match arg_rest a with
        Some f -> List.iter f (s :: sl); Some []
      | None ->
          match arg_set_string a with
            Some r ->
              if s = "" then
                match sl with
                  s :: sl -> r := s; Some sl
                | [] -> None
              else begin r := s; Some sl end
          | None ->
              match arg_set_int a with
                Some r ->
                  if s = "" then
                    match sl with
                      s :: sl ->
                        begin try r := int_of_string s; Some sl with
                          Failure _ -> None
                        end
                    | [] -> None
                  else
                    (try r := int_of_string s; Some sl with Failure _ -> None)
              | None ->
                  match arg_set_float a with
                    Some r ->
                      if s = "" then
                        match sl with
                          s :: sl -> r := float_of_string s; Some sl
                        | [] -> None
                      else begin r := float_of_string s; Some sl end
                  | None ->
                      match arg_symbol a with
                        Some (syms, f) ->
                          begin match if s = "" then sl else s :: sl with
                            s :: sl when List.mem s syms -> f s; Some sl
                          | _ -> None
                          end
                      | None ->
                          match arg_tuple a with
                            Some _ -> failwith "Arg.Tuple not implemented"
                          | None ->
                              match arg_bool a with
                                Some _ -> failwith "Arg.Bool not implemented"
                              | None ->
                                  match a with
                                    Arg.Unit f ->
                                      if s = "" then begin f (); Some sl end
                                      else None
                                  | _ -> assert false
;;

let common_start s1 s2 =
  let rec loop i =
    if i == String.length s1 || i == String.length s2 then i
    else if s1.[i] == s2.[i] then loop (i + 1)
    else i
  in
  loop 0
;;

let rec parse_arg s sl =
  function
    (name, action, _) :: spec_list ->
      let i = common_start s name in
      if i == String.length name then
        try action_arg (String.sub s i (String.length s - i)) sl action with
          Arg.Bad _ -> parse_arg s sl spec_list
      else parse_arg s sl spec_list
  | [] -> None
;;

let rec parse_aux spec_list anon_fun =
  function
    [] -> []
  | s :: sl ->
      if String.length s > 1 && s.[0] = '-' then
        match parse_arg s sl spec_list with
          Some sl -> parse_aux spec_list anon_fun sl
        | None -> s :: parse_aux spec_list anon_fun sl
      else begin (anon_fun s : unit); parse_aux spec_list anon_fun sl end
;;

let align_doc key s =
  let s =
    let rec loop i =
      if i = String.length s then ""
      else if s.[i] = ' ' then loop (i + 1)
      else String.sub s i (String.length s - i)
    in
    loop 0
  in
  let (p, s) =
    if String.length s > 0 then
      if s.[0] = '<' then
        let rec loop i =
          if i = String.length s then "", s
          else if s.[i] <> ' ' then loop (i + 1)
          else
            let p = String.sub s 0 i in
            let rec loop i =
              if i >= String.length s then p, ""
              else if s.[i] = ' ' then loop (i + 1)
              else p, String.sub s i (String.length s - i)
            in
            loop i
        in
        loop 0
      else "", s
    else "", ""
  in
  let tab =
    String.make (max 1 (13 - String.length key - String.length p)) ' '
  in
  p ^ tab ^ s
;;

let make_symlist l =
  match l with
    [] -> "<none>"
  | h :: t -> List.fold_left (fun x y -> x ^ "|" ^ y) ("{" ^ h) t ^ "}"
;;

let print_usage_list l =
  List.iter
    (fun (key, spec, doc) ->
       match Versdep.arg_symbol spec with
         Some (symbs, _) ->
           let s = make_symlist symbs in
           let synt = key ^ " " ^ s in
           eprintf "  %s %s\n" synt (align_doc synt doc)
       | None -> eprintf "  %s %s\n" key (align_doc key doc))
    l
;;

let usage ini_sl ext_sl =
  let name = Filename.basename Sys.argv.(0) in
  eprintf "\
Usage: %s [load-options] [--] [other-options]
Load options:
  -I directory  Add directory in search patch for object files.
  -where        Print camlp5 library directory and exit.
  -nolib        No automatic search for object files in library directory.
  <object-file> Load this file in Camlp5 core.
Other options:
  <file>        Parse this file.\n"
    name;
  print_usage_list ini_sl;
  let rec loop =
    function
      (y, _, _) :: _ when y = "-help" -> ()
    | _ :: sl -> loop sl
    | [] -> eprintf "  -help         Display this list of options.\n"
  in
  loop (ini_sl @ ext_sl);
  if ext_sl <> [] then
    begin
      eprintf "Options added by loaded object files:\n";
      print_usage_list ext_sl
    end
;;

let parse spec_list anon_fun remaining_args =
  let spec_list =
    list_sort (fun (k1, _, _) (k2, _, _) -> compare k2 k1) spec_list
  in
  parse_aux spec_list anon_fun remaining_args
;;
