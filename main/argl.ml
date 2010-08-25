(* camlp5r *)
(* $Id: argl.ml,v 1.4 2010/08/25 15:31:51 deraugla Exp $ *)

open Printf;

value action_arg = Versdep.action_arg;

value common_start s1 s2 =
  loop 0 where rec loop i =
    if i == String.length s1 || i == String.length s2 then i
    else if s1.[i] == s2.[i] then loop (i + 1)
    else i
;

value rec parse_arg s sl =
  fun
  [ [(name, action, _) :: spec_list] ->
      let i = common_start s name in
      if i == String.length name then
        try action_arg (String.sub s i (String.length s - i)) sl action with
        [ Arg.Bad _ -> parse_arg s sl spec_list ]
      else parse_arg s sl spec_list
  | [] -> None ]
;

value rec parse_aux spec_list anon_fun =
  fun
  [ [] -> []
  | [s :: sl] ->
      if String.length s > 1 && s.[0] = '-' then
        match parse_arg s sl spec_list with
        [ Some sl -> parse_aux spec_list anon_fun sl
        | None -> [s :: parse_aux spec_list anon_fun sl] ]
      else do { (anon_fun s : unit); parse_aux spec_list anon_fun sl } ]
;

value align_doc key s =
  let s =
    loop 0 where rec loop i =
      if i = String.length s then ""
      else if s.[i] = ' ' then loop (i + 1)
      else String.sub s i (String.length s - i)
  in
  let (p, s) =
    if String.length s > 0 then
      if s.[0] = '<' then
        loop 0 where rec loop i =
          if i = String.length s then ("", s)
          else if s.[i] <> ' ' then loop (i + 1)
          else
            let p = String.sub s 0 i in
            loop i where rec loop i =
              if i >= String.length s then (p, "")
              else if s.[i] = ' ' then loop (i + 1)
              else (p, String.sub s i (String.length s - i))
      else ("", s)
    else ("", "")
  in
  let tab =
    String.make (max 1 (13 - String.length key - String.length p)) ' '
  in
  p ^ tab ^ s
;

value make_symlist l =
  match l with
  [ [] -> "<none>"
  | [h :: t] -> List.fold_left (fun x y -> x ^ "|" ^ y) ("{" ^ h) t ^ "}" ]
;

value print_usage_list l =
  List.iter
    (fun (key, spec, doc) ->
       match Versdep.arg_symbol spec with
       [ Some symbs ->
           let s = make_symlist symbs in
           let synt = key ^ " " ^ s in
           eprintf "  %s %s\n" synt (align_doc synt doc)
       | None ->
           eprintf "  %s %s\n" key (align_doc key doc) ])
    l
;

value usage ini_sl ext_sl = do {
  eprintf "\
Usage: camlp5 [load-options] [--] [other-options]
Load options:
  -I directory  Add directory in search patch for object files.
  -where        Print camlp5 library directory and exit.
  -nolib        No automatic search for object files in library directory.
  <object-file> Load this file in Camlp5 core.
Other options:
  <file>        Parse this file.\n";
  print_usage_list ini_sl;
  let rec loop =
    fun
    [ [(y, _, _) :: _] when y = "-help" -> ()
    | [_ :: sl] -> loop sl
    | [] -> eprintf "  -help         Display this list of options.\n" ]
  in
  loop (ini_sl @ ext_sl);
  if ext_sl <> [] then do {
    eprintf "Options added by loaded object files:\n";
    print_usage_list ext_sl
  }
  else ()
};

value parse spec_list anon_fun remaining_args =
  let spec_list =
    Sort.list (fun (k1, _, _) (k2, _, _) -> k1 >= k2) spec_list
  in
  parse_aux spec_list anon_fun remaining_args
;
