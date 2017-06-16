(* camlp5r *)
(* odyl.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

let apply_load () =
  let i = ref 1 in
  let stop = ref false in
  while not !stop && !i < Array.length Sys.argv do
    let s = Sys.argv.(!i) in
    if s = "-I" && !i + 1 < Array.length Sys.argv then
      begin Odyl_main.directory Sys.argv.(!i + 1); i := !i + 2 end
    else if s = "-nolib" then begin Odyl_main.nolib := true; incr i end
    else if s = "-where" then
      begin
        print_string Odyl_config.standard_library;
        print_newline ();
        flush stdout;
        exit 0
      end
    else if s = "--" then begin incr i; stop := true; () end
    else if String.length s > 0 && s.[0] == '-' then stop := true
    else if
      Filename.check_suffix s ".cmo" || Filename.check_suffix s ".cma"
    then
      begin Odyl_main.loadfile s; incr i end
    else stop := true
  done
;;

let main () =
  try apply_load (); !(Odyl_main.go) () with
    Odyl_main.Error (fname, str) ->
      flush stdout;
      Printf.eprintf "Error while loading \"%s\": " fname;
      Printf.eprintf "%s.\n" str;
      flush stderr;
      exit 2
;;

Printexc.catch main ();;
