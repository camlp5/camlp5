(** -syntax camlp5o *)
open Rresult
open Bos
open Fpath

let ( let* ) x f = Rresult.(>>=) x f ;;


module L = struct
let sub l n = List.nth !l n
let push l x = (l := x :: !l)
let pop l =
  match !l with
    [] -> failwith "pop: empty list"
  | h::t -> l := t ; h
let len l = List.length !l
end

let read_ic_fully ?(msg="") ?(channel=stdin) () =
  let fd = Unix.descr_of_in_channel channel in
  if Unix.isatty fd && msg <> "" then
    Fmt.(pf stdout "%s\n%!" msg) ;
  let b = Buffer.create 23 in
  let rec rrec () =
    match input_char channel with
      exception End_of_file -> Buffer.contents b
    | c -> Buffer.add_char b c ; rrec ()
  in
  rrec()

let write_fully ~mode ofile txt =
  OS.File.write ~mode (v ofile) txt |> R.failwith_error_msg

let capturex (cmd, args) =
  let channel = Unix.open_process_args_in cmd args in
  let txt = read_ic_fully ~channel () in
  close_in channel ;
  txt

let join s l = String.concat s l

let chomp s =
  [%subst {|\n+$|} / {||} / s pcre] s
;;

let toremove = ref []
let ocaml_version = chomp (capturex("ocamlc",[|"ocamlc"; "-version"|]))
let ocaml_lib = chomp (capturex("ocamlc", [|"ocamlc"; "-where"|]))
;;

let verbose = ref false
let preserve = ref false
let noexecute = ref false
let rev_interfaces = ref []
let rev_options = ref []
let rev_predicates = ref ["preprocessor"; "syntax"]
let rev_packages = ref ["camlp5"]
let randpid = ref (Unix.getpid())
let opt =
  None <> ([%match {|mkcamlp5.opt$|}] Sys.argv.(0))
;;
if opt then
  L.push rev_predicates "native"
else
  L.push rev_predicates "byte" ;;

Stdlib.at_exit (fun () ->
    !toremove
    |>  List.iter (fun f ->
            (let* existsp = OS.File.exists (v f) in
             if existsp then
               if !preserve then
                 Ok (Fmt.(pf stderr "Preserving tmpfile %s\n%!" f))
               else
                 OS.Path.delete (v f)
             else Ok()) |> ignore
          )
  )
;;

let usage_msg = {|
Options:
  -I <dir>   Add directory in search path for object files

All options of ocamlc (and ocamlfind) are also available

Files:
  .cmi file  Add visible interface for possible future loading
  .cmo file  Load this file in core
  .cma file  Load this file in core

|} ;;

let usage () = Fmt.(pf stdout "%s" usage_msg)

let rest_arg s =
  if None <> ([%match {|\.cmi$|}] s) then begin
    if opt then failwith Fmt.(str "%s: cannot specify .cmi file for %s" Sys.argv.(0) Sys.argv.(0)) ;
    L.push rev_interfaces s
    end
  else
    L.push rev_options s
;;

let argv = ref (List.tl (Array.to_list Sys.argv)) ;;

while L.len argv > 0 do
    if L.sub argv 0 = "-help" then begin
        ignore(L.pop argv) ;
        usage() ;
        exit 0
      end
    else if L.sub argv 0 = "-verbose" then begin
        ignore(L.pop argv) ;
        verbose := true
      end
    else if L.sub argv 0 = "-random-pid" then begin
        ignore(L.pop argv) ;
        randpid := int_of_string (L.pop argv)
      end
    else if L.sub argv 0 = "-preserve" then begin
        ignore(L.pop argv) ;
        preserve := true
      end
    else if L.sub argv 0 = "-n" then begin
        ignore(L.pop argv) ;
        noexecute := true
      end
    else if L.sub argv 0 = "-package" then begin
        ignore(L.pop argv);
        List.iter (L.push rev_packages) ([%split {|,|}] (L.pop argv))
      end
    else if L.sub argv 0 = "-predicates" then begin
        ignore(L.pop argv) ;
        List.iter (L.push rev_predicates) ([%split {|,|}] (L.pop argv))
      end
    else if None <> ([%match {|\.cmi$|}] (L.sub argv  0)) then begin
        if opt then failwith Fmt.(str "%s: cannot specify .cmi file for %s" Sys.argv.(0) Sys.argv.(0)) ;
        L.push rev_interfaces (L.pop argv)
      end
    else
      L.push rev_options (L.pop argv)
done

(*
Arg.(parse [
         "-verbose",Set verbose,"enable verbose output"
       ; "-preserve",Set preserve,"preserve generated tmp-files"
       ; "-random-pid",Set_int randpid,"supply the value for the PID (for generating tmp filenames)"
       ; "-n",Set preserve,"no-execute"
       ; "-package",String(fun s -> List.iter (L.push packages) ([%split {|,|}] s)),"add packages"
       ; "-predicates",String(fun s -> List.iter (L.push predicates) ([%split {|,|}] s)),"add predicates"
       ; "--", Rest rest_arg, "rest of the arguments"
       ]
       rest_arg
       usage_msg)
;;
 *)
let interfaces = List.rev !rev_interfaces
let options = List.rev !rev_options
let packages = List.rev !rev_packages
let predicates = List.rev !rev_predicates

let link =
if not opt then begin
    let stringified = Fmt.(str "%a" (list ~sep:(const string "; ") (quote string)) interfaces) in
    let txt =
      if ocaml_version < "4.08.0" then
        let extract_crc = [%pattern {|${ocaml_lib}/extract_crc|}] in
        let crcs = capturex(extract_crc,Array.of_list (["extract_crc"; "-I"; ocaml_lib] @ interfaces)) in
        if !verbose then Fmt.(pf stderr "%s%!" crcs) ;
        [%pattern {|
${crcs}
let _ = Dynlink.add_available_units crc_unit_list
|}]
        else [%pattern {|
Dynlink.set_allowed_units [
  ${stringified}
] ;;
|}] in
    let linkbase = Fmt.(str "link%04d" !randpid) in
    List.iter (L.push toremove) [[%pattern {|${linkbase}.ml|}]; [%pattern {|${linkbase}.cmi|}]; [%pattern {|${linkbase}.cmo|}]; [%pattern {|${linkbase}.cmx|}]] ;
    write_fully ~mode:0o755 [%pattern {|${linkbase}.ml|}] txt ;
    [[%pattern {|${linkbase}.ml|}]]
  end
else []

let cmd = ["ocamlfind"]
	  @[if opt then "ocamlopt" else "ocamlc"]
	     @["-predicates"; join"," predicates]
	    @["-package"; join "," packages]
	    @(if !verbose then ["-verbose"] else [])
	    @["-linkall"; "-linkpkg"]
	    @ link @ options
	    @[if opt then "odyl.cmx" else "odyl.cmo"] in
    if !verbose then Fmt.(pf stderr "%a\n%!" (list ~sep:(const string " ") string) cmd) ;
    if not !noexecute then
      Unix.execvp "ocamlfind" (Array.of_list cmd)
;;
