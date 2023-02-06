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

let toremove = ref []
let ocaml_version = chomp (capturex("ocamlc",[|"ocamlc"; "-version"|]))
let ocaml_lib = chomp (capturex("ocamlc", [|"ocamlc"; "-where"|]))
let verbose = ref false
let preserve = ref false
let noexecute = ref false
let rev_interfaces = ref []
let rev_options = ref []
let rev_predicates = ref ["preprocessor"; "syntax"]
let rev_packages = ref ["camlp5"]
let randpid = ref (Unix.getpid())

let main cmd args =
let opt = ([%match {|mkcamlp5.opt$|}/pred] cmd) in

if opt then
  L.push rev_predicates "native"
else
  L.push rev_predicates "byte" ;

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
;

let rec parec = function
    "-help"::l ->
     usage() ;
     exit 0
  | "-verbose"::l ->
     verbose := true ;
     parec l
  | "-random-pid"::pid::l ->
     randpid := int_of_string pid ;
     parec l
  | "-preserve"::l ->
     preserve := true ;
     parec l
  | "-n"::l ->
     noexecute := true ;
     parec l
  | "-package"::s::l ->
     List.iter (L.push rev_packages) ([%split {|,|}] s) ;
     parec l
  | "-predicates"::s::l ->
     List.iter (L.push rev_predicates) ([%split {|,|}] s) ;
     parec l
  | s::l ->
     (match ([%match {|([^\./]+)\.cmi$|}/strings !1] s) with
       Some s ->
        if opt then failwith Fmt.(str "%s: cannot specify .cmi file for %s" cmd cmd) ;
        L.push rev_interfaces (String.capitalize_ascii s)
       | None ->
          L.push rev_options s) ;
     parec l
  | [] -> ()
    in
    parec args ;

let interfaces = List.rev !rev_interfaces in
let options = List.rev !rev_options in
let packages = List.rev !rev_packages in
let predicates = List.rev !rev_predicates in

let link =
if not opt then begin
    let stringified = Fmt.(str "%a" (list ~sep:(const string "; ") (quote string)) interfaces) in
    let txt =
      if ocaml_version < "4.08.0" then
        let extract_crc = [%pattern {|${ocaml_lib}/extract_crc|}] in
        let crcs = capturex(extract_crc,Array.of_list (["extract_crc"; "-I"; ocaml_lib] @ interfaces)) in
        if !verbose then Fmt.(pf stderr "%s%!" crcs) ;
        [%pattern {|${crcs}
let _ = Dynlink.add_available_units crc_unit_list
|}]
        else [%pattern {|Dynlink.set_allowed_units [
  ${stringified}
] ;;
|}] in
    let linkbase = Fmt.(str "link%04d" !randpid) in
    List.iter (L.push toremove) [[%pattern {|${linkbase}.ml|}]; [%pattern {|${linkbase}.cmi|}]; [%pattern {|${linkbase}.cmo|}]; [%pattern {|${linkbase}.cmx|}]] ;
    write_fully ~mode:0o755 [%pattern {|${linkbase}.ml|}] txt ;
    [[%pattern {|${linkbase}.ml|}]]
  end
else [] in

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

let cmd = Sys.argv.(0) ;;
let argv = List.tl (Array.to_list Sys.argv) ;;
main cmd argv ;;
