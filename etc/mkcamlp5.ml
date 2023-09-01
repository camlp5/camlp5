(**pp -syntax camlp5o -ppopt -pa_ppx_regexp-nostatic -package bos *)
open Rresult
open Bos
open Fpath

let ( let* ) x f = Rresult.(>>=) x f


module L =
  struct
    let sub l n = List.nth !l n
    let push l x = l := x :: !l
    let pop l =
      match !l with
        [] -> failwith "pop: empty list"
      | h :: t -> l := t; h
    let len l = List.length !l
  end

let read_ic_fully ?(msg = "") ?(channel = stdin) () =
  let fd = Unix.descr_of_in_channel channel in
  if Unix.isatty fd && msg <> "" then Fmt.(pf stdout "%s\n%!" msg);
  let b = Buffer.create 23 in
  let rec rrec () =
    match input_char channel with
      exception End_of_file -> Buffer.contents b
    | c -> Buffer.add_char b c; rrec ()
  in
  rrec ()

let write_fully ~mode ofile txt =
  OS.File.write ~mode (v ofile) txt |> R.failwith_error_msg

let capturex cmd =
  let channel = Unix.open_process_in cmd in
  let txt = read_ic_fully ~channel () in close_in channel; txt

let join s l = String.concat s l

let chomp s =
  Re.replace ~all:false (Re.Perl.compile_pat ~opts:[`Dotall] "\\n+$")
    ~f:(fun __g__ -> String.concat "" []) s


let usage_msg =
  "\nOptions:\n  -I <dir>   Add directory in search path for object files\n\nAll options of ocamlc (and ocamlfind) are also available\n\nFiles:\n  .cmi file  Add visible interface for possible future loading\n  .cmo file  Load this file in core\n  .cma file  Load this file in core\n\n"

let usage () = Fmt.(pf stdout "%s" usage_msg)

let toremove = ref []
let ocaml_version = chomp (capturex "ocamlc -version")
let ocaml_lib = chomp (capturex "ocamlc -where")
let verbose = ref false
let preserve = ref false
let noexecute = ref false
let rev_interfaces = ref []
let rev_options = ref []
let rev_predicates = ref ["preprocessor"; "syntax"]
let rev_packages = ref ["camlp5"]
let randpid = ref (Unix.getpid ())

let main cmd args =
  let opt =
    (let __re__ = Re.Perl.compile_pat ~opts:[] "mkcamlp5.opt$" in
     fun __subj__ -> Re.execp __re__ __subj__)
      cmd
  in
  if opt then L.push rev_predicates "native"
  else L.push rev_predicates "byte";
  Stdlib.at_exit
    (fun () ->
       !toremove |>
         List.iter
           (fun f ->
              ( let* ) (OS.File.exists (v f))
                (fun existsp ->
                   if existsp then
                     if !preserve then
                       Ok Fmt.(pf stderr "Preserving tmpfile %s\n%!" f)
                     else OS.Path.delete (v f)
                   else Ok ()) |>
                ignore));
  let rec parec =
    function
      "-help" :: l -> usage (); exit 0
    | "-verbose" :: l -> verbose := true; parec l
    | "-random-pid" :: pid :: l -> randpid := int_of_string pid; parec l
    | "-preserve" :: l -> preserve := true; parec l
    | "-n" :: l -> noexecute := true; parec l
    | "-package" :: s :: l ->
        List.iter (L.push rev_packages)
          ((let __re__ = Re.Perl.compile_pat ~opts:[] "," in
            fun __subj__ -> Re.split __re__ __subj__)
             s);
        parec l
    | "-predicates" :: s :: l ->
        List.iter (L.push rev_predicates)
          ((let __re__ = Re.Perl.compile_pat ~opts:[] "," in
            fun __subj__ -> Re.split __re__ __subj__)
             s);
        parec l
    | s :: l ->
        begin match
          (let __re__ = Re.Perl.compile_pat ~opts:[] "([^\\./]+)\\.cmi$" in
           fun __subj__ ->
             match
               Option.map (fun __g__ -> Re.Group.get __g__ 1)
                 (Re.exec_opt __re__ __subj__)
             with
               exception Not_found -> None
             | rv -> rv)
            s
        with
          Some s ->
            if opt then
              failwith
                Fmt.(str "%s: cannot specify .cmi file for %s" cmd cmd);
            L.push rev_interfaces (String.capitalize_ascii s)
        | None -> L.push rev_options s
        end;
        parec l
    | [] -> ()
  in
  parec args;
  let interfaces = List.rev !rev_interfaces in
  let options = List.rev !rev_options in
  let packages = List.rev !rev_packages in
  let predicates = List.rev !rev_predicates in
  let link =
    if not opt then
      let stringified =
        Fmt.
        (str "%a" (list ~sep:(const string "; ") (quote string)) interfaces)
      in
      let txt =
        String.concat ""
          ["Dynlink.set_allowed_units [\n  "; stringified; "\n] ;;\n"]
      in
      let linkbase = Fmt.(str "link%04d" !randpid) in
      List.iter (L.push toremove)
        [String.concat "" [linkbase; ".ml"];
         String.concat "" [linkbase; ".cmi"];
         String.concat "" [linkbase; ".cmo"];
         String.concat "" [linkbase; ".cmx"]];
      write_fully ~mode:0o755 (String.concat "" [linkbase; ".ml"]) txt;
      [String.concat "" [linkbase; ".ml"]]
    else []
  in
  let cmd =
    ["ocamlfind"] @ [if opt then "ocamlopt" else "ocamlc"] @
    ["-predicates"; join "," predicates] @ ["-package"; join "," packages] @
    (if !verbose then ["-verbose"] else []) @
    ["-linkall"; "-linkpkg"; "-I"; "+dynlink"] @ link @ options @
    [if opt then "odyl.cmx" else "odyl.cmo"]
  in
  if !verbose then
    Fmt.(pf stderr "%a\n%!" (list ~sep:(const string " ") string) cmd);
  if not !noexecute then
    match
      Unix.system (Filename.quote_command (List.hd cmd) (List.tl cmd))
    with
      WEXITED 0 -> ()
    | WEXITED n ->
        Fmt.(pf stderr "Maybe an error? Command exited with code %d\n%!" n);
        Stdlib.exit n
    | WSIGNALED n ->
        Fmt.
        (pf stderr "Maybe an error? Command signaled (??) with code %d\n%!"
          n);
        Stdlib.exit (-1)
    | WSTOPPED n ->
        Fmt.
        (pf stderr "Maybe an error? Command stopped (??) with code %d\n%!" n);
        Stdlib.exit (-1)

let cmd = Sys.argv.(0)
let argv = List.tl (Array.to_list Sys.argv)
let _ = main cmd argv
