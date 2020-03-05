(* camlp5r *)
(* pprintf.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)

type pr_context = { ind : int; bef : string; aft : string; dang : string };;
type 'a pr_fun = pr_context -> 'a -> string;;

let tab ind = String.make ind ' ';;
let empty_pc = {ind = 0; bef = ""; aft = ""; dang = ""};;

let sprint_break nspaces offset pc f g =
  Pretty.horiz_vertic
    (fun () ->
       let sp = String.make nspaces ' ' in
       Pretty.sprintf "%s%s%s" (f {pc with aft = ""}) sp
         (g {pc with bef = ""}))
    (fun () ->
       let s1 = f {pc with aft = ""} in
       let s2 =
         g {pc with ind = pc.ind + offset; bef = tab (pc.ind + offset)}
       in
       Pretty.sprintf "%s\n%s" s1 s2)
;;

let sprint_break_all force_newlines pc f fl =
  Pretty.horiz_vertic
    (fun () ->
       if force_newlines then Pretty.sprintf "\n"
       else
         let rec loop s =
           function
             (sp, off, f) :: fl ->
               let s =
                 Pretty.sprintf "%s%s%s" s (String.make sp ' ')
                   (f
                      {pc with bef = "";
                       aft = if fl = [] then pc.aft else ""})
               in
               loop s fl
           | [] -> s
         in
         loop (f (if fl = [] then pc else {pc with aft = ""})) fl)
    (fun () ->
       let rec loop s =
         function
           (sp, off, f) :: fl ->
             let s =
               Pretty.sprintf "%s\n%s" s
                 (f
                    {pc with ind = pc.ind + off; bef = tab (pc.ind + off);
                     aft = if fl = [] then pc.aft else ""})
             in
             loop s fl
         | [] -> s
       in
       loop (f (if fl = [] then pc else {pc with aft = ""})) fl)
;;
