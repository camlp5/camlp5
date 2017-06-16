(* camlp5r *)
(* pprintf.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)

type pr_context = { ind : int; bef : string; aft : string; dang : string };;
type 'a pr_fun = pr_context -> 'a -> string;;

let tab ind = String.make ind ' ';;
let empty_pc = {ind = 0; bef = ""; aft = ""; dang = ""};;

let with_ind pc ind =
  {ind = ind; bef = pc.bef; aft = pc.aft; dang = pc.dang}
;;
let with_ind_bef pc ind bef =
  {ind = ind; bef = bef; aft = pc.aft; dang = pc.dang}
;;
let with_ind_bef_aft pc ind bef aft =
  {ind = ind; bef = bef; aft = aft; dang = pc.dang}
;;
let with_bef pc bef =
  {ind = pc.ind; bef = bef; aft = pc.aft; dang = pc.dang}
;;
let with_bef_aft pc bef aft =
  {ind = pc.ind; bef = bef; aft = aft; dang = pc.dang}
;;
let with_bef_aft_dang pc bef aft dang =
  {ind = pc.ind; bef = bef; aft = aft; dang = dang}
;;
let with_bef_dang pc bef dang =
  {ind = pc.ind; bef = bef; aft = pc.aft; dang = dang}
;;
let with_aft pc aft =
  {ind = pc.ind; bef = pc.bef; aft = aft; dang = pc.dang}
;;
let with_aft_dang pc aft dang =
  {ind = pc.ind; bef = pc.bef; aft = aft; dang = dang}
;;
let with_dang pc dang =
  {ind = pc.ind; bef = pc.bef; aft = pc.aft; dang = dang}
;;

let sprint_break nspaces offset pc f g =
  Pretty.horiz_vertic
    (fun () ->
       let sp = String.make nspaces ' ' in
       Pretty.sprintf "%s%s%s" (f (with_aft pc "")) sp (g (with_bef pc "")))
    (fun () ->
       let s1 = f (with_aft pc "") in
       let s2 =
         g (with_ind_bef pc (pc.ind + offset) (tab (pc.ind + offset)))
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
                   (f (with_bef_aft pc "" (if fl = [] then pc.aft else "")))
               in
               loop s fl
           | [] -> s
         in
         loop (f (if fl = [] then pc else with_aft pc "")) fl)
    (fun () ->
       let rec loop s =
         function
           (sp, off, f) :: fl ->
             let s =
               Pretty.sprintf "%s\n%s" s
                 (f
                    (with_ind_bef_aft pc (pc.ind + off) (tab (pc.ind + off))
                       (if fl = [] then pc.aft else "")))
             in
             loop s fl
         | [] -> s
       in
       loop (f (if fl = [] then pc else with_aft pc "")) fl)
;;
