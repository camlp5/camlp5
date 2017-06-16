(* camlp5r *)
(* eprinter.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)

type 'a t =
  { pr_name : string;
    mutable pr_fun : string -> 'a pr_fun;
    mutable pr_levels : 'a pr_level list }
and 'a pr_level = { pr_label : string; mutable pr_rules : 'a pr_rule }
and 'a pr_rule = ('a, 'a pr_fun -> 'a pr_fun -> pr_context -> string) Extfun.t
and 'a pr_fun = pr_context -> 'a -> string
and pr_context =
  Pprintf.pr_context =
    { ind : int; bef : string; aft : string; dang : string }
;;

type position =
    First
  | Last
  | Before of string
  | After of string
  | Level of string
;;

let add_lev (lab, extf) levs =
  let lab =
    match lab with
      Some lab -> lab
    | None -> ""
  in
  let lev = {pr_label = lab; pr_rules = extf Extfun.empty} in lev :: levs
;;

let with_pr_rules lev pr_rules =
  {pr_label = lev.pr_label; pr_rules = pr_rules}
;;

let extend pr pos levs =
  match pos with
    None ->
      let levels = List.fold_right add_lev levs pr.pr_levels in
      pr.pr_levels <- levels
  | Some (Level lab) ->
      let levels =
        let rec loop =
          function
            pr_lev :: pr_levs ->
              if lab = pr_lev.pr_label then
                match levs with
                  (_, extf) :: levs ->
                    let lev = with_pr_rules pr_lev (extf pr_lev.pr_rules) in
                    let levs = List.fold_right add_lev levs pr_levs in
                    lev :: levs
                | [] -> pr_lev :: pr_levs
              else pr_lev :: loop pr_levs
          | [] -> failwith ("level " ^ lab ^ " not found")
        in
        loop pr.pr_levels
      in
      pr.pr_levels <- levels
  | Some (After lab) ->
      let levels =
        let rec loop =
          function
            pr_lev :: pr_levs ->
              if lab = pr_lev.pr_label then
                let pr_levs = List.fold_right add_lev levs pr_levs in
                pr_lev :: pr_levs
              else pr_lev :: loop pr_levs
          | [] -> failwith ("level " ^ lab ^ " not found")
        in
        loop pr.pr_levels
      in
      pr.pr_levels <- levels
  | Some (Before lab) ->
      let levels =
        let rec loop =
          function
            pr_lev :: pr_levs ->
              if lab = pr_lev.pr_label then
                List.fold_right add_lev levs (pr_lev :: pr_levs)
              else pr_lev :: loop pr_levs
          | [] -> failwith ("level " ^ lab ^ " not found")
        in
        loop pr.pr_levels
      in
      pr.pr_levels <- levels
  | Some _ -> failwith "not impl EXTEND_PRINTER entry with at level parameter"
;;

let pr_fun name pr lab =
  let rec loop app =
    function
      [] ->
        (fun pc z ->
           failwith
             (Printf.sprintf
                "cannot print %s%s; a missing case in camlp5; please report"
                name (if lab = "" then "" else " \"" ^ lab ^ "\"")))
    | lev :: levl ->
        if lab = "" || app || lev.pr_label = lab then
          let next = loop true levl in
          let rec curr pc z = Extfun.apply lev.pr_rules z curr next pc in curr
        else loop app levl
  in
  loop false pr.pr_levels
;;

let make name =
  let pr =
    {pr_name = name;
     pr_fun = (fun _ -> raise (Match_failure ("eprinter.ml", 112, 37)));
     pr_levels = []}
  in
  pr.pr_fun <- pr_fun name pr; pr
;;

let clear pr = pr.pr_levels <- []; pr.pr_fun <- pr_fun pr.pr_name pr;;

let apply_level pr lname pc z = pr.pr_fun lname pc z;;
let apply pr pc z = pr.pr_fun "" pc z;;

let print pr =
  List.iter
    (fun lev ->
       Printf.printf "level \"%s\"\n" lev.pr_label;
       Extfun.print lev.pr_rules;
       flush stdout)
    pr.pr_levels
;;
