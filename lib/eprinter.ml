(* camlp5r *)
(* eprinter.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";

type t 'a =
  { pr_name : string;
    pr_fail : 'a -> string;
    pr_fun : mutable string -> pr_fun 'a;
    pr_levels : mutable list (pr_level 'a) }
and pr_level 'a = { pr_label : string; pr_rules : mutable pr_rule 'a }
and pr_rule 'a =
  Extfun.t 'a (pr_fun 'a -> pr_fun 'a -> pr_fun 'a -> (~fail:(unit -> string) -> pr_fun 'a) -> pr_context -> string)
and pr_fun 'a = pr_context -> 'a -> string
and pr_context =
  Pprintf.pr_context ==
    { ind : int; bef : string; aft : string; dang : string }
;

type position =
  [ First
  | Last
  | Before of string
  | After of string
  | Level of string ]
;

value add_lev (lab, extf) levs =
  let lab =
    match lab with
    [ Some lab -> lab
    | None -> "" ]
  in
  let lev = {pr_label = lab; pr_rules = extf Extfun.empty} in
  [lev :: levs]
;

value extend pr pos levs =
  match pos with
  [ None ->
      let levels = List.fold_right add_lev levs pr.pr_levels in
      pr.pr_levels := levels
  | Some (Level lab) ->
      let levels =
        loop pr.pr_levels where rec loop =
          fun
          [ [pr_lev :: pr_levs] ->
              if lab = pr_lev.pr_label then
                match levs with
                [ [(_, extf) :: levs] ->
                    let lev =
                      {(pr_lev) with pr_rules = extf pr_lev.pr_rules}
                    in
                    let levs = List.fold_right add_lev levs pr_levs in
                    [lev :: levs]
                | [] -> [pr_lev :: pr_levs] ]
              else [pr_lev :: loop pr_levs]
          | [] -> failwith ("level " ^ lab ^ " not found") ]
      in
      pr.pr_levels := levels
  | Some (After lab) ->
      let levels =
        loop pr.pr_levels where rec loop =
          fun
          [ [pr_lev :: pr_levs] ->
              if lab = pr_lev.pr_label then
                let pr_levs = List.fold_right add_lev levs pr_levs in
                [pr_lev :: pr_levs]
              else [pr_lev :: loop pr_levs]
          | [] -> failwith ("level " ^ lab ^ " not found") ]
      in
      pr.pr_levels := levels
  | Some (Before lab) ->
      let levels =
        loop pr.pr_levels where rec loop =
          fun
          [ [pr_lev :: pr_levs] ->
              if lab = pr_lev.pr_label then
                List.fold_right add_lev levs [pr_lev :: pr_levs]
              else [pr_lev :: loop pr_levs]
          | [] -> failwith ("level " ^ lab ^ " not found") ]
      in
      pr.pr_levels := levels
  | Some _ ->
      failwith "not impl EXTEND_PRINTER entry with at level parameter" ]
;

value rec pr_fun name pr lab0 pc z =
  let rec top prev pc z = loop "" False pr.pr_levels pc (prev, z)
  and bottom lab prev ~{fail: unit -> string} pc z =
    if prev = Some z then 
          fail ()
    else top (Some z) pc z
  and loop lab app levl pc (prev, z) =
    match levl with
    [ [] ->
          failwith
            (Printf.sprintf
               "cannot print %s%s; a missing case in camlp5; please report\n%s"
               name (if lab = "" then "" else " \"" ^ lab ^ "\"")
               (pr.pr_fail z))
    | [lev :: levl] ->
        if lab = "" || app || lev.pr_label = lab then
          let next pc z = loop lab True levl pc (prev, z) in
          curr pc z where rec curr pc z =
            Extfun.apply lev.pr_rules z curr next (top None) (bottom lab prev) pc
        else loop lab app levl pc (prev, z) ]
  in loop lab0 False pr.pr_levels pc (None, z)
;

value make ?{fail} name = do {
  let fail = match fail with [ None -> fun _ -> "<"^name^">" | Some f -> f ] in
  let pr = {pr_name = name; pr_fail = fail; pr_fun = fun []; pr_levels = []} in
  pr.pr_fun := pr_fun name pr;
  pr
};

value clear pr = do {
  pr.pr_levels := [];
  pr.pr_fun := pr_fun pr.pr_name pr;
};

value apply_level pr lname pc z = pr.pr_fun lname pc z;
value apply pr pc z = pr.pr_fun "" pc z;

value print pr =
  List.iter
    (fun lev -> do {
       Printf.printf "level \"%s\"\n" lev.pr_label;
       Extfun.print lev.pr_rules;
       flush stdout;
     })
    pr.pr_levels
;
