(* camlp5r *)
(* $Id: eprinter.ml,v 1.1 2007/08/15 15:44:25 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

type t 'a =
  { pr_fun : mutable string -> pr_fun 'a;
    pr_levels : mutable list (pr_level 'a) }
and pr_level 'a = { pr_label : string; pr_rules : mutable pr_rule 'a }
and pr_rule 'a =
  Extfun.t 'a
    (pr_fun 'a -> pr_fun 'a -> pr_context string string -> string)
and pr_fun 'a = pr_context string string -> 'a -> string
and pr_context 'bef 'aft =
  { ind : int;
    bef : 'bef;
    aft : 'aft;
    dang : string }
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

value extend_printer lpplr =
  List.iter
    (fun (pr, pos, levs) ->
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
                         let levs =
                           List.fold_right add_lev levs pr_levs
                         in
                         [lev :: levs]
                     | [] -> [pr_lev :: pr_levs] ]
                   else [pr_lev :: loop pr_levs]
               | [] -> failwith ("level " ^ lab ^ " not found") ]
           in
           pr.pr_levels := levels
       | Some _ ->
           failwith
             "not impl EXTEND_PRINTER entry with at level parameter" ])
    lpplr
;
