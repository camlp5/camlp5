(* camlp5r *)
(* pa_unmatched_vala.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";
#load "pa_extfun.cmo";

open Asttools;
open MLast;
open Pa_passthru ;
open Ppxutil ;

value is_unmatched_vala_branches l =
  let rec isrec = fun [
    [ (<:patt< [%unmatched_vala] >>, <:vala< None >>, _) :: _ ] -> True
  | [ _ :: t ] -> isrec t
  | [] -> False
  ] in
  isrec (List.rev l)
;

value sep_unmatched_vala_branch l =
  let rec seprec acc = fun [
    [] -> assert False
  | [ ((<:patt< [%unmatched_vala] >>, <:vala< None >>, _) as b) :: t ] -> (List.rev acc, b, t)
  | [ h :: t ] -> seprec [ h::acc ] t
  ] in
  seprec [] l
;

value is_orpat = fun [ <:patt< $_$ | $_$ >> -> True | _ -> False ] ;

value unpack_orpat p =
  let rec orec = fun [
    <:patt:< $a$ | $b$ >> -> (orec a) @ (orec b)
  | p -> [p]
  ] in
  orec p
;

value pack_orpat l = do {
  assert (l <> []) ;
  List.fold_left (fun a b -> let loc = loc_of_patt b in <:patt< $a$ | $b$ >>) (List.hd l) (List.tl l)
}
;

value strip_vars p =
  let rec strec = fun [
    <:patt:< $lid:_$ >> -> <:patt< _ >>
  | <:patt:< $a$ $b$ >> -> <:patt:< $strec a$ $strec b$ >>
  | <:patt:< $a$ | $b$ >> -> <:patt:< $strec a$ | $strec b$ >>
  | p -> p
  ] in
  strec p
;

value covers a b =
  let rec covrec = fun [
    (<:patt< $a1$ $b1$ >>, <:patt< $a2$ $b2$ >>) -> covrec (a1, a2) && covrec(b1, b2)
  | (<:patt< _ >>, p) -> True
  | (p, q) -> Reloc.eq_patt p q
  ] in
  covrec (a,b)
;

module HasVaVal = struct
  value rec patt = fun [
    <:patt< Ploc.VaVal $_$ >> -> True
  | <:patt< $a$ $b$ >> -> patt a || patt b
  | <:patt< MLast . $uid:_$  >> -> False
  | _ -> False
  ]
;
end
;

value rec has_vaval = fun [
  <:patt< $a$ | $b$ >> -> has_vaval a || has_vaval b
| p -> HasVaVal.patt p
]
;

value erase_vaval p = do {
  assert (not (is_orpat p)) ;
  let rec erec = fun [
    <:patt:< Ploc.VaVal $_$ >> -> <:patt< _ >>
  | <:patt:< $a$ $b$ >> -> <:patt< $(erec a)$ $(erec b)$ >>
  | p -> p
  ] in
  erec p
}
;

module PattSet = struct
  type t = list patt ;
  value mt = [] ;

  value norm p = do {
    assert (not (is_orpat p)) ;
    let p = strip_vars p in
    Reloc.patt (fun _ -> Ploc.dummy) 0 p };

  value mem p s =
    List.exists (fun covp -> covers covp p) s ;

  value add s p =
    let p = norm p in
    if mem p s then s else [ p :: s ] ;

end ;

value rewrite_unmatched_vala_branches branches = do {
  assert (is_unmatched_vala_branches branches) ;
  let (prefix, ((_, _, uvb_exp) as uvb), suffix) = sep_unmatched_vala_branch branches in
  let branchpats = List.map (fun (p, _, _) -> p) prefix in
  let branchpats = List.concat (List.map unpack_orpat branchpats) in

  let seen = List.fold_left PattSet.add PattSet.mt branchpats in
  let patll = List.map (fun p ->
      if has_vaval p then [strip_vars (erase_vaval p)] else []
   ) branchpats in
  let patl = List.concat patll in
  let (_,rev_patl) = List.fold_left (fun (seen,acc) p ->
      if PattSet.mem p seen then (seen, acc) else (PattSet.add seen p, [p :: acc]))
      (seen, []) patl in
  let patl = List.rev rev_patl in
  let newbranches = List.map (fun p -> (p, <:vala< None >>, uvb_exp)) patl in
  if patl = [] then prefix @ suffix
  else
(*
    let orpat = pack_orpat patl in
    prefix @ [ (orpat, <:vala< None >>, uvb_exp) ] @ suffix
*)
    prefix @ newbranches @ suffix
}
;

value rewrite_expr arg = fun [
  <:expr:< fun [ $list:l$ ] >> ->
  let l = rewrite_unmatched_vala_branches l in
  <:expr< fun [ $list:l$ ] >>
| <:expr:< match $e$ with [ $list:l$ ] >> ->
  let l = rewrite_unmatched_vala_branches l in
  <:expr< match $e$ with [ $list:l$ ] >>
| _ -> assert False
]
;

ef.val := EF.{ (ef.val) with
            expr = extfun ef.val.expr with [
    <:expr:< match $e$ with [ $list:branches$ ] >> as z
    when is_unmatched_vala_branches branches ->
    fun arg ->
      Some (rewrite_expr arg z)
  | <:expr:< fun [ $list:branches$ ] >> as z
    when is_unmatched_vala_branches branches ->
    fun arg ->
      Some (expr0 arg (rewrite_expr arg z))
  ] }
;

