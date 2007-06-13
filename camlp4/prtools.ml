(* camlp4r *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Sformat;
open Pcaml.NewPrinter;

type pr_gfun 'a 'b = pr_ctx -> string -> 'a -> 'b -> string;

value shi ctx sh = {ind = ctx.ind + sh};
value tab ctx = String.make ctx.ind ' ';

(* horizontal list *)
value rec hlist elem ctx b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ctx b x k
  | [x :: xl] -> sprintf "%s %s" (elem ctx b x "") (hlist elem ctx "" xl k) ]
;

(* horizontal list with different function from 2nd element on *)
value rec hlist2 elem elem2 ctx b xl (k0, k) =
  match xl with
  [ [] -> invalid_arg "hlist2"
  | [x] -> elem ctx b x k
  | [x :: xl] ->
      sprintf "%s %s" (elem ctx b x k0) (hlist2 elem2 elem2 ctx "" xl
        (k0, k)) ]
;

(* horizontal list with different function for the last element *)
value rec hlistl elem eleml ctx b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> eleml ctx b x k
  | [x :: xl] ->
      sprintf "%s %s" (elem ctx b x "") (hlistl elem eleml ctx "" xl k) ]
;

(* vertical list *)
value rec vlist elem ctx b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ctx b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ctx b x "") (vlist elem ctx (tab ctx) xl k) ]
;

(* vertical list with different function from 2nd element on *)
value rec vlist2 elem elem2 ctx b xl (k0, k) =
  match xl with
  [ [] -> invalid_arg "vlist2"
  | [x] -> elem ctx b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ctx b x k0)
        (vlist2 elem2 elem2 ctx (tab ctx) xl (k0, k)) ]
;

(* vertical list with different function for the last element *)
value rec vlistl elem eleml ctx b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> eleml ctx b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ctx b x "")
        (vlistl elem eleml ctx (tab ctx) xl k) ]
;

value rise_string ctx sh b s =
  (* hack for "plistl" (below): if s is a "string" (i.e. starting with
     double-quote) which contains newlines, attempt to concat its first
     line in the previous line, and, instead of displaying this:
              eprintf
                "\
           hello, world"
     displays that:
              eprintf "\
           hello, world"
     what "saves" one line.
   *)
  let ind = ctx.ind in
  if String.length s > ind + sh && s.[ind+sh] = '"' then
    match try Some (String.index s '\n') with [ Not_found -> None ] with
    [ Some i ->
        let t = String.sub s (ind + sh) (String.length s - ind - sh) in
        let i = i - ind - sh in
        match
          horiz_vertic (fun () -> Some (sprintf "%s %s" b (String.sub t 0 i)))
            (fun () -> None)
        with
        [ Some b -> (b, String.sub t (i + 1) (String.length t - i - 1))
        | None -> (b, s) ]
    | None -> (b, s) ]
  else (b, s)
;

(* paragraph list with a different function for the last element;
   the list elements are pairs where second elements are separators
   (the last separator is ignored) *)
value rec plistl elem eleml sh ctx b xl k =
  let (s1, s2o) = plistl_two_parts elem eleml sh ctx b xl k in
  match s2o with
  [ Some s2 -> sprintf "%s\n%s" s1 s2
  | None -> s1 ]
and plistl_two_parts elem eleml sh ctx b xl k =
  match xl with
  [ [] -> assert False
  | [(x, _)] -> (eleml ctx b x k, None)
  | [(x, sep) :: xl] ->
      let s =
        horiz_vertic (fun () -> Some (elem ctx b x sep)) (fun () -> None)
      in
      match s with
      [ Some b -> (plistl_kont_same_line elem eleml sh ctx b xl k, None)
      | None ->
          let s1 = elem ctx b x sep in
          let s2 = plistl elem eleml 0 (shi ctx sh) (tab (shi ctx sh)) xl k in
          (s1, Some s2) ] ]
and plistl_kont_same_line elem eleml sh ctx b xl k =
  match xl with
  [ [] -> assert False
  | [(x, _)] ->
      horiz_vertic (fun () -> eleml ctx (sprintf "%s " b) x k)
        (fun () ->
           let s = eleml (shi ctx sh) (tab (shi ctx sh)) x k in
           let (b, s) = rise_string ctx sh b s in
           sprintf "%s\n%s" b s)
  | [(x, sep) :: xl] ->
      let s =
        horiz_vertic (fun () -> Some (elem ctx (sprintf "%s " b) x sep))
          (fun () -> None)
      in
      match s with
      [ Some b -> plistl_kont_same_line elem eleml sh ctx b xl k
      | None ->
          let (s1, s2o) =
            plistl_two_parts elem eleml 0 (shi ctx sh) (tab (shi ctx sh))
              [(x, sep) :: xl] k
          in
          match s2o with
          [ Some s2 ->
              let (b, s1) = rise_string ctx sh b s1 in
              sprintf "%s\n%s\n%s" b s1 s2
          | None -> sprintf "%s\n%s" b s1 ] ] ]
;

(* paragraph list *)
value plist elem sh ctx b xl k = plistl elem elem sh ctx b xl k;
