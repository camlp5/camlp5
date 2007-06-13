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
      sprintf "%s %s" (elem ctx b x k0)
        (hlist2 elem2 elem2 ctx "" xl (k0, k)) ]
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

(* comments *)

module Buff =
  struct
    value buff = ref (String.create 80);
    value store len x = do {
      if len >= String.length buff.val then
        buff.val := buff.val ^ String.create (String.length buff.val)
      else ();
      buff.val.[len] := x;
      succ len
    };
    value mstore len s =
      add_rec len 0 where rec add_rec len i =
        if i == String.length s then len
        else add_rec (store len s.[i]) (succ i)
    ;
    value get len = String.sub buff.val 0 len;
  end
;

value rev_extract_comment strm =
  let rec find_comm len =
    parser
    [ [: `' '; a = find_comm (Buff.store len ' ') :] -> a
    | [: `'\t'; a = find_comm (Buff.mstore len (String.make 8 ' ')) :] -> a
    | [: `'\n'; a = find_comm (Buff.store len '\n') :] -> a
    | [: `')'; a = find_star_bef_rparen (Buff.store len ')') :] -> a
    | [: :] -> 0 ]
  and find_star_bef_rparen len =
    parser
    [ [: `'*'; a = insert (Buff.store len '*') :] -> a
    | [: :] -> 0 ]
  and insert len =
    parser
    [ [: `')'; a = find_star_bef_rparen_in_comm (Buff.store len ')') :] -> a
    | [: `'*'; a = find_lparen_aft_star (Buff.store len '*') :] -> a
    | [: `x; a = insert (Buff.store len x) :] -> a
    | [: :] -> len ]
  and find_star_bef_rparen_in_comm len =
    parser
    [ [: `'*'; len = insert (Buff.store len '*'); s :] -> insert len s
    | [: a = insert len :] -> a ]
  and find_lparen_aft_star len =
    parser
    [ [: `'('; a = while_space (Buff.store len '(') :] -> a
    | [: a = insert len :] -> a ]
  and while_space len =
    parser
    [ [: `' '; a = while_space (Buff.store len ' ') :] -> a
    | [: `'\t'; a = while_space (Buff.mstore len (String.make 8 ' ')) :] -> a
    | [: `'\n'; a = while_space (Buff.store len '\n') :] -> a
    | [: `')'; a = find_star_bef_rparen_again len :] -> a
    | [: :] -> len ]
  and find_star_bef_rparen_again len =
    parser
    [ [: `'*'; a = insert (Buff.mstore len ")*") :] -> a
    | [: :] -> len ]
  in
  let len = find_comm 0 strm in
  let s = Buff.get len in
  loop (len - 1) 0 0 where rec loop i nl_bef ind_bef =
    if i <= 0 then ("", 0, 0)
    else if s.[i] = '\n' then loop (i - 1) (nl_bef + 1) ind_bef
    else if s.[i] = ' ' then loop (i - 1) nl_bef (ind_bef + 1)
    else do {
      let s = String.sub s 0 (i + 1) in
      for i = 0 to String.length s / 2 - 1 do {
        let t = s.[i] in
        s.[i] := s.[String.length s - i - 1];
        s.[String.length s - i - 1] := t;
      };
      (s, nl_bef, ind_bef)
    }
;

value source = ref "";

value rev_read_comment_in_file bp ep =
  let strm =
    Stream.from
      (fun i ->
         let j = bp - i - 1 in
         if j < 0 || j >= String.length source.val then None
         else Some source.val.[j])
  in
  rev_extract_comment strm
;

value adjust_comment_indentation ind s nl_bef ind_bef =
  if s = "" then ""
  else
    let (ind_aft, i_bef_ind) =
      loop 0 (String.length s - 1) where rec loop ind_aft i =
        if i >= 0 && s.[i] = ' ' then loop (ind_aft + 1) (i - 1)
        else (ind_aft, i)
    in
    let ind_bef = if nl_bef > 0 then ind_bef else ind in
    let len = i_bef_ind + 1 in
    let olen = Buff.mstore 0 (String.make ind ' ') in
    loop olen 0 where rec loop olen i =
      if i = len then Buff.get olen
      else
        let olen = Buff.store olen s.[i] in
        let (olen, i) =
          if s.[i] = '\n' && (i + 1 = len || s.[i + 1] <> '\n') then
            let delta_ind = if i = i_bef_ind then 0 else ind - ind_bef in
            if delta_ind >= 0 then
              (Buff.mstore olen (String.make delta_ind ' '), i + 1)
            else
              let i =
                loop delta_ind (i + 1) where rec loop cnt i =
                  if cnt = 0 then i
                  else if i = len then i
                  else if s.[i] = ' ' then loop (cnt + 1) (i + 1)
                  else i
              in
              (olen, i)
          else (olen, i + 1)
        in
        loop olen i
;

value comm_bef ctx loc =
  let ind = ctx.ind in
  let bp = Stdpp.first_pos loc in
  let ep = Stdpp.last_pos loc in
  let (s, nl_bef, ind_bef) = rev_read_comment_in_file bp ep in
  adjust_comment_indentation ind s nl_bef ind_bef
;
