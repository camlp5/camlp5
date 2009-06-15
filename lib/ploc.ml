(* camlp5r *)
(* $Id: ploc.ml,v 1.3 2007/09/17 10:22:31 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

type t =
  { line_nb : int;
    bol_pos : int;
    bp : int;
    ep : int }
;

value make line_nb bol_pos (bp, ep) =
  {line_nb = line_nb; bol_pos = bol_pos; bp = bp; ep = ep}
;

value make_unlined (bp, ep) = {line_nb = -1; bol_pos = 0; bp = bp; ep = ep};

value dummy = {line_nb = -1; bol_pos = 0; bp = 0; ep = 0};

value first_pos loc = loc.bp;
value last_pos loc = loc.ep;
value line_nb loc = loc.line_nb;
value bol_pos loc = loc.bol_pos;

value encl loc1 loc2 =
  {(loc1) with bp = min loc1.bp loc2.bp; ep = max loc1.ep loc2.ep}
;
value shift sh loc = {(loc) with bp = sh + loc.bp; ep = sh + loc.ep};
value sub loc sh len = {(loc) with bp = loc.bp + sh; ep = loc.bp + sh + len};
value after loc sh len =
  {(loc) with bp = loc.ep + sh; ep = loc.ep + sh + len}
;

value name = ref "loc";

value from_file fname loc =
  let (bp, ep) = (first_pos loc, last_pos loc) in
  try
    let ic = open_in_bin fname in
    let strm = Stream.of_channel ic in
    let rec loop fname lin =
      let rec not_a_line_dir col =
        parser cnt
          [: `c; s :] ->
            if cnt < bp then
              if c = '\n' then loop fname (lin + 1)
              else not_a_line_dir (col + 1) s
            else
              let col = col - (cnt - bp) in
              (fname, lin, col, col + ep - bp)
      in
      let rec a_line_dir str n col =
        parser
        [ [: `'\n' :] -> loop str n
        | [: `_; s :] -> a_line_dir str n (col + 1) s ]
      in
      let rec spaces col =
        parser
        [ [: `' '; s :] -> spaces (col + 1) s
        | [: :] -> col ]
      in
      let rec check_string str n col =
        parser
        [ [: `'"'; col = spaces (col + 1); s :] -> a_line_dir str n col s
        | [: `c when c <> '\n'; s :] ->
            check_string (str ^ String.make 1 c) n (col + 1) s
        | [: a = not_a_line_dir col :] -> a ]
      in
      let check_quote n col =
        parser
        [ [: `'"'; s :] -> check_string "" n (col + 1) s
        | [: a = not_a_line_dir col :] -> a ]
      in
      let rec check_num n col =
        parser
        [ [: `('0'..'9' as c); s :] ->
            check_num (10 * n + Char.code c - Char.code '0') (col + 1) s
        | [: col = spaces col; s :] -> check_quote n col s ]
      in
      let begin_line =
        parser
        [ [: `'#'; col = spaces 1; s :] -> check_num 0 col s
        | [: a = not_a_line_dir 0 :] -> a ]
      in
      begin_line strm
    in
    let r = try loop fname 1 with [ Stream.Failure -> (fname, 1, bp, ep) ] in
    do { close_in ic; r }
  with
  [ Sys_error _ -> (fname, 1, bp, ep) ]
;

value call_with r v f a =
  let saved = r.val in
  try do {
    r.val := v;
    let b = f a in
    r.val := saved;
    b
  }
  with e -> do { r.val := saved; raise e }
;

exception Exc of t and exn;

value raise loc exc =
  match exc with
  [ Exc _ _ -> raise exc
  | _ -> raise (Exc loc exc) ]
;

type vala 'a =
  [ VaAnt of string
  | VaVal of 'a ]
;
