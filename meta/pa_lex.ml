(* camlp4r *)
(* $Id$ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;

(**)
value var = "buf";
value add_char loc c cl = <:expr< B.add $cl$ $c$ >>;
value get_buf loc cl = <:expr< B.get $cl$ >>;
(*
value var = "cl";
value add_char loc c cl = <:expr< [$c$ :: $cl$] >>;
value get_buf loc cl = cl;
*)

value fresh_c cl =
  let n =
    List.fold_left
      (fun n c ->
         match c with
         [ <:expr< $lid:_$ >> -> n + 1
         | _ -> n ])
      0 cl
  in
  if n = 0 then "c" else "c" ^ string_of_int n
;

value accum_chars loc cl =
  List.fold_right (add_char loc) cl <:expr< $lid:var$ >>
;

value mk_parser loc rl =
  let rl =
    List.map
      (fun (sl, cl, a) ->
         let a =
           let b = accum_chars loc cl in
           match a with
           [ Some e ->
               let loc = MLast.loc_of_expr e in
               <:expr< let lexbuf = $get_buf loc b$ in $e$ >>
           | None -> b ]
         in
         (List.rev sl, None, a))
      rl
  in
  Exparser.cparser loc None rl
;

EXTEND
  GLOBAL: expr;
  expr:
    [ [ "lexer"; rl = rules ->
          <:expr< fun $lid:var$ -> $mk_parser loc rl$ >> ] ]
  ;
  rules:
    [ [ "["; rl = LIST0 rule SEP "|"; "]" -> rl ] ]
  ;
  rule:
    [ [ (sl, cl) = symbs; a = act -> (sl, cl, a) ] ]
  ;
  symbs:
    [ [ (sl, cl) = symbs; c = CHAR ->
          let s = (Exparser.SpTrm loc <:patt< $chr:c$ >> None, None) in
          ([s :: sl], [<:expr< $chr:c$ >> :: cl])
      | (sl, cl) = symbs; c = CHAR; "/" ->
          let s = (Exparser.SpTrm loc <:patt< $chr:c$ >> None, None) in
          ([s :: sl], cl)
      | (sl, cl) = symbs; c1 = CHAR; ".."; c2 = CHAR; errk = err_kont ->
          let c = fresh_c cl in
          let s =
            let p = <:patt< ($chr:c1$ .. $chr:c2$ as $lid:c$) >> in
            (Exparser.SpTrm loc p None, errk)
          in
          ([s :: sl], [<:expr< $lid:c$ >> :: cl])
      | (sl, cl) = symbs; f = simple_expr; errk = err_kont ->
          let s =
            let buf = accum_chars loc cl in
            let e = <:expr< $f$ $buf$ >> in
            (Exparser.SpNtr loc <:patt< $lid:var$ >> e, errk)
          in
          ([s :: sl], [])
      | (sl, cl) = symbs; "?="; "["; pll = LIST1 lookahead SEP "|"; "]";
        errk = err_kont ->
          let s = (Exparser.SpLhd loc pll, errk) in
          ([s :: sl], cl)
      | (sl, cl) = symbs; rl = rules; errk = err_kont ->
          let sl =
            if cl = [] then sl
            else
              let s =
                let b = accum_chars loc cl in
                let e = <:expr< fun (strm__ : Stream.t _) -> $b$ >> in
                (Exparser.SpNtr loc <:patt< $lid:var$ >> e, Some None)
              in
              [s :: sl]
          in
          let s =
            let e = mk_parser loc rl in
            (Exparser.SpNtr loc <:patt< $lid:var$ >> e, errk)
          in
          ([s :: sl], [])
      | -> ([], []) ] ]
  ;
  simple_expr:
    [ [ i = LIDENT -> <:expr< $lid:i$ >>
      | "("; e = expr; ")" -> e ] ]
  ;
  lookahead:
    [ [ pl = LIST1 lookahead_char -> pl ] ]
  ;
  lookahead_char:
    [ [ c = CHAR -> <:patt< $chr:c$ >>
      | "_" -> <:patt< _ >> ] ]
  ;
  err_kont:
    [ [ "!" -> Some None
      | "?"; s = STRING -> Some (Some <:expr< $str:s$ >>)
      | -> None ] ]
  ;
  act:
    [ [ "->"; e = expr -> Some e
      | -> None ] ]
  ;
END;
