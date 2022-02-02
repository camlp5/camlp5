(* camlp5r *)
(* q_regexp.ml,v *)

#load "q_MLast.cmo";

open Quotation ;
open Token_regexps ;

value export_dfa (init, initre, states) =
  let open PatternBaseToken in
  let loc = Ploc.dummy in
  let statename i = Printf.sprintf "q%04d" i in
  let token_pattern = fun [
        CLS s -> <:patt< Some (CLS $str:s$) >>
      | SPCL s -> <:patt< Some (SPCL $str:s$) >>
  ] in
  let export_state (i, rex, is_final, edges) =
    if is_final then
      (<:patt< $lid:(statename i)$ >>, <:expr< fun ofs -> Some ofs >>, <:vala< [] >>)
    else
      let branches =
        edges |> List.map (fun (tok, newst) ->
                     (token_pattern tok, <:vala< None >>, <:expr< $lid:(statename newst)$ (ofs+1) >>)
                   ) in
      let branches = branches @ [
            (<:patt< _ >>, <:vala< None >>, <:expr< None >>)
          ] in
      let rhs = <:expr< fun ofs ->
                        match must_peek_nth (ofs+1) strm with [
                            $list:branches$
                          ] >> in
      (<:patt< $lid:(statename i)$ >>, rhs, <:vala< [] >>) in
  let bindl = List.map export_state states in
  <:expr< fun strm ->
    let open Token_regexps in
    let open PatternBaseToken in
    let must_peek_nth n strm =
      let l = Stream.npeek n strm in
        if List.length l = n then
          convert_token (fst(sep_last l))
        else None in
    let rec $list:bindl$ in $lid:(statename init)$ 0 >>
;

value expand_expr txt =
  let rex = parse txt in
  let module C = Compile(struct value rex = rex ; value extra = [] ; end) in
  let dfa = C.dfa in
  let export = C.BEval.export dfa in
  export_dfa export
;

value expand_patt txt =
  failwith Fmt.(str "Q_regexp: cannot expand quotation in a pattern position: %a" Dump.string txt)
;

Quotation.add "regexp" (ExAst (expand_expr,expand_patt)) ;
