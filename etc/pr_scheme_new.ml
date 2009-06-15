(* camlp5r q_MLast.cmo ./pa_extprint.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Pretty;
open Pcaml;
open Prtools;

do {
  Eprinter.clear pr_expr;
  Eprinter.clear pr_patt;
(*
  Eprinter.clear pr_ctyp;
*)
  Eprinter.clear pr_str_item;
  Eprinter.clear pr_sig_item;
(*
  Eprinter.clear pr_module_expr;
  Eprinter.clear pr_module_type;
  Eprinter.clear pr_class_sig_item;
  Eprinter.clear pr_class_str_item;
  Eprinter.clear pr_class_expr;
  Eprinter.clear pr_class_type;
*)
};

(* general functions *)

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_scheme_new, not impl: %s; %s\"%s" pc.bef name
    (String.escaped desc) pc.aft
;

value rec mod_ident pc sl =
  match sl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [s] -> sprintf "%s%s%s" pc.bef s pc.aft
  | [s :: sl] -> mod_ident {(pc) with bef = sprintf "%s%s." pc.bef s} sl ]
;

(*
 * Extensible printers
 *)

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
(*
value ctyp = Eprinter.apply pr_ctyp;
*)
value str_item = Eprinter.apply pr_str_item;
value sig_item = Eprinter.apply pr_sig_item;
(*
value module_expr = Eprinter.apply pr_module_expr;
value module_type = Eprinter.apply pr_module_type;
value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;
*)

value match_assoc pc (p, we, e) =
  horiz_vertic
    (fun () ->
       let s1 =
         let pc = {(pc) with bef = sprintf "%s(" pc.bef; aft = ""} in
         match we with
         [ <:vala< Some e >> -> not_impl "match_assoc 1" pc 0
         | _ -> patt pc p ]
       in
       let s2 = expr {(pc) with bef = ""; aft = sprintf ")%s" pc.aft} e in
       sprintf "%s %s" s1 s2)
    (fun () ->
       let s1 =
         let pc =
           {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef; aft = ""}
         in
         match we with
         [ <:vala< Some e >> ->
             horiz_vertic
               (fun () ->
                  sprintf "%s(when %s %s)" pc.bef
                    (patt {(pc) with bef = ""} p)
                    (expr {(pc) with bef = ""} e))
               (fun () ->
                  let s1 =
                    horiz_vertic
                      (fun () ->
                         sprintf "%s(when %s" pc.bef
                           (patt {(pc) with bef = ""} p))
                      (fun () -> not_impl "match_assoc 2" pc 0)
                  in
                  let s2 =
                    expr
                      {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                       aft = ")"}
                      e
                  in
                  sprintf "%s\n%s" s1 s2)
         | _ ->
             patt pc p ]
       in
       let s2 =
         expr
           {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
            aft = sprintf ")%s" pc.aft}
           e
       in
       sprintf "%s\n%s" s1 s2)
;

EXTEND_PRINTER
  pr_expr:
    [ "top"
      [ (* <:expr< fun [] >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(lambda%t" (ks ")" k)
      | *) <:expr< fun $lid:s$ -> $e$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(lambda %s %s)%s" pc.bef s
                 (curr {(pc) with bef = ""; aft = ""} e) pc.aft)
            (fun () ->
               let s1 =
                 horiz_vertic
                   (fun () -> sprintf "%s(lambda %s" pc.bef s)
                   (fun () -> not_impl "fun1 vertic" pc 0)
               in
               let s2 =
                 curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   e
               in
               sprintf "%s\n%s" s1 s2)
      | <:expr< fun [ $list:pwel$ ] >> ->
          horiz_vertic (fun () -> sprintf "\n")
            (fun () ->
               let s1 = sprintf "%s(lambda_match" pc.bef in
               let s2 =
                 vlist match_assoc
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   pwel
               in
               sprintf "%s\n%s" s1 s2)
(*
      | <:expr< match $e$ with [ $list:pwel$ ] >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[<hv>@[<b 2>match@ %a@]@ %a@]" expr (e, nok)
              (list match_assoc) (pwel, ks ")" k)
*)
      | <:expr< try $e$ with [ $list:pwel$ ] >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(try %s %s)%s" pc.bef
                 (curr {(pc) with bef = ""; aft = ""} e)
                 (hlist match_assoc {(pc) with bef = ""; aft = ""} pwel)
                 pc.aft)
            (fun () ->
               let s1 =
                 horiz_vertic
                   (fun () ->
                      sprintf "%s(try %s" pc.bef
                        (curr {(pc) with bef = ""; aft = ""} e))
                   (fun () -> not_impl "try vertic" pc 0)
               in
               let s2 =
                 let pc =
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1)}
                 in
                 vlist match_assoc {(pc) with aft = sprintf ")%s" pc.aft} pwel
               in
               sprintf "%s\n%s" s1 s2)
      | <:expr< let $flag:rf$ $p1$ = $e1$ in $e2$ >> ->
          let b = if rf then "letrec" else "let" in
          horiz_vertic
            (fun () ->
               sprintf "%s(%s ((%s %s) %s))%s" pc.bef b
                 (patt {(pc) with bef = ""; aft = ""} p1)
                 (curr {(pc) with bef = ""; aft = ""} e1)
                 (curr {(pc) with bef = ""; aft = ""} e2) pc.aft)
            (fun () ->
               let s1 =
                 horiz_vertic
                   (fun () ->
                      sprintf "%s(%s ((%s %s))" pc.bef b
                        (patt {(pc) with bef = ""; aft = ""} p1)
                        (curr {(pc) with bef = ""; aft = ""} e1))
                   (fun () ->
                      let s1 = sprintf "%s(%s" pc.bef b in
                      let s2 =
                        let pc =
                          {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1)}
                        in
                        horiz_vertic
                          (fun () ->
                             sprintf "%s((%s %s))" pc.bef
                               (patt {(pc) with bef = ""; aft = ""} p1)
                               (curr {(pc) with bef = ""; aft = ""} e1))
                          (fun () ->
                             let s1 =
                               sprintf "%s((%s" pc.bef
                                 (patt {(pc) with bef = ""; aft = ""} p1)
                             in
                             let s2 =
                               sprintf "%s))"
                                 (curr
                                    {(pc) with ind = pc.ind + 2;
                                     bef = tab (pc.ind + 2); aft = ""}
                                    e1)
                             in
                             sprintf "%s\n%s" s1 s2)
                      in
                      sprintf "%s\n%s" s1 s2)
               in
               let s2 =
                 curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   e2
               in
               sprintf "%s\n%s" s1 s2)
      | <:expr< let $flag:rf$ $list:pel$ in $e$ >> ->
          horiz_vertic (fun () -> not_impl "let2 vertic" pc 0)
            (fun () -> not_impl "let2 vertic" pc 0)
      | <:expr< if $e1$ then $e2$ else () >> ->
          not_impl "if else ()" pc 0
      | <:expr< if $e1$ then $e2$ else $e3$ >> ->
          horiz_vertic
            (fun () ->
               let pc1 = {(pc) with bef = ""; aft = ""} in
               sprintf "%s(if %s %s %s)%s" pc.bef (curr pc1 e1) (curr pc1 e2)
                 (curr pc1 e3) pc.aft)
            (fun () ->
               let s1 =
                 horiz_vertic
                   (fun () ->
                      sprintf "%s(if %s" pc.bef
                        (curr {(pc) with bef = ""; aft = ""} e1))
                    (fun () -> not_impl "if else ... vertic" pc 0)
               in
               let s2 =
                 curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = ""}
                   e2
               in
               let s3 =
                 curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   e3
               in
               sprintf "%s\n%s\n%s" s1 s2 s3)
      | <:expr< do { $list:el$ } >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(begin %s)%s" pc.bef
                 (hlist curr {(pc) with bef = ""; aft = ""} el) pc.aft)
            (fun () ->
               let s1 = sprintf "%s(begin" pc.bef in
               let s2 =
                 vlist curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   el
               in
               sprintf "%s\n%s" s1 s2)
(*
      | <:expr< for $lid:i$ = $e1$ to $e2$ do { $list:el$ } >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[for %s@ %a@ %a %a@]" i expr (e1, nok)
              expr (e2, nok) (list expr) (el, ks ")" k)
      | <:expr< ($e$ : $t$) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(:@ %a@ %a" expr (e, nok) ctyp (t, ks ")" k)
      | <:expr< ($list:el$) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(values @[%a@]" (list expr) (el, ks ")" k)
      | <:expr< { $list:fel$ } >> ->
          fun ppf curr next dg k ->
            let record_binding ppf ((p, e), k) =
              fprintf ppf "(@[%a@ %a@]" patt (p, nok) expr (e, ks ")" k)
            in
            fprintf ppf "{@[<hv>%a@]" (list record_binding) (fel, ks "}" k)
      | <:expr< { ($e$) with $list:fel$ } >> ->
          fun ppf curr next dg k ->
            let record_binding ppf ((p, e), k) =
              fprintf ppf "(@[%a@ %a@]" patt (p, nok) expr (e, ks ")" k)
            in
            fprintf ppf "{@[@[with@ %a@]@ @[%a@]@]" expr (e, nok)
              (list record_binding) (fel, ks "}" k)
      | <:expr< $e1$ := $e2$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(:=@;<1 1>%a@;<1 1>%a" expr (e1, nok)
              expr (e2, ks ")" k)
*)
      | <:expr< [$_$ :: $_$] >> as e ->
          let (el, c) =
            make_list e where rec make_list e =
              match e with
              [ <:expr< [$e$ :: $y$] >> ->
                  let (el, c) = make_list y in
                  ([e :: el], c)
              | <:expr< [] >> -> ([], None)
              | x -> ([], Some e) ]
          in
          let pc =
            {(pc) with bef = sprintf "%s[" pc.bef; aft = sprintf "]%s" pc.aft}
          in
          match c with
          [ None ->
              let el = List.map (fun e -> (e, "")) el in
              plist curr 1 pc el
          | Some x ->
              let dot_expr pc e =
                curr {(pc) with bef = sprintf "%s. " pc.bef} e
              in
              horiz_vertic
                (fun () -> hlistl curr dot_expr pc (el @ [x]))
                (fun () -> not_impl "expr list 2 vertic" pc 0) ]
(*
      | <:expr< lazy ($x$) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[lazy@ %a@]" expr (x, ks ")" k)
      | <:expr< $lid:s$ $e1$ $e2$ >>
        when List.mem s assoc_right_parsed_op_list ->
          fun ppf curr next dg k ->
            let el =
              loop [e1] e2 where rec loop el =
                fun
                [ <:expr< $lid:s1$ $e1$ $e2$ >> when s1 = s ->
                    loop [e1 :: el] e2
                | e -> List.rev [e :: el] ]
            in
            fprintf ppf "(@[%s %a@]" s (list expr) (el, ks ")" k)
*)
      | <:expr< $e1$ $e2$ >> ->
          let el =
            loop [e2] e1 where rec loop el =
              fun
              [ <:expr< $e1$ $e2$ >> -> loop [e2 :: el] e1
              | e1 -> [e1 :: el] ]
          in
          let el = List.map (fun e -> (e, "")) el in
          plist curr 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            el
(*
      | <:expr< ~$s$: ($e$) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(~%s@ %a" s expr (e, ks ")" k)
      | <:expr< $e1$ .[ $e2$ ] >> ->
          fun ppf curr next dg k ->
            fprintf ppf "%a.[%a" expr (e1, nok) expr (e2, ks "]" k)
      | <:expr< $e1$ .( $e2$ ) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "%a.(%a" expr (e1, nok) expr (e2, ks ")" k)
*)
      | <:expr< $e1$ . $e2$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s%s.%s%s" pc.bef
                 (curr {(pc) with bef = ""; aft = ""} e1)
                 (curr {(pc) with bef = ""; aft = ""} e2) pc.aft)
            (fun () -> not_impl "expr dot vertic" pc 0)
      | <:expr< $int:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $lid:s$ >> | <:expr< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
(*
      | <:expr< ` $s$ >> ->
          fun ppf curr next dg k -> fprintf ppf "`%s%t" s k
*)
      | <:expr< $str:s$ >> ->
          sprintf "%s\"%s\"%s" pc.bef s pc.aft
      | <:expr< $chr:s$ >> ->
          sprintf "%s'%s'%s" pc.bef s pc.aft
      | x ->
          not_impl "expr" pc x ] ]
  ;
  pr_patt:
    [ "top"
      [ <:patt< $p1$ | $p2$ >> ->
          let pl =
            loop [p2] p1 where rec loop pl =
              fun
              [ <:patt< $p1$ | $p2$ >> -> loop [p2 :: pl] p1
              | p1 -> [p1 :: pl] ]
          in
          let pl = List.map (fun p -> (p, "")) pl in
          plistb curr 1
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(or" pc.bef;
             aft = sprintf ")%s" pc.aft}
            pl
      | <:patt< ($p1$ as $p2$) >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(as %s %s)%s" pc.bef
                 (curr {(pc) with bef = ""; aft = ""} p1)
                 (curr {(pc) with bef = ""; aft = ""} p2) pc.aft)
            (fun () ->
               let s1 =
                 horiz_vertic
                   (fun () ->
                      sprintf "%s(as %s" pc.bef
                        (curr {(pc) with bef = ""; aft = ""} p1))
                   (fun () ->
                      let s1 = sprintf "%s(as" pc.bef in
                      let s2 =
                        curr
                          {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                           aft = ""} p1
                      in
                      sprintf "%s\n%s" s1 s2)
               in
               let s2 =
                 curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   p2
               in
               sprintf "%s\n%s" s1 s2)
(*
      | <:patt< $p1$ .. $p2$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[range@ %a@ %a@]" patt (p1, nok) patt
              (p2, ks ")" k)
      | <:patt< [$_$ :: $_$] >> as p ->
          fun ppf curr next dg k ->
            let (pl, c) =
              make_list p where rec make_list p =
                match p with
                [ <:patt< [$p$ :: $y$] >> ->
                    let (pl, c) = make_list y in
                    ([p :: pl], c)
                | <:patt< [] >> -> ([], None)
                | x -> ([], Some p) ]
            in
            match c with
            [ None ->
                fprintf ppf "[%a" (list patt) (pl, ks "]" k)
            | Some x ->
                fprintf ppf "[%a@ %a" (list patt) (pl, ks " ." nok)
                  patt (x, ks "]" k) ]
*)
      | <:patt< $p1$ $p2$ >> ->
          let pl =
            loop [p2] p1 where rec loop pl =
              fun
              [ <:patt< $p1$ $p2$ >> -> loop [p2 :: pl] p1
              | p1 -> [p1 :: pl] ]
          in
          let pl = List.map (fun p -> (p, "")) pl in
          plist curr 1
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            pl
(*
      | <:patt< ($p$ : $t$) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(:@ %a@ %a" patt (p, nok) ctyp (t, ks ")" k)
*)
      | <:patt< ($list:pl$) >> ->
          let pl = List.map (fun p -> (p, "")) pl in
          plistb patt 1
            {(pc) with bef = sprintf "%s(values" pc.bef;
             aft = sprintf ")%s" pc.aft}
            pl
      | <:patt< { $list:fpl$ } >> ->
          let record_binding pc (p1, p2) =
            horiz_vertic
              (fun () ->
                 sprintf "%s(%s %s)%s" pc.bef
                   (curr {(pc) with bef = ""; aft = ""} p1)
                   (curr {(pc) with bef = ""; aft = ""} p2) pc.aft)
              (fun () -> not_impl "record_binding vertic" pc 0)
          in
          let fpl = List.map (fun fp -> (fp, "")) fpl in
          plistb record_binding 1
            {(pc) with bef = sprintf "%s({}" pc.bef;
             aft = sprintf ")%s" pc.aft}
            fpl
(*
      | <:patt< ?$x$ >> ->
          fun ppf curr next dg k -> fprintf ppf "?%s%t" x k
      |  <:patt< ? ($lid:x$ = $e$) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(?%s@ %a" x expr (e, ks ")" k)
      | <:patt< $p1$ . $p2$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "%a.%a" patt (p1, nok) patt (p2, k)
*)
      | <:patt< $lid:s$ >> | <:patt< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:patt< $str:s$ >> ->
          sprintf "%s\"%s\"%s" pc.bef s pc.aft
(*
      | <:patt< $chr:s$ >> ->
          fun ppf curr next dg k -> fprintf ppf "'%s'%t" s k
      | <:patt< $int:s$ >> ->
          fun ppf curr next dg k -> fprintf ppf "%s%t" (int_repr s) k
      | <:patt< $flo:s$ >> ->
          fun ppf curr next dg k -> fprintf ppf "%s%t" s k
*)
      | <:patt< _ >> ->
          sprintf "%s_%s" pc.bef pc.aft
      | x ->
          not_impl "patt" pc x ] ]
  ;
  pr_str_item:
    [ "top"
      [ <:str_item< open $i$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(open %s)%s" pc.bef
                 (mod_ident {(pc) with bef = ""; aft = ""} i) pc.aft)
            (fun () ->
               not_impl "str_item open vertic" pc i)
(*
      | <:str_item< type $list:tdl$ >> ->
          fun ppf curr next dg k ->
            match tdl with
            [ [td] -> fprintf ppf "(%a" type_decl (("type", td), ks ")" k)
            | tdl ->
                fprintf ppf "(@[<hv>type@ %a@]" (listwb "" type_decl)
                  (tdl, ks ")" k) ]
      | <:str_item< exception $uid:c$ of $list:tl$ >> ->
          fun ppf curr next dg k ->
            match tl with
            [ [] -> fprintf ppf "(@[exception@ %s%t@]" c (ks ")" k)
            | tl ->
                fprintf ppf "(@[@[exception@ %s@]@ %a@]" c
                  (list ctyp) (tl, ks ")" k) ]
*)
      | <:str_item< value $flag:rf$ $list:pel$ >> ->
          let let_binding b pc (p, e) =
            horiz_vertic
              (fun () ->
                 sprintf "%s(%s%s %s)%s" pc.bef b
                   (patt {(pc) with bef = ""; aft = ""} p)
                   (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
              (fun () ->
                 let s1 =
                   patt {(pc) with bef = sprintf "%s(%s" pc.bef b; aft = ""}
                     p
                 in
                 let s2 =
                   expr
                     {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                      aft = sprintf ")%s" pc.aft}
                     e
                 in
                 sprintf "%s\n%s" s1 s2)
          in
          let b = if rf then "definerec" else "define" in
          match pel with
          [ [(p, e)] -> let_binding (b ^ " ") pc (p, e)
          | _ ->
              let s1 = sprintf "%s(%s*" pc.bef b in
              let s2 =
                let pc =
                  {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                   aft = sprintf ")%s" pc.aft}
                in
                vlist (let_binding "") pc pel
              in
              sprintf "%s\n%s" s1 s2 ]
(*
      | <:str_item< module $uid:s$ = $me$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(%a" module_binding (("module", s, me), ks ")" k)
      | <:str_item< module type $uid:s$ = $mt$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[moduletype@ %s@]@ %a@]" s
              module_type (mt, ks ")" k)
      | <:str_item< external $lid:i$ : $t$ = $list:pd$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[external@ %s@ %a@ %a@]" i ctyp (t, nok)
              (list string) (pd, ks ")" k)
      | <:str_item< $exp:e$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "%a" expr (e, k)
      | <:str_item< # $lid:s$ $opt:x$ >> ->
          fun ppf curr next dg k ->
            match x with
            [ Some e -> fprintf ppf "; # (%s %a" s expr (e, ks ")" k)
            | None -> fprintf ppf "; # (%s%t" s (ks ")" k) ]
      | <:str_item< declare $list:s$ end >> ->
          fun ppf curr next dg k ->
            if s = [] then fprintf ppf "; ..."
            else fprintf ppf "%a" (list str_item) (s, k)
      | MLast.StUse _ _ _ ->
          fun ppf curr next dg k -> ()
*)
      | x ->
          not_impl "str_item" pc x ] ]
  ;
  pr_sig_item:
    [ "top"
      [ (* <:sig_item< type $list:tdl$ >> ->
          match tdl with
          [ [td] -> sprintf "(%s" (type_decl (("type", td), ks ")" k))
          | tdl ->
              fprintf ppf "(@[<hv>type@ %a@]" (listwb "" type_decl)
                (tdl, ks ")" k) ]
      | <:sig_item< exception $uid:c$ of $list:tl$ >> ->
          fun ppf curr next dg k ->
            match tl with
            [ [] -> fprintf ppf "(@[exception@ %s%t@]" c (ks ")" k)
            | tl ->
                fprintf ppf "(@[@[exception@ %s@]@ %a@]" c
                  (list ctyp) (tl, ks ")" k) ]
      | <:sig_item< value $lid:i$ : $t$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[value %s@]@ %a@]" i ctyp (t, ks ")" k)
      | <:sig_item< external $lid:i$ : $t$ = $list:pd$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[external@ %s@]@ %a@ %a@]" i ctyp (t, nok)
              (list string) (pd, ks ")" k)
      | <:sig_item< module $uid:s$ : $mt$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[module@ %s@]@ %a@]" s
              module_type (mt, ks ")" k)
      | <:sig_item< module type $uid:s$ = $mt$ >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(@[@[moduletype@ %s@]@ %a@]" s
              module_type (mt, ks ")" k)
      | <:sig_item< declare $list:s$ end >> ->
          fun ppf curr next dg k ->
            if s = [] then fprintf ppf "; ..."
            else fprintf ppf "%a" (list sig_item) (s, k)
      | MLast.SgUse _ _ _ ->
          fun ppf curr next dg k -> ()
      | *) x ->
          not_impl "sig_item" pc x ] ]
  ;
END;

(* main part *)

value sep = ref None;

value output_string_eval oc s =
  loop 0 where rec loop i =
    if i == String.length s then ()
    else if i == String.length s - 1 then output_char oc s.[i]
    else
      match (s.[i], s.[i + 1]) with
      [ ('\\', 'n') -> do { output_char oc '\n'; loop (i + 2) }
      | (c, _) -> do { output_char oc c; loop (i + 1) } ]
;

value input_source src bp len =
  let len = min (max 0 len) (String.length src) in
  String.sub src bp len
;

value copy_source src oc first bp ep =
  match sep.val with
  [ Some str ->
      if first then ()
      else if ep == String.length src then output_string oc "\n"
      else output_string_eval oc str
  | None ->
      let s = input_source src bp (ep - bp) in
      output_string oc s ]
;

value copy_to_end src oc first bp =
  let ilen = String.length src in
  if bp < ilen then copy_source src oc first bp ilen
  else output_string oc "\n"
;

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

value apply_printer f ast = do {
  if Pcaml.input_file.val = "-" then sep.val := Some "\n"
  else do {
    let ic = open_in_bin Pcaml.input_file.val in
    let src =
      loop 0 where rec loop len =
        match try Some (input_char ic) with [ End_of_file -> None ] with
        [ Some c -> loop (Buff.store len c)
        | None -> Buff.get len ]
    in
    Prtools.source.val := src;
    close_in ic
  };
  let oc =
    match Pcaml.output_file.val with
    [ Some f -> open_out_bin f
    | None -> stdout ]
  in
  let cleanup () =
    match Pcaml.output_file.val with
    [ Some f -> close_out oc
    | None -> () ]
  in
  try do {
    let (first, last_pos) =
      List.fold_left
        (fun (first, last_pos) (si, loc) -> do {
           let bp = Ploc.first_pos loc in
           let ep = Ploc.last_pos loc in
           copy_source Prtools.source.val oc first last_pos bp;
           flush oc;
           output_string oc (f {ind = 0; bef = ""; aft = ""; dang = ""} si);
           (False, ep)
         })
        (True, 0) ast
    in
    copy_to_end Prtools.source.val oc first last_pos;
    flush oc
  }
  with exn -> do {
    cleanup ();
    raise exn
  };
  cleanup ();
};

Pcaml.print_interf.val := apply_printer sig_item;
Pcaml.print_implem.val := apply_printer str_item;

Pcaml.add_option "-l" (Arg.Int (fun x -> Pretty.line_length.val := x))
  ("<length> Maximum line length for pretty printing (default " ^
     string_of_int Pretty.line_length.val ^ ")");

Pcaml.add_option "-sep_src" (Arg.Unit (fun () -> sep.val := None))
  "Read source file for text between phrases (default).";

Pcaml.add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";
