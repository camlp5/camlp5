(* camlp5r *)
(* pr_scheme.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "pa_macro.cmo";
#load "q_MLast.cmo";
#load "pa_extprint.cmo";
#load "pa_extfun.cmo";
#load "pa_pprintf.cmo";

open Pretty;
open Pcaml;
open Prtools;
open Versdep;

do {
  Eprinter.clear pr_expr;
  Eprinter.clear pr_patt;
  Eprinter.clear pr_ctyp;
  Eprinter.clear pr_str_item;
  Eprinter.clear pr_sig_item;
  Eprinter.clear pr_module_expr;
  Eprinter.clear pr_module_type;
  Eprinter.clear pr_class_sig_item;
  Eprinter.clear pr_class_str_item;
  Eprinter.clear pr_class_expr;
  Eprinter.clear pr_class_type;
};

(* general functions *)

(**)
value test = ref False;
Pcaml.add_option "-test" (Arg.Set test) " test";
(**)

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      "\"" ^ Obj.magic x ^ "\""
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  pprintf pc "\"pr_scheme, not impl: %s; %s\"" name (String.escaped desc)
;

value to_be_renamed = ["cond"; "sum"];

value rename_id s = if List.mem s to_be_renamed then s ^ "#" else s;

IFDEF OCAML_VERSION <= OCAML_1_07 THEN
  value with_ind_bef = Pprintf.with_ind_bef;
  value with_ind_bef_aft = Pprintf.with_ind_bef_aft;
  value with_bef = Pprintf.with_bef;
  value with_bef_aft = Pprintf.with_bef_aft;
  value with_aft = Pprintf.with_aft;
END;

value rec longident pc sl =
  match sl with
  [ [] -> pprintf pc ""
  | [s] -> pprintf pc "%s" s
  | [s :: sl] -> pprintf pc "%s.%p" s longident sl ]
;

(*
 * Extensible printers
 *)

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value ctyp = Eprinter.apply pr_ctyp;
value str_item = Eprinter.apply pr_str_item;
value sig_item = Eprinter.apply pr_sig_item;
value module_expr = Eprinter.apply pr_module_expr;
value module_type = Eprinter.apply pr_module_type;
value class_str_item = Eprinter.apply pr_class_str_item;
value class_sig_item = Eprinter.apply pr_class_sig_item;
value class_expr = Eprinter.apply pr_class_expr;
value class_type = Eprinter.apply pr_class_type;

value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;

value rec is_irrefut_patt =
  fun
  [ <:patt< $lid:_$ >> -> True
  | <:patt< () >> -> True
  | <:patt< _ >> -> True
  | <:patt< ($x$ as $y$) >> -> is_irrefut_patt x && is_irrefut_patt y
  | <:patt< { $list:fpl$ } >> ->
      List.for_all (fun (_, p) -> is_irrefut_patt p) fpl
  | <:patt< ($p$ : $_$) >> -> is_irrefut_patt p
  | <:patt< ($list:pl$) >> -> List.for_all is_irrefut_patt pl
  | <:patt< ?{$_$ = ?{$_$ = $_$}} >> -> True
  | <:patt< ?{$_$ = $_$} >> -> True
  | <:patt< ?{$_$} >> -> True
  | <:patt< ~{$_$} >> -> True
  | _ -> False ]
;

pr_expr_fun_args.val :=
  extfun Extfun.empty with
  [ <:expr< fun [$p$ -> $e$] >> as ge ->
      if is_irrefut_patt p then
        let (pl, e) = expr_fun_args e in
        ([p :: pl], e)
      else ([], ge)
  | ge -> ([], ge) ];

value has_cons_with_params vdl =
  List.exists
    (fun (_, _, tl, rto) ->
       match tl with
       [ <:vala< [] >> -> False
       | _ -> True ])
    vdl
;

value paren pc b =
  {(pc) with ind = pc.ind + 1; bef = sprintf "%s(%s" pc.bef b;
   aft = sprintf ")%s" pc.aft}
;

value bracket pc b =
  {(pc) with ind = pc.ind + 1; bef = sprintf "%s[%s" pc.bef b;
   aft = sprintf "]%s" pc.aft}
;

value brace pc b =
  {(pc) with ind = pc.ind + 1; bef = sprintf "%s{%s" pc.bef b;
   aft = sprintf "}%s" pc.aft}
;

value braceless pc b =
  {(pc) with ind = pc.ind + 1; bef = sprintf "%s{<%s" pc.bef b;
   aft = sprintf ">}%s" pc.aft}
;

value type_param pc (tv, vari) =
  let tv = Pcaml.unvala tv in
  pprintf pc "%s%s"
    (match vari with
     [ Some True -> "+"
     | Some False -> "-"
     | None -> "" ])
    (match tv with
     [ Some v -> "'" ^ v
     | None -> "_" ])
;

value type_var pc v = pprintf pc "'%s" v;

value type_decl b pc td =
  let n = rename_id (Pcaml.unvala (snd (Pcaml.unvala td.MLast.tdNam))) in
  pprintf pc "@[<1>(%s%p@ %p)@]" b
    (fun pc ->
       fun
       [ [] -> pprintf pc "%s" n
       | tp -> pprintf pc "(%s %p)" n (hlist type_param) tp ])
    (Pcaml.unvala td.MLast.tdPrm) ctyp td.MLast.tdDef
;

value type_decl_list pc =
  fun
  [ [td] -> type_decl "type " pc td
  | tdl ->
      horiz_vertic
        (fun () -> pprintf pc "(type* %p)" (hlist (type_decl "")) tdl)
        (fun () -> pprintf pc "(type*@;<1 1>%p)" (vlist (type_decl "")) tdl) ]
;

value exception_decl pc (c, tl) =
  plistbf 0 (paren pc "exception")
    [(fun pc -> pprintf pc "%s" c, "") ::
     List.map (fun t -> (fun pc -> ctyp pc t, "")) tl]
;

value value_binding b pc (p, e) =
  let (pl, e) = expr_fun_args e in
  horiz_vertic
    (fun () ->
       pprintf pc "(%s%p %p)" (if b = "" then "" else b ^ " ")
         (fun pc ->
            fun
            [ [] -> patt pc p
            | _ -> pprintf pc "(%p)" (hlist patt) [p :: pl] ])
         pl expr e)
    (fun () ->
       let s1 =
         match pl with
         [ [] ->
             let pc = {(pc) with aft = ""} in
             pprintf pc "@[<1>(%s%p@]" (if b = "" then "" else b ^ " ") patt p
         | _ ->
             let pc =
               {(pc) with ind = pc.ind + 1; bef = sprintf "%s(%s" pc.bef b;
                aft = ""}
             in
             (if b = "" then plistf else plistbf) 0 pc
               [(fun pc ->
                   plist patt 0 (paren pc "")
                     (List.map (fun p -> (p, "")) [p :: pl]),
                 "")] ]
       in
       let s2 =
         expr
           {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
            aft = sprintf ")%s" pc.aft}
           e
       in
       sprintf "%s\n%s" s1 s2)
;

value value_binding_list pc (rf, pel) =
  let b = if rf then "definerec" else "define" in
  match pel with
  [ [(p, e)] -> value_binding b pc (p, e)
  | _ ->
      horiz_vertic
        (fun () ->
           pprintf pc "(%s* %p)" b (hlist (value_binding "")) pel)
        (fun () ->
           pprintf pc "(%s*@;<1 1>%p)" b (vlist (value_binding "")) pel) ]
;

value let_binding pc (p, e) =
  let (pl, e) = expr_fun_args e in
  plistf 0 (paren pc "")
    [(fun pc ->
        match pl with
        [ [] -> patt pc p
        | _ -> pprintf pc "(%p)" (hlist patt) [p :: pl] ],
      "");
     (fun pc -> expr pc e, "")]
;

value let_binding_list pc (b, pel, e) =
  plistbf 0 (paren pc b)
    [(fun pc ->
        horiz_vertic
          (fun () -> hlist let_binding (paren pc "") pel)
          (fun () -> vlist let_binding (paren pc "") pel),
      "");
     (fun pc -> expr pc e, "")]
;

value match_assoc pc (p, we, e) =
  let list = [(fun pc -> expr pc e, "")] in
  let list =
    match we with
    [ <:vala< Some e >> ->
        [(fun pc ->
            plistbf 0 (paren pc "when")
              [(fun pc -> patt pc p, ""); (fun pc -> expr pc e, "")],
          "") ::
         list]
    | _ -> [(fun pc -> patt pc p, "") :: list] ]
  in
  plistf 0 (paren pc "") list
;

value constr_decl pc (_, c, tl, rto) =
  let c = Pcaml.unvala c in
  let tl = Pcaml.unvala tl in
  match tl with
  [ [] -> pprintf pc "(%s)" c
  | _ ->
      plistf 0 (paren pc "")
        [(fun pc -> pprintf pc "%s" c, "") ::
         List.map (fun t -> (fun pc -> ctyp pc t, "")) tl] ]
;

value poly_variant_decl pc =
  fun
  [ <:poly_variant< `$s$ >> ->
      pprintf pc "(` %s)" s
  | <:poly_variant< `$s$ of $flag:a$ $list:tl$ >> ->
      let list =
        let list =
          [(fun pc -> plist ctyp 0 pc (List.map (fun t -> (t, "")) tl), "")]
        in
        let list =
          if a then [(fun pc -> pprintf pc "&", "") :: list] else list
        in
        [(fun pc -> pprintf pc "%s" s, "") :: list]
      in
      plistbf 0 (paren pc "`") list
  | <:poly_variant< $t$ >> ->
      ctyp pc t
  | IFDEF STRICT THEN
      _ -> not_impl "poly_variant_decl" pc 0
    END ]
;

value label_decl pc (_, l, m, t) =
  let list = [(fun pc -> ctyp pc t, "")] in
  plistf 0 (paren pc "")
    [(fun pc -> pprintf pc "%s" l, "") ::
     if m then [(fun pc -> pprintf pc "mutable", "") :: list] else list]
;

value module_type_decl pc (s, mt) =
  plistbf 0 (paren pc "moduletype")
    [(fun pc -> pprintf pc "%s" s, "");
     (fun pc -> module_type pc mt, "")]
;

value field_expr pc (l, e) =
  plistf 0 (paren pc "")
    [(fun pc -> pprintf pc "%s" l, ""); (fun pc -> expr pc e, "")]
;

value string pc s = pprintf pc "\"%s\"" s;

value int_repr s =
  if String.length s > 2 && s.[0] = '0' then
    match s.[1] with
    [ 'b' | 'B' -> "#b" ^ String.sub s 2 (String.length s - 2)
    | 'o' | 'O' -> "#o" ^ String.sub s 2 (String.length s - 2)
    | 'x' | 'X' -> "#x" ^ String.sub s 2 (String.length s - 2)
    | _ -> s ]
  else if String.length s > 3 && s.[0] = '-' && s.[1] = '0' then
    match s.[2] with
    [ 'b' | 'B' -> "-#b" ^ String.sub s 3 (String.length s - 3)
    | 'o' | 'O' -> "-#o" ^ String.sub s 3 (String.length s - 3)
    | 'x' | 'X' -> "-#x" ^ String.sub s 3 (String.length s - 3)
    | _ -> s ]
  else s
;

value with_constraint pc =
  fun
  [ <:with_constr< type $sl$ $list:tvl$ = $flag:pf$ $t$ >> ->
      pprintf pc "(type%s %p@;<1 1>%p)" (if pf then "private" else "")
        (fun pc ->
           fun
           [ [] -> longident pc sl
           | tvl ->
               pprintf pc "(%p %p)" longident sl
                 (hlist type_param) tvl ])
        tvl ctyp t
  | wc -> not_impl "with_constraint" pc wc ]
;

value class_descr b pc cd =
  let n = Pcaml.unvala cd.MLast.ciNam in
  horiz_vertic
    (fun () ->
       pprintf pc "(%s%s%p %p)" (if b = "" then "" else b ^ " ")
         (if Pcaml.unvala cd.MLast.ciVir then "virtual " else "")
         (fun pc ->
            fun
            [ [] -> pprintf pc "%s" n
            | tvl -> pprintf pc "(%s %p)" n (hlist type_param) tvl ])
         (Pcaml.unvala (snd cd.MLast.ciPrm)) class_type cd.MLast.ciExp)
    (fun () ->
       let list =
         let list =
           [(fun pc ->
               match Pcaml.unvala (snd cd.MLast.ciPrm) with
               [ [] -> pprintf pc "%s" n
               | tvl ->
                   plistb type_param 0 (paren pc n)
                     (List.map (fun tv -> (tv, "")) tvl) ],
             "");
            (fun pc -> class_type pc cd.MLast.ciExp, "")]
         in
         let list =
           if Pcaml.unvala cd.MLast.ciVir then
             [(fun pc -> pprintf pc "virtual", "") :: list]
           else list
         in
         if b = "" then list
         else [(fun pc -> pprintf pc "%s" b, "") :: list]
       in
       plistf 0 (paren pc "") list)
;

value class_descr_list pc =
  fun
  [ [cd] -> class_descr "class" pc cd
  | cdl ->
      horiz_vertic
        (fun () -> pprintf pc "(class* %p)" (hlist (class_descr "")) cdl)
        (fun () ->
           let s1 = sprintf "%s(class*" pc.bef in
           let s2 =
             vlist (class_descr "")
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               cdl
           in
           sprintf "%s\n%s" s1 s2) ]
;

value class_decl b pc cd =
  let n = Pcaml.unvala cd.MLast.ciNam in
  let ce = cd.MLast.ciExp in
  horiz_vertic
    (fun () ->
       sprintf "%s(%s%s%s %s)%s" pc.bef (if b = "" then "" else b ^ " ")
         (if Pcaml.unvala cd.MLast.ciVir then "virtual " else "")
         (match Pcaml.unvala (snd cd.MLast.ciPrm) with
          [ [] -> n
          | tvl ->
              sprintf "(%s %s)" n
                (hlist type_param {(pc) with bef = ""; aft = ""} tvl) ])
         (class_expr {(pc) with bef = ""; aft = ""} ce) pc.aft)
    (fun () ->
       let list =
         let list =
           [(fun pc ->
               match Pcaml.unvala (snd cd.MLast.ciPrm) with
               [ [] -> sprintf "%s%s%s" pc.bef n pc.aft
               | tvl ->
                   plistb type_param 0 (paren pc n)
                     (List.map (fun tv -> (tv, "")) tvl) ],
             "");
            (fun pc -> class_expr pc ce, "")]
         in
         let list =
           if Pcaml.unvala cd.MLast.ciVir then
             [(fun pc -> sprintf "%svirtual%s" pc.bef pc.aft, "") ::
              list]
           else list
         in
         if b = "" then list
         else [(fun pc -> sprintf "%s%s%s" pc.bef b pc.aft, "") :: list]
       in
       plistf 0 (paren pc "") list)
;

value class_type_decl b pc cd =
  let n = Pcaml.unvala cd.MLast.ciNam in
  let ct = cd.MLast.ciExp in
  horiz_vertic
    (fun () ->
       sprintf "%s(%s%s%s %s)%s" pc.bef (if b = "" then "" else b ^ " ")
         (if Pcaml.unvala cd.MLast.ciVir then "virtual " else "")
         (match Pcaml.unvala (snd cd.MLast.ciPrm) with
          [ [] -> n
          | tvl ->
              sprintf "(%s %s)" n
                (hlist type_param {(pc) with bef = ""; aft = ""} tvl) ])
         (class_type {(pc) with bef = ""; aft = ""} ct) pc.aft)
    (fun () ->
       let list =
         let list =
           [(fun pc ->
               match Pcaml.unvala (snd cd.MLast.ciPrm) with
               [ [] -> sprintf "%s%s%s" pc.bef n pc.aft
               | tvl ->
                   plistb type_param 0 (paren pc n)
                     (List.map (fun tv -> (tv, "")) tvl) ],
             "");
            (fun pc -> class_type pc ct, "")]
         in
         let list =
           if Pcaml.unvala cd.MLast.ciVir then
             [(fun pc -> sprintf "%svirtual%s" pc.bef pc.aft, "") ::
              list]
           else list
         in
         if b = "" then list
         else [(fun pc -> sprintf "%s%s%s" pc.bef b pc.aft, "") :: list]
       in
       plistf 0 (paren pc "") list)
;

value class_decl_list pc =
  fun
  [ [cd] -> class_decl "class" pc cd
  | cdl ->
      horiz_vertic
        (fun () ->
           sprintf "%s(class* %s)%s" pc.bef
             (hlist (class_decl "") {(pc) with bef = ""; aft = ""} cdl)
             pc.aft)
        (fun () ->
           let s1 = sprintf "%s(class*" pc.bef in
           let s2 =
             vlist (class_decl "")
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               cdl
           in
           sprintf "%s\n%s" s1 s2) ]
;

value class_type_decl_list pc =
  fun
  [ [ctd] -> class_type_decl "class" pc ctd
  | ctdl ->
      horiz_vertic
        (fun () ->
           sprintf "%s(class* %s)%s" pc.bef
             (hlist (class_type_decl "") {(pc) with bef = ""; aft = ""} ctdl)
             pc.aft)
        (fun () ->
           let s1 = sprintf "%s(classtype*" pc.bef in
           let s2 =
             vlist (class_type_decl "")
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               ctdl
           in
           sprintf "%s\n%s" s1 s2) ]
;

EXTEND_PRINTER
  pr_ctyp:
    [ "top"
      [ <:ctyp< [ $list:cdl$ ] >> ->
          horiz_vertic
            (fun () ->
               if has_cons_with_params cdl then sprintf "\n"
               else
                 sprintf "%s(sum %s)%s" pc.bef
                   (hlist constr_decl {(pc) with bef = ""; aft = ""} cdl)
                   pc.aft)
            (fun () ->
               vlistf (paren pc "")
                 [fun pc -> sprintf "%ssum%s" pc.bef pc.aft ::
                  List.map (fun cd pc -> constr_decl pc cd) cdl])
      | <:ctyp< { $list:cdl$ } >> ->
          let cdl = List.map (fun cd -> (cd, "")) cdl in
          plist label_decl 0 (brace pc "") cdl
      | <:ctyp< [ = $list:vl$ ] >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(variants %s)%s" pc.bef
                 (hlist poly_variant_decl {(pc) with bef = ""; aft = ""} vl)
                 pc.aft)
            (fun () ->
               vlistf (paren pc "")
                 [fun pc -> sprintf "%svariants%s" pc.bef pc.aft ::
                  List.map (fun cd pc -> poly_variant_decl pc cd) vl])
      | <:ctyp< [ < $list:vl$ ] >> ->
          plistbf 0 (paren pc "variantsless")
            (List.map (fun v -> (fun pc -> poly_variant_decl pc v, "")) vl)
      | <:ctyp< [ > $list:vl$ ] >> ->
          plistbf 0 (paren pc "variantsgreater")
            (List.map (fun v -> (fun pc -> poly_variant_decl pc v, "")) vl)
      | <:ctyp< ( $list:tl$ ) >> ->
          let tl = List.map (fun t -> (t, "")) tl in
          plistb curr 0 (paren pc "*") tl
      | <:ctyp< $t1$ -> $t2$ >> ->
          let tl =
            loop t2 where rec loop =
              fun
              [ <:ctyp< $t1$ -> $t2$ >> -> [(t1, "") :: loop t2]
              | t -> [(t, "")] ]
          in
          plistb ctyp 0 (paren pc "->") [(t1, "") :: tl]
      | <:ctyp< $t1$ $t2$ >> ->
          let tl =
            loop [t2] t1 where rec loop tl =
              fun
              [ <:ctyp< $t1$ $t2$ >> -> loop [t2 :: tl] t1
              | t1 -> [t1 :: tl] ]
          in
          let tl = List.map (fun p -> (p, "")) tl in
          plist curr 1 (paren pc "") tl
      | <:ctyp< $t1$ == $t2$ >> ->
          plistb curr 0 (paren pc "==") [(t1, ""); (t2, "")]
      | <:ctyp< $t1$ as $t2$ >> ->
          plistb curr 0 (paren pc "as") [(t1, ""); (t2, "")]
      | <:ctyp< $t1$ . $t2$ >> ->
          sprintf "%s.%s"
            (curr {(pc) with aft = ""} t1)
            (curr {(pc) with bef = ""} t2)
      | <:ctyp< < $list:fl$ $flag:v$ > >> ->
          let b = if v then "objectvar" else "object" in
          if fl = [] then sprintf "%s(%s)%s" pc.bef b pc.aft
          else not_impl "ty obj" pc 0
      | <:ctyp< ?$s$: $t$ >> ->
          plistbf 0 (paren pc "?")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> curr pc t, "")]
      | <:ctyp< ~$s$: $t$ >> ->
          plistbf 0 (paren pc "~")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> curr pc t, "")]
      | <:ctyp< $lid:s$ >> ->
          sprintf "%s%s%s" pc.bef (rename_id s) pc.aft
      | <:ctyp< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:ctyp< ' $s$ >> ->
          sprintf "%s'%s%s" pc.bef s pc.aft
      | <:ctyp< _ >> ->
          sprintf "%s_%s" pc.bef pc.aft
      | <:ctyp< # $list:sl$ >> ->
          pprintf pc "(# %p)" longident sl
      | <:ctyp< ! $list:pl$ . $t$ >> ->
          pprintf pc "(! (%p)@;<1 1>%p)" (hlist type_var) pl ctyp t
      | x ->
          not_impl "ctyp" pc x ] ]
  ;
  pr_expr:
    [ "top"
      [ <:expr< fun [] >> ->
          sprintf "%s(lambda)%s" pc.bef pc.aft
      | <:expr< fun $p$ -> $e$ >> when is_irrefut_patt p ->
          let (pl, e) = expr_fun_args e in
          if pl = [] then
            plistbf 0 (paren pc "lambda")
              [(fun pc -> patt pc p, ""); (fun pc -> curr pc e, "")]
          else
            plistbf 0 (paren pc "lambda")
              [(fun pc ->
                  plist patt 0
                    {(pc) with bef = sprintf "%s(" pc.bef;
                     aft = sprintf ")%s" pc.aft}
                    (List.map (fun p -> (p, "")) [p :: pl]),
                "");
               (fun pc -> curr pc e, "")]
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
      | <:expr< match $e$ with [ $list:pwel$ ] >> |
        <:expr< try $e$ with [ $list:pwel$ ] >> as x ->
          let op =
            match x with
            [ <:expr< match $e$ with [ $list:pwel$ ] >> -> "match"
            | _ -> "try" ]
          in
          horiz_vertic
            (fun () ->
               sprintf "%s(%s %s %s)%s" pc.bef op
                 (curr {(pc) with bef = ""; aft = ""} e)
                 (hlist match_assoc {(pc) with bef = ""; aft = ""} pwel)
                 pc.aft)
            (fun () ->
               let s1 =
                 let pc = {(pc) with bef = sprintf "%s(" pc.bef} in
                 horiz_vertic
                   (fun () ->
                      sprintf "%s%s %s" pc.bef op
                        (curr {(pc) with bef = ""; aft = ""} e))
                   (fun () ->
                      let s1 = sprintf "%s%s" pc.bef op in
                      let s2 =
                        curr
                          {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                           aft = ""}
                        e
                      in
                      sprintf "%s\n%s" s1 s2)
               in
               let s2 =
                 let pc =
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1)}
                 in
                 vlist match_assoc {(pc) with aft = sprintf ")%s" pc.aft} pwel
               in
               sprintf "%s\n%s" s1 s2)
      | <:expr< let $p1$ = $e1$ in $e2$ >> ->
          let (pel, e) =
            loop [(p1, e1)] e2 where rec loop pel =
              fun
              [ <:expr< let $p1$ = $e1$ in $e2$ >> ->
                  loop [(p1, e1) :: pel] e2
              | e -> (List.rev pel, e) ]
          in
          let b =
            match pel with
            [ [_] -> "let"
            | _ -> "let*" ]
          in
          let_binding_list pc (b, pel, e)
      | <:expr< let $flag:rf$ $list:pel$ in $e$ >> ->
          let b = if rf then "letrec" else "let" in
          let_binding_list pc (b, pel, e)
      | <:expr< let module $uid:s$ = $me$ in $e$ >> ->
          plistbf 0 (paren pc "letmodule")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> module_expr pc me, "");
             (fun pc -> curr pc e, "")]
      | <:expr< if $e1$ then $e2$ else () >> ->
          plistb curr 0 (paren pc "if") [(e1, ""); (e2, "")]
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
                    (fun () ->
                       let s1 = sprintf "%s(if" pc.bef in
                       let s2 =
                         curr
                           {(pc) with ind = pc.ind + 1;
                            bef = tab (pc.ind + 1); aft = ""} e1
                       in
                       sprintf "%s\n%s" s1 s2)
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
      | <:expr< for $lid:i$ = $e1$ $to:tf$ $e2$ do { $list:el$ } >> ->
          let b = if tf then "for" else "fordown" in
          plistbf 0 (paren pc b)
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> curr pc e1, ""); (fun pc -> curr pc e2, "");
             (fun pc -> plist curr 0 pc (List.map (fun e -> (e, "")) el), "")]
      | <:expr< while $e$ do { $list:el$ } >> ->
          plistbf 0 (paren pc "while")
            [(fun pc -> curr pc e, "");
             (fun pc -> plist curr 0 pc (List.map (fun e -> (e, "")) el), "")]
      | <:expr< ($e$ : $t$) >> ->
          plistbf 0 (paren pc ":")
            [(fun pc -> curr pc e, ""); (fun pc -> ctyp pc t, "")]
      | <:expr< ($list:el$) >> ->
          let el = List.map (fun e -> (e, "")) el in
          plistb curr 1
            {(pc) with bef = sprintf "%s(values" pc.bef;
             aft = sprintf ")%s" pc.aft}
            el
      | <:expr< { $list:fel$ } >> ->
          let record_binding pc (p, e) =
            plistf 0 (paren pc "")
              [(fun pc -> patt pc p, ""); (fun pc -> curr pc e, "")]
          in
          plist record_binding 0 (brace pc "")
            (List.map (fun fe -> (fe, "")) fel)
      | <:expr< { ($e$) with $list:fel$ } >> ->
          let record_binding pc (p, e) =
            plistf 0 (paren pc "")
              [(fun pc -> patt pc p, ""); (fun pc -> curr pc e, "")]
          in
          plistbf 0 (brace pc "with")
            [(fun pc -> curr pc e, "") ::
             List.map (fun fe -> (fun pc -> record_binding pc fe, "")) fel]
      | <:expr< $e1$ := $e2$ >> ->
          plistb curr 1
            {(pc) with bef = sprintf "%s(:=" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(e1, ""); (e2, "")]
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
          let pc = bracket pc "" in
          match c with
          [ None ->
              let el = List.map (fun e -> (e, "")) el in
              plist curr 0 pc el
          | Some x ->
              let dot_expr pc e =
                curr {(pc) with bef = sprintf "%s. " pc.bef} e
              in
              horiz_vertic
                (fun () -> hlistl curr dot_expr pc (el @ [x]))
                (fun () ->
                   let el =
                     list_rev_map (fun e -> (e, "")) [x :: List.rev el]
                   in
                   plistl curr dot_expr 0 pc el) ]
      | <:expr< [| $list:el$ |] >> ->
          plist curr 0
            {(pc) with ind = pc.ind + 2; bef = sprintf "%s#(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            (List.map (fun e -> (e, "")) el)
      | <:expr< assert $x$ >> ->
          plistf 0 (paren pc "")
            [(fun pc -> sprintf "%sassert%s" pc.bef pc.aft, "");
             (fun pc -> curr pc x, "")]
      | <:expr< lazy $x$ >> ->
          plistf 0 (paren pc "")
            [(fun pc -> sprintf "%slazy%s" pc.bef pc.aft, "");
             (fun pc -> curr pc x, "")]
      | <:expr< new $list:x$ >> ->
          plistf 0 (paren pc "")
            [(fun pc -> sprintf "%snew%s" pc.bef pc.aft, "");
             (fun pc -> longident pc x, "")]
(*
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
          plist curr 0 (paren pc "") el
      | <:expr< $e$ # $s$ >> ->
          plistf 0 (paren pc "")
            [(fun pc -> sprintf "%ssend%s" pc.bef pc.aft, "");
             (fun pc -> curr pc e, "");
             (fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "")]
      | <:expr< ?{$lid:s$} >> ->
          plistbf 0 (paren pc "?")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "")]
      | <:expr< ?{$lid:s$ = $e$} >> ->
          plistbf 0 (paren pc "?")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> curr pc e, "")]
      | <:expr< ~{$lid:s$} >> ->
          plistbf 0 (paren pc "~")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "")]
      | <:expr< ~{$lid:s$ = $e$} >> ->
          plistbf 0 (paren pc "~")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> curr pc e, "")]
      | <:expr< $e1$ .[ $e2$ ] >> ->
          sprintf "%s%s.[%s]%s" pc.bef
            (curr {(pc) with bef = ""; aft = ""} e1)
            (curr {(pc) with bef = ""; aft = ""} e2) pc.aft
      | <:expr< $e1$ .( $e2$ ) >> ->
          sprintf "%s%s.(%s)%s" pc.bef
            (curr {(pc) with bef = ""; aft = ""} e1)
            (curr {(pc) with bef = ""; aft = ""} e2) pc.aft
      | <:expr< $e1$ . $e2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} e1)
             (curr {(pc) with bef = ""} e2)
      | <:expr< $int:s$ >> ->
          sprintf "%s%s%s" pc.bef (int_repr s) pc.aft
      | <:expr< $int32:s$ >> ->
          sprintf "%s%sl%s" pc.bef (int_repr s) pc.aft
      | <:expr< $int64:s$ >> ->
          sprintf "%s%sL%s" pc.bef (int_repr s) pc.aft
      | <:expr< $nativeint:s$ >> ->
          sprintf "%s%sn%s" pc.bef (int_repr s) pc.aft
      | <:expr< $flo:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $lid:s$ >> ->
          let s =
            match s with
            [ "~-" -> "-"
            | "~-." -> "-."
            | s -> rename_id s ]
          in
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $str:s$ >> ->
          sprintf "%s\"%s\"%s" pc.bef s pc.aft
      | <:expr< $chr:s$ >> ->
          sprintf "%s'%s'%s" pc.bef s pc.aft
      | <:expr< ` $s$ >> ->
          sprintf "%s(` %s)%s" pc.bef s pc.aft
      | <:expr< {< $list:fel$ >} >> ->
          let fel = List.map (fun fel -> (fel, "")) fel in
          plist field_expr 0 (braceless pc "") fel
      | <:expr< object $opt:cst$ $list:csl$ end >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(object%s %s)%s" pc.bef
                 (match cst with
                  [ Some t -> not_impl "expr object self horiz " pc 0
                  | None -> "" ])
                 (hlist class_str_item {(pc) with bef = ""; aft = ""} csl)
                    pc.aft)
            (fun () ->
               let s1 =
                 let s = sprintf "%s(object" pc.bef in
                 match cst with
                 [ Some p ->
                     plistb patt 0
                       {(pc) with ind = pc.ind + 1; bef = s; aft = ""}
                       [(p, "")]
                 | None -> s ]
               in
               let s2 =
                 vlist class_str_item
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   csl
               in
               sprintf "%s\n%s" s1 s2)
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
            {(pc) with bef = sprintf "%s(or" pc.bef;
             aft = sprintf ")%s" pc.aft}
            pl
      | <:patt< ($p1$ as $p2$) >> ->
          plistb curr 0 (paren pc "as") [(p1, ""); (p2, "")]
      | <:patt< $p1$ .. $p2$ >> ->
          plistb curr 0 (paren pc "range") [(p1, ""); (p2, "")]
      | <:patt< [$_$ :: $_$] >> as p ->
          let (pl, c) =
            make_list p where rec make_list p =
              match p with
              [ <:patt< [$p$ :: $y$] >> ->
                  let (pl, c) = make_list y in
                  ([p :: pl], c)
              | <:patt< [] >> -> ([], None)
              | x -> ([], Some p) ]
          in
          let pc = bracket pc "" in
          match c with
          [ None ->
              let pl = List.map (fun p -> (p, "")) pl in
              plist curr 0 pc pl
          | Some x ->
              let dot_patt pc p =
                curr {(pc) with bef = sprintf "%s. " pc.bef} p
              in
              horiz_vertic
                (fun () -> hlistl curr dot_patt pc (pl @ [x]))
                (fun () ->
                   let pl =
                     list_rev_map (fun p -> (p, "")) [x :: List.rev pl]
                   in
                   plistl curr dot_patt 0 pc pl) ]
      | <:patt< [| $list:pl$ |] >> ->
          plist curr 0
            {(pc) with ind = pc.ind + 2; bef = sprintf "%s#(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            (List.map (fun p -> (p, "")) pl)
      | <:patt< $p1$ $p2$ >> ->
          let pl =
            loop [p2] p1 where rec loop pl =
              fun
              [ <:patt< $p1$ $p2$ >> -> loop [p2 :: pl] p1
              | p1 -> [p1 :: pl] ]
          in
          let pl = List.map (fun p -> (p, "")) pl in
          plist curr 1 (paren pc "") pl
      | <:patt< ($p$ : $t$) >> ->
          plistbf 0 (paren pc ":")
            [(fun pc -> curr pc p, ""); (fun pc -> ctyp pc t, "")]
      | <:patt< ($list:pl$) >> ->
          let pl = List.map (fun p -> (p, "")) pl in
          plistb curr 1
            {(pc) with bef = sprintf "%s(values" pc.bef;
             aft = sprintf ")%s" pc.aft}
            pl
      | <:patt< { $list:fpl$ } >> ->
          let record_binding pc (p1, p2) =
            plistf 0 (paren pc "")
              [(fun pc -> curr pc p1, ""); (fun pc -> curr pc p2, "")]
          in
          plist record_binding 0 (brace pc "")
            (List.map (fun fp -> (fp, "")) fpl)
      | <:patt< ?{$p$} >> ->
          plistbf 0 (paren pc "?")
            [(fun pc -> pprintf pc "%p" patt p, "")]
      | <:patt< ?{$lid:s$ = $lid:p$} >> ->
          plistbf 0 (paren pc "?")
            [(fun pc -> plistbf 0 (paren pc s) [(fun pc -> p, "")], "")]
      | <:patt< ?{$lid:s$ = $e$} >> ->
          plistbf 0 (paren pc "?")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> expr pc e, "")]
      | <:patt< ?{$lid:s$ = ?{$lid:p$ = $e$}} >> ->
          plistbf 0 (paren pc "?")
            [(fun pc -> plistbf 0 (paren pc s) [(fun pc -> p, "")], "");
             (fun pc -> expr pc e, "")]
      | <:patt< ~{$lid:s$} >> ->
          plistbf 0 (paren pc "~")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "")]
      | <:patt< ~{$lid:s$ = $p$} >> ->
          plistbf 0 (paren pc "~")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> curr pc p, "")]
      | <:patt< $p1$ . $p2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} p1)
             (curr {(pc) with bef = ""} p2)
      | <:patt< $lid:s$ >> ->
          sprintf "%s%s%s" pc.bef (rename_id s) pc.aft
      | <:patt< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:patt< $str:s$ >> ->
          sprintf "%s\"%s\"%s" pc.bef s pc.aft
      | <:patt< $chr:s$ >> ->
          sprintf "%s'%s'%s" pc.bef s pc.aft
      | <:patt< $int:s$ >> ->
          sprintf "%s%s%s" pc.bef (int_repr s) pc.aft
      | <:patt< $int32:s$ >> ->
          sprintf "%s%sl%s" pc.bef (int_repr s) pc.aft
      | <:patt< $int64:s$ >> ->
          sprintf "%s%sL%s" pc.bef (int_repr s) pc.aft
      | <:patt< $nativeint:s$ >> ->
          sprintf "%s%sn%s" pc.bef (int_repr s) pc.aft
(*
      | <:patt< $flo:s$ >> ->
          fun ppf curr next dg k -> fprintf ppf "%s%t" s k
*)
      | <:patt< ` $s$ >> ->
          sprintf "%s(` %s)%s" pc.bef s pc.aft
      | <:patt< _ >> ->
          sprintf "%s_%s" pc.bef pc.aft
      | <:patt< # $list:sl$ >> ->
          pprintf pc "(# %p)" longident sl
      | x ->
          not_impl "patt" pc x ] ]
  ;
  pr_str_item:
    [ "top"
      [ <:str_item< class $list:cdl$ >> ->
          class_decl_list pc cdl
      | <:str_item< class type $list:ctdl$ >> ->
          class_type_decl_list pc ctdl
      | <:str_item< open $i$ >> ->
          plistb longident 0 (paren pc "open") [(i, "")]
      | <:str_item< include $me$ >> ->
          plistb module_expr 0 (paren pc "include") [(me, "")]
      | <:str_item< type $list:tdl$ >> ->
          type_decl_list pc tdl
      | <:str_item< exception $uid:c$ of $list:tl$ >> ->
          exception_decl pc (c, tl)
      | <:str_item< exception $uid:c$ of $list:_$ = $id$ >> ->
          plistbf 0 (paren pc "exceptionrebind")
            [(fun pc -> sprintf "%s%s%s" pc.bef c pc.aft, "");
             (fun pc -> longident pc id, "")]
      | <:str_item< value $flag:rf$ $list:pel$ >> ->
          value_binding_list pc (rf, pel)
      | <:str_item< module $uid:s$ = $me$ >> ->
          plistbf 0 (paren pc "module")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> module_expr pc me, "")]
      | <:str_item< module type $s$ = $mt$ >> ->
          module_type_decl pc (s, mt)
      | <:str_item< external $lid:i$ : $t$ = $list:pd$ >> ->
          plistbf 0 (paren pc "external")
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> ctyp pc t, "") ::
             List.map (fun s -> (fun pc -> string pc s, "")) pd]
      | <:str_item< $exp:e$ >> ->
          expr pc e
      | <:str_item< # $lid:s$ $opt:x$ >> ->
          plistbf 0 (paren pc "#")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "") ::
             match x with
             [ Some e -> [(fun pc -> expr pc e, "")]
             | None -> [] ]]
      | <:str_item< declare $list:sil$ end >> ->
          if sil = [] then sprintf "%s%s" pc.bef pc.aft
          else vlist str_item pc sil
(*
      | MLast.StUse _ _ _ ->
          fun ppf curr next dg k -> ()
*)
      | x ->
          not_impl "str_item" pc x ] ]
  ;
  pr_sig_item:
    [ "top"
      [ <:sig_item< class $list:cdl$ >> ->
          class_descr_list pc cdl
      | <:sig_item< declare $list:sil$ end >> ->
          if sil = [] then sprintf "%s%s" pc.bef pc.aft
          else vlist sig_item pc sil
      | <:sig_item< external $lid:i$ : $t$ = $list:pd$ >> ->
          plistbf 0 (paren pc "external")
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> ctyp pc t, "") ::
             List.map (fun s -> (fun pc -> string pc s, "")) pd]
      | <:sig_item< include $mt$ >> ->
          plistb module_type 0 (paren pc "include") [(mt, "")]
      | <:sig_item< module $uid:s$ : $mt$ >> ->
          plistbf 0 (paren pc "module")
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> module_type pc mt, "")]
      | <:sig_item< module type $s$ = $mt$ >> ->
          module_type_decl pc (s, mt)
      | <:sig_item< open $i$ >> ->
          plistb longident 0 (paren pc "open") [(i, "")]
      | <:sig_item< type $list:tdl$ >> ->
          type_decl_list pc tdl
      | <:sig_item< exception $uid:c$ of $list:tl$ >> ->
          exception_decl pc (c, tl)
      | <:sig_item< value $lid:i$ : $t$ >> ->
          plistbf 0 (paren pc "value")
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> ctyp pc t, "")]
(*
      | MLast.SgUse _ _ _ ->
          fun ppf curr next dg k -> ()
*)
      | x ->
          not_impl "sig_item" pc x ] ]
  ;
  pr_module_expr:
    [ "top"
      [ <:module_expr< functor ($uid:i$ : $mt$) -> $me$ >> ->
          plistbf 0 (paren pc "functor")
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> module_type pc mt, "");
             (fun pc -> module_expr pc me, "")]
      | <:module_expr< struct $list:sil$ end >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(struct %s)%s" pc.bef
                 (hlist str_item {(pc) with bef = ""; aft = ""} sil) pc.aft)
            (fun () ->
               let s1 = sprintf "%s(struct" pc.bef in
               let s2 =
                 vlist str_item
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   sil
               in
               sprintf "%s\n%s" s1 s2)
      | <:module_expr< $me1$ $me2$ >> ->
          plist curr 0 (paren pc "") [(me1, ""); (me2, "")]
      | <:module_expr< ($me$ : $mt$) >> ->
          plistbf 0 (paren pc ":")
            [(fun pc -> curr pc me, ""); (fun pc -> module_type pc mt, "")]
      | <:module_expr< $me1$ . $me2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} me1)
             (curr {(pc) with bef = ""} me2)
      | <:module_expr< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | x ->
          not_impl "module_expr" pc x ] ]
  ;
  pr_module_type:
    [ "top"
      [ <:module_type< functor ($uid:i$ : $mt1$) -> $mt2$ >> ->
          plistbf 0 (paren pc "functor")
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> curr pc mt1, "");
             (fun pc -> curr pc mt2, "")]
      | <:module_type< sig $list:sil$ end >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(sig %s)%s" pc.bef
                 (hlist sig_item {(pc) with bef = ""; aft = ""} sil) pc.aft)
            (fun () ->
               let s1 = sprintf "%s(sig" pc.bef in
               let s2 =
                 vlist sig_item
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   sil
               in
               sprintf "%s\n%s" s1 s2)
      | <:module_type< $mt$ with $list:wcl$ >> ->
          pprintf pc "(with %p@;<1 1>%p)" curr mt (hlist with_constraint) wcl
      | <:module_type< $me1$ . $me2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} me1)
             (curr {(pc) with bef = ""} me2)
      | <:module_type< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | x ->
          not_impl "module_type" pc x ] ]
  ;
  pr_class_sig_item:
    [ [ <:class_sig_item< method $flag:pf$ $s$ : $t$ >> ->
          let list =
            let list =
              [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
               (fun pc -> ctyp pc t, "")]
            in
            if pf then
              [(fun pc -> sprintf "%sprivate%s" pc.bef pc.aft, "") :: list]
            else list
          in
          plistbf 0 (paren pc "method") list
      | <:class_sig_item< value $flag:mf$ $s$ : $t$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(value%s %s %s)%s" pc.bef
                 (if mf then " mutable" else "") s
                 (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
            (fun () -> not_impl "class_sig_item value vertic" pc 0)
      | x ->
          not_impl "class_sig_item" pc x ] ]
  ;
  pr_class_str_item:
    [ [ <:class_str_item< inherit $ce$ $opt:so$ >> ->
          let list =
            match so with
            [ Some s -> [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "")]
            | None -> [] ]
          in
          plistbf 0 (paren pc "inherit")
            [(fun pc -> class_expr pc ce, "") :: list]
      | <:class_str_item< initializer $e$ >> ->
          plistb expr 0 (paren pc "initializer") [(e, "")]
      | <:class_str_item< method $priv:pf$ $s$ = $e$ >> ->
          let (pl, e) = expr_fun_args e in
          let list =
            let list =
              [(fun pc ->
                  match pl with
                  [ [] -> sprintf "%s%s%s" pc.bef s pc.aft
                  | pl ->
                      plistf 0 (paren pc "")
                        [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "") ::
                         List.map (fun p -> (fun pc -> patt pc p, "")) pl] ],
                "");
               (fun pc -> expr pc e, "")]
            in
            if pf then
              [(fun pc -> sprintf "%sprivate%s" pc.bef pc.aft, "") :: list]
            else list
          in
          plistbf 0 (paren pc "method") list
      | <:class_str_item< method virtual $flag:pf$ $s$ : $t$ >> ->
          let list =
            let list =
              [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
               (fun pc -> ctyp pc t, "")]
            in
            let list =
              if pf then
                [(fun pc -> sprintf "%sprivate%s" pc.bef pc.aft, "") :: list]
              else list
            in
            [(fun pc -> sprintf "%svirtual%s" pc.bef pc.aft, "") :: list]
          in
          plistbf 0 (paren pc "method") list
      | <:class_str_item< value $flag:mf$ $s$ = $e$ >> ->
          let list =
            let list =
              [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
               (fun pc -> expr pc e, "")]
            in
            if mf then
              [(fun pc -> sprintf "%smutable%s" pc.bef pc.aft, "") :: list]
            else list
          in
          plistbf 0 (paren pc "value") list
      | <:class_str_item< type $t1$ = $t2$ >> ->
          pprintf pc "(type %p@;<1 1>%p)" ctyp t1 ctyp t2
      | x ->
          not_impl "class_str_item" pc x ] ]
  ;
  pr_class_type:
    [ [ <:class_type< [ $t$ ] -> $ct$ >> ->
          let (rtl, ct) =
            loop [t] ct where rec loop rtl =
              fun
              [ <:class_type< [ $t$ ] -> $ct$ >> -> loop [t :: rtl] ct
              | ct -> (rtl, ct) ]
          in
          plistbf 0 (paren pc "->")
            (List.rev
               [(fun pc -> class_type pc ct, "") ::
                List.map (fun t -> (fun pc -> ctyp pc t, "")) rtl])
      | <:class_type< object $opt:cst$ $list:csl$ end >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(object%s %s)%s" pc.bef
                 (match cst with
                  [ Some t -> not_impl "class_type object self horiz " pc 0
                  | None -> "" ])
                 (hlist class_sig_item {(pc) with bef = ""; aft = ""} csl)
                    pc.aft)
            (fun () ->
               let s1 =
                 let s = sprintf "%s(object" pc.bef in
                 match cst with
                 [ Some t -> not_impl "class_type object self vertic" pc 0
                 | None -> s ]
               in
               let s2 =
                 vlist class_sig_item
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   csl
               in
               sprintf "%s\n%s" s1 s2)
      | x ->
          not_impl "class_type" pc x ] ]
  ;
  pr_class_expr:
    [ [ <:class_expr< let $flag:rf$ $list:lbl$ in $ce$ >> ->
          let list =
            [(fun pc ->
                plistf 0 (paren pc "")
                  (List.map (fun lb -> (fun pc -> let_binding pc lb, ""))
                     lbl),
              "");
             (fun pc -> curr pc ce, "")]
          in
          plistbf 0 (paren pc (if rf then "letrec" else "let")) list
      | <:class_expr< fun $p$ -> $ce$ >> ->
          let (pl, ce) =
            loop ce where rec loop =
              fun
              [ <:class_expr< fun $p$ -> $ce$ >> as gce ->
                  if is_irrefut_patt p then
                    let (pl, ce) = loop ce in
                    ([p :: pl], ce)
                  else ([], gce)
              | ce -> ([], ce) ]
          in
          plistbf 0 (paren pc "lambda")
            [(fun pc ->
                match pl with
                [ [] -> patt pc p
                | pl ->
                    plistf 0 (paren pc "")
                      (List.map (fun p -> (fun pc -> patt pc p, ""))
                         [p :: pl]) ],
              "");
             (fun pc -> curr pc ce, "")]
      | <:class_expr< object $opt:csp$ $list:csl$ end >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(object%s %s)%s" pc.bef
                 (match csp with
                  [ Some t -> not_impl "class_expr object self horiz " pc 0
                  | None -> " ()" ])
                 (hlist class_str_item {(pc) with bef = ""; aft = ""} csl)
                    pc.aft)
            (fun () ->
               let s1 =
                 let s = sprintf "%s(object" pc.bef in
                 match csp with
                 [ Some p ->
                     plistb patt 0
                       {(pc) with ind = pc.ind + 1; bef = s; aft = ""}
                       [(p, "")]
                 | None -> sprintf "%s ()" s ]
               in
               let s2 =
                 vlist class_str_item
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   csl
               in
               sprintf "%s\n%s" s1 s2)
      | <:class_expr< $ce$ $e$ >> ->
          let (ce, el) =
            loop [e] ce where rec loop el =
              fun
              [ <:class_expr< $ce$ $e$ >> -> loop [e :: el] ce
              | ce -> (ce, el) ]
          in
          plistf 0 (paren pc "")
            [(fun pc -> curr pc ce, "") ::
             List.map (fun e -> (fun pc -> expr pc e, "")) el]
      | <:class_expr< $list:sl$ >> ->
          longident pc sl
      | <:class_expr< [ $list:ctcl$ ] $list:sl$ >> ->
          not_impl "CeCon" pc sl
      | x ->
          not_impl "class_expr" pc x ] ]
  ;
END;

(* main part *)

value sep = Pcaml.inter_phrases;

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
    value buff = ref (string_create 80);
    value store len x = do {
      if len >= string_length buff.val then
        buff.val :=
          string_cat buff.val (string_create (string_length buff.val))
      else ();
      string_set buff.val len x;
      succ len
    };
    value mstore len s =
      add_rec len 0 where rec add_rec len i =
        if i == String.length s then len
        else add_rec (store len s.[i]) (succ i)
    ;
    value get len = bytes_to_string (string_sub buff.val 0 len);
  end
;

value first_loc_of_ast =
  fun
  [ [(_, loc) :: _] -> loc
  | [] -> Ploc.dummy ]
;

value apply_printer f (ast, eoi_loc) = do {
  let loc = first_loc_of_ast ast in
  let fname = Ploc.file_name loc in
  let src =
    if fname = "-" then do { sep.val := Some "\n"; "" }
    else do {
      let ic = open_in_bin fname in
      let src =
        loop 0 where rec loop len =
          match try Some (input_char ic) with [ End_of_file -> None ] with
          [ Some c -> loop (Buff.store len c)
          | None -> Buff.get len ]
      in
      close_in ic;
      src
    }
  in
  let oc =
    match Pcaml.output_file.val with
    [ Some f -> open_out_bin f
    | None -> do { pervasives_set_binary_mode_out stdout True; stdout } ]
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
           copy_source src oc first last_pos bp;
           flush oc;
           output_string oc (f {ind = 0; bef = ""; aft = ""; dang = ""} si);
           (False, ep)
         })
        (True, 0) ast
    in
    copy_to_end src oc first last_pos;
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
