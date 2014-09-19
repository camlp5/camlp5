(* camlp5r *)
(* q_MLast.ml,v *)
(* Copyright (c) INRIA 2007-2014 *)

(* #load "pa_extend.cmo" *)
(* #load "pa_extend_m.cmo" *)
(* #load "q_MLast.cmo" *)
(* #load "pa_macro.cmo" *)

(* *)

let gram = Grammar.gcreate (Plexer.gmake ());;

let antiquot k loc s f =
  let shift_bp =
    if k = "" then String.length "$"
    else String.length "$" + String.length k + String.length ":"
  in
  let shift_ep = String.length "$" in
  let loc =
    Ploc.make_loc (Ploc.file_name loc) (Ploc.line_nb loc) (Ploc.bol_pos loc)
      (Ploc.first_pos loc + shift_bp, Ploc.last_pos loc - shift_ep) ""
  in
  try loc, Grammar.Entry.parse f (Stream.of_string s) with
    Ploc.Exc (loc1, exc) ->
      let shift = Ploc.first_pos loc in
      let loc =
        Ploc.make_loc (Ploc.file_name loc)
          (Ploc.line_nb loc + Ploc.line_nb loc1 - 1)
          (if Ploc.line_nb loc1 = 1 then Ploc.bol_pos loc
           else shift + Ploc.bol_pos loc1)
          (shift + Ploc.first_pos loc1, shift + Ploc.last_pos loc1) ""
      in
      raise (Ploc.Exc (loc, exc))
;;

module Qast =
  struct
    type t =
        Node of string * t list
      | List of t list
      | Tuple of t list
      | Option of t option
      | Int of string
      | Str of string
      | Bool of bool
      | Cons of t * t
      | Apply of string * t list
      | Record of (string * t) list
      | Loc
      | TrueLoc
      | VaAnt of string * MLast.loc * string
      | VaVal of t
    ;;
    let loc = Ploc.dummy;;
    let expr_node m n =
      if m = "" then MLast.ExUid (loc, n)
      else MLast.ExAcc (loc, MLast.ExUid (loc, m), MLast.ExUid (loc, n))
    ;;
    let patt_node m n =
      if m = "" then MLast.PaUid (loc, n)
      else MLast.PaAcc (loc, MLast.PaUid (loc, m), MLast.PaUid (loc, n))
    ;;
    let patt_label m n =
      if m = "" then MLast.PaLid (loc, n)
      else MLast.PaAcc (loc, MLast.PaUid (loc, m), MLast.PaLid (loc, n))
    ;;
    let rec to_expr m =
      function
        Node (n, al) ->
          List.fold_left (fun e a -> MLast.ExApp (loc, e, to_expr m a))
            (expr_node m n) al
      | List al ->
          List.fold_right
            (fun a e ->
               MLast.ExApp
                 (loc,
                  MLast.ExApp (loc, MLast.ExUid (loc, "::"), to_expr m a), e))
            al (MLast.ExUid (loc, "[]"))
      | Tuple al -> MLast.ExTup (loc, List.map (to_expr m) al)
      | Option None -> MLast.ExUid (loc, "None")
      | Option (Some a) ->
          MLast.ExApp (loc, MLast.ExUid (loc, "Some"), to_expr m a)
      | Int s -> MLast.ExInt (loc, s, "")
      | Str s -> MLast.ExStr (loc, s)
      | Bool true -> MLast.ExUid (loc, "True")
      | Bool false -> MLast.ExUid (loc, "False")
      | Cons (a1, a2) ->
          MLast.ExApp
            (loc, MLast.ExApp (loc, MLast.ExUid (loc, "::"), to_expr m a1),
             to_expr m a2)
      | Apply (f, al) ->
          List.fold_left (fun e a -> MLast.ExApp (loc, e, to_expr m a))
            (MLast.ExLid (loc, f)) al
      | Record lal -> MLast.ExRec (loc, List.map (to_expr_label m) lal, None)
      | Loc | TrueLoc -> MLast.ExLid (loc, !(Ploc.name))
      | VaAnt (k, loc, x) ->
          let (loc, e) = antiquot k loc x Pcaml.expr_eoi in
          MLast.ExAnt (loc, e)
      | VaVal a ->
          let e = to_expr m a in
          if !(Pcaml.strict_mode) then
            match e with
              MLast.ExAnt (_, ee) ->
                let loc = MLast.loc_of_expr ee in
                let ee =
                  MLast.ExApp
                    (loc,
                     MLast.ExAcc
                       (loc, MLast.ExUid (loc, "Ploc"),
                        MLast.ExUid (loc, "VaVal")),
                     ee)
                in
                let loc = MLast.loc_of_expr e in MLast.ExAnt (loc, ee)
            | _ ->
                MLast.ExApp
                  (loc,
                   MLast.ExAcc
                     (loc, MLast.ExUid (loc, "Ploc"),
                      MLast.ExUid (loc, "VaVal")),
                   e)
          else e
    and to_expr_label m (l, e) = patt_label m l, to_expr m e;;
    let rec to_patt m =
      function
        Node (n, al) ->
          List.fold_left (fun e a -> MLast.PaApp (loc, e, to_patt m a))
            (patt_node m n) al
      | List al ->
          List.fold_right
            (fun a p ->
               MLast.PaApp
                 (loc,
                  MLast.PaApp (loc, MLast.PaUid (loc, "::"), to_patt m a), p))
            al (MLast.PaUid (loc, "[]"))
      | Tuple al -> MLast.PaTup (loc, List.map (to_patt m) al)
      | Option None -> MLast.PaUid (loc, "None")
      | Option (Some a) ->
          MLast.PaApp (loc, MLast.PaUid (loc, "Some"), to_patt m a)
      | Int s -> MLast.PaInt (loc, s, "")
      | Str s -> MLast.PaStr (loc, s)
      | Bool true -> MLast.PaUid (loc, "True")
      | Bool false -> MLast.PaUid (loc, "False")
      | Cons (a1, a2) ->
          MLast.PaApp
            (loc, MLast.PaApp (loc, MLast.PaUid (loc, "::"), to_patt m a1),
             to_patt m a2)
      | Apply (_, _) -> failwith "bad pattern"
      | Record lal -> MLast.PaRec (loc, List.map (to_patt_label m) lal)
      | Loc -> MLast.PaAny loc
      | TrueLoc -> MLast.PaLid (loc, !(Ploc.name))
      | VaAnt (k, loc, x) ->
          let (loc, e) = antiquot k loc x Pcaml.patt_eoi in
          MLast.PaAnt (loc, e)
      | VaVal a ->
          let p = to_patt m a in
          if !(Pcaml.strict_mode) then
            match p with
              MLast.PaAnt (_, pp) ->
                let loc = MLast.loc_of_patt pp in
                let pp =
                  MLast.PaApp
                    (loc,
                     MLast.PaAcc
                       (loc, MLast.PaUid (loc, "Ploc"),
                        MLast.PaUid (loc, "VaVal")),
                     pp)
                in
                let loc = MLast.loc_of_patt p in MLast.PaAnt (loc, pp)
            | _ ->
                MLast.PaApp
                  (loc,
                   MLast.PaAcc
                     (loc, MLast.PaUid (loc, "Ploc"),
                      MLast.PaUid (loc, "VaVal")),
                   p)
          else p
    and to_patt_label m (l, a) = patt_label m l, to_patt m a;;
  end
;;

let sig_item = Grammar.Entry.create gram "sig_item";;
let str_item = Grammar.Entry.create gram "str_item";;
let ctyp = Grammar.Entry.create gram "type";;
let patt = Grammar.Entry.create gram "patt";;
let expr = Grammar.Entry.create gram "expr";;

let module_type = Grammar.Entry.create gram "module_type";;
let module_expr = Grammar.Entry.create gram "module_expr";;

let structure = Grammar.Entry.create gram "structure";;
let signature = Grammar.Entry.create gram "signature";;

let class_type = Grammar.Entry.create gram "class_type";;
let class_expr = Grammar.Entry.create gram "class_expr";;
let class_sig_item = Grammar.Entry.create gram "class_sig_item";;
let class_str_item = Grammar.Entry.create gram "class_str_item";;

let ipatt = Grammar.Entry.create gram "ipatt";;
let let_binding = Grammar.Entry.create gram "let_binding";;
let type_decl = Grammar.Entry.create gram "type_decl";;
let match_case = Grammar.Entry.create gram "match_case";;
let constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration"
;;
let label_declaration = Grammar.Entry.create gram "label_declaration";;

let with_constr = Grammar.Entry.create gram "with_constr";;
let poly_variant = Grammar.Entry.create gram "poly_variant";;

let mksequence2 _ =
  function
    Qast.VaVal (Qast.List [e]) -> e
  | el -> Qast.Node ("ExSeq", [Qast.Loc; el])
;;

let mksequence _ =
  function
    Qast.List [e] -> e
  | el -> Qast.Node ("ExSeq", [Qast.Loc; Qast.VaVal el])
;;

let mkmatchcase _ p aso w e =
  let p =
    match aso with
      Qast.Option (Some p2) -> Qast.Node ("PaAli", [Qast.Loc; p; p2])
    | Qast.Option None -> p
    | _ -> Qast.Node ("PaAli", [Qast.Loc; p; aso])
  in
  Qast.Tuple [p; w; e]
;;

let neg_string n =
  let x =
    let len = String.length n in
    if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1) else "-" ^ n
  in
  Qast.Str x
;;

let mklistexp _ last =
  let rec loop top =
    function
      [] ->
        begin match last with
          Qast.Option (Some e) -> e
        | Qast.Option None ->
            Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")])
        | a -> a
        end
    | e1 :: el ->
        Qast.Node
          ("ExApp",
           [Qast.Loc;
            Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "::")]);
                e1]);
            loop false el])
  in
  loop true
;;

let mklistpat _ last =
  let rec loop top =
    function
      [] ->
        begin match last with
          Qast.Option (Some p) -> p
        | Qast.Option None ->
            Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")])
        | a -> a
        end
    | p1 :: pl ->
        Qast.Node
          ("PaApp",
           [Qast.Loc;
            Qast.Node
              ("PaApp",
               [Qast.Loc;
                Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "::")]);
                p1]);
            loop false pl])
  in
  loop true
;;

let mktupexp _ e el =
  Qast.Node ("ExTup", [Qast.Loc; Qast.VaVal (Qast.Cons (e, Qast.List el))])
;;

let mktuppat _ p pl =
  Qast.Node ("PaTup", [Qast.Loc; Qast.VaVal (Qast.Cons (p, Qast.List pl))])
;;

let mktuptyp _ t tl =
  Qast.Node ("TyTup", [Qast.Loc; Qast.VaVal (Qast.Cons (t, Qast.List tl))])
;;

let mklabdecl _ i mf t = Qast.Tuple [Qast.Loc; Qast.Str i; Qast.Bool mf; t];;
let mkident i = Qast.Str i;;

let generalized_type_of_type t =
  let rec gen =
    function
      Qast.Node ("TyArr", [_; t1; t2]) ->
        let (tl, rt) = gen t2 in t1 :: tl, rt
    | t -> [], t
  in
  let (tl, rt) = gen t in Qast.List tl, rt
;;

let greek_ascii_equiv s = Qast.Str (Pcaml.greek_ascii_equiv s);;

let warned = ref false;;
let warning_deprecated_since_6_00 loc =
  if not !warned then
    begin
      !(Pcaml.warning) loc "syntax deprecated since version 6.00";
      warned := true
    end
;;

(* -- begin copy from pa_r to q_MLast -- *)

Grammar.extend
  (let _ = (sig_item : 'sig_item Grammar.Entry.e)
   and _ = (str_item : 'str_item Grammar.Entry.e)
   and _ = (ctyp : 'ctyp Grammar.Entry.e)
   and _ = (patt : 'patt Grammar.Entry.e)
   and _ = (expr : 'expr Grammar.Entry.e)
   and _ = (module_type : 'module_type Grammar.Entry.e)
   and _ = (module_expr : 'module_expr Grammar.Entry.e)
   and _ = (signature : 'signature Grammar.Entry.e)
   and _ = (structure : 'structure Grammar.Entry.e)
   and _ = (class_type : 'class_type Grammar.Entry.e)
   and _ = (class_expr : 'class_expr Grammar.Entry.e)
   and _ = (class_sig_item : 'class_sig_item Grammar.Entry.e)
   and _ = (class_str_item : 'class_str_item Grammar.Entry.e)
   and _ = (let_binding : 'let_binding Grammar.Entry.e)
   and _ = (type_decl : 'type_decl Grammar.Entry.e)
   and _ =
     (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
   and _ = (label_declaration : 'label_declaration Grammar.Entry.e)
   and _ = (match_case : 'match_case Grammar.Entry.e)
   and _ = (ipatt : 'ipatt Grammar.Entry.e)
   and _ = (with_constr : 'with_constr Grammar.Entry.e)
   and _ = (poly_variant : 'poly_variant Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry sig_item) s
   in
   let rebind_exn : 'rebind_exn Grammar.Entry.e =
     grammar_entry_create "rebind_exn"
   and mod_binding : 'mod_binding Grammar.Entry.e =
     grammar_entry_create "mod_binding"
   and mod_fun_binding : 'mod_fun_binding Grammar.Entry.e =
     grammar_entry_create "mod_fun_binding"
   and mod_type_fun_binding : 'mod_type_fun_binding Grammar.Entry.e =
     grammar_entry_create "mod_type_fun_binding"
   and mod_decl_binding : 'mod_decl_binding Grammar.Entry.e =
     grammar_entry_create "mod_decl_binding"
   and module_declaration : 'module_declaration Grammar.Entry.e =
     grammar_entry_create "module_declaration"
   and cons_expr_opt : 'cons_expr_opt Grammar.Entry.e =
     grammar_entry_create "cons_expr_opt"
   and dummy : 'dummy Grammar.Entry.e = grammar_entry_create "dummy"
   and sequence : 'sequence Grammar.Entry.e = grammar_entry_create "sequence"
   and fun_binding : 'fun_binding Grammar.Entry.e =
     grammar_entry_create "fun_binding"
   and as_patt_opt : 'as_patt_opt Grammar.Entry.e =
     grammar_entry_create "as_patt_opt"
   and when_expr : 'when_expr Grammar.Entry.e =
     grammar_entry_create "when_expr"
   and label_expr : 'label_expr Grammar.Entry.e =
     grammar_entry_create "label_expr"
   and fun_def : 'fun_def Grammar.Entry.e = grammar_entry_create "fun_def"
   and paren_patt : 'paren_patt Grammar.Entry.e =
     grammar_entry_create "paren_patt"
   and cons_patt_opt : 'cons_patt_opt Grammar.Entry.e =
     grammar_entry_create "cons_patt_opt"
   and label_patt : 'label_patt Grammar.Entry.e =
     grammar_entry_create "label_patt"
   and patt_label_ident : 'patt_label_ident Grammar.Entry.e =
     grammar_entry_create "patt_label_ident"
   and paren_ipatt : 'paren_ipatt Grammar.Entry.e =
     grammar_entry_create "paren_ipatt"
   and label_ipatt : 'label_ipatt Grammar.Entry.e =
     grammar_entry_create "label_ipatt"
   and type_patt : 'type_patt Grammar.Entry.e =
     grammar_entry_create "type_patt"
   and constrain : 'constrain Grammar.Entry.e =
     grammar_entry_create "constrain"
   and type_parameter : 'type_parameter Grammar.Entry.e =
     grammar_entry_create "type_parameter"
   and simple_type_parameter : 'simple_type_parameter Grammar.Entry.e =
     grammar_entry_create "simple_type_parameter"
   and ident : 'ident Grammar.Entry.e = grammar_entry_create "ident"
   and mod_ident : 'mod_ident Grammar.Entry.e =
     grammar_entry_create "mod_ident"
   and class_declaration : 'class_declaration Grammar.Entry.e =
     grammar_entry_create "class_declaration"
   and class_fun_binding : 'class_fun_binding Grammar.Entry.e =
     grammar_entry_create "class_fun_binding"
   and class_type_parameters : 'class_type_parameters Grammar.Entry.e =
     grammar_entry_create "class_type_parameters"
   and class_fun_def : 'class_fun_def Grammar.Entry.e =
     grammar_entry_create "class_fun_def"
   and class_structure : 'class_structure Grammar.Entry.e =
     grammar_entry_create "class_structure"
   and class_self_patt : 'class_self_patt Grammar.Entry.e =
     grammar_entry_create "class_self_patt"
   and as_lident : 'as_lident Grammar.Entry.e =
     grammar_entry_create "as_lident"
   and polyt : 'polyt Grammar.Entry.e = grammar_entry_create "polyt"
   and cvalue_binding : 'cvalue_binding Grammar.Entry.e =
     grammar_entry_create "cvalue_binding"
   and lident : 'lident Grammar.Entry.e = grammar_entry_create "lident"
   and class_self_type : 'class_self_type Grammar.Entry.e =
     grammar_entry_create "class_self_type"
   and class_description : 'class_description Grammar.Entry.e =
     grammar_entry_create "class_description"
   and class_type_declaration : 'class_type_declaration Grammar.Entry.e =
     grammar_entry_create "class_type_declaration"
   and field_expr : 'field_expr Grammar.Entry.e =
     grammar_entry_create "field_expr"
   and field : 'field Grammar.Entry.e = grammar_entry_create "field"
   and typevar : 'typevar Grammar.Entry.e = grammar_entry_create "typevar"
   and class_longident : 'class_longident Grammar.Entry.e =
     grammar_entry_create "class_longident"
   and poly_variant_list : 'poly_variant_list Grammar.Entry.e =
     grammar_entry_create "poly_variant_list"
   and name_tag : 'name_tag Grammar.Entry.e = grammar_entry_create "name_tag"
   and patt_tcon_opt_eq_patt : 'patt_tcon_opt_eq_patt Grammar.Entry.e =
     grammar_entry_create "patt_tcon_opt_eq_patt"
   and patt_tcon : 'patt_tcon Grammar.Entry.e =
     grammar_entry_create "patt_tcon"
   and ipatt_tcon_opt_eq_patt : 'ipatt_tcon_opt_eq_patt Grammar.Entry.e =
     grammar_entry_create "ipatt_tcon_opt_eq_patt"
   and ipatt_tcon : 'ipatt_tcon Grammar.Entry.e =
     grammar_entry_create "ipatt_tcon"
   and patt_option_label : 'patt_option_label Grammar.Entry.e =
     grammar_entry_create "patt_option_label"
   and ipatt_tcon_fun_binding : 'ipatt_tcon_fun_binding Grammar.Entry.e =
     grammar_entry_create "ipatt_tcon_fun_binding"
   and direction_flag : 'direction_flag Grammar.Entry.e =
     grammar_entry_create "direction_flag"
   and joinautomaton : 'joinautomaton Grammar.Entry.e =
     grammar_entry_create "joinautomaton"
   and joinclause : 'joinclause Grammar.Entry.e =
     grammar_entry_create "joinclause"
   and joinpattern : 'joinpattern Grammar.Entry.e =
     grammar_entry_create "joinpattern"
   and a_ti : 'a_ti Grammar.Entry.e =
     (* -- end copy from pa_r to q_MLast -- *)
     grammar_entry_create "a_ti"
   and a_tic : 'a_tic Grammar.Entry.e = grammar_entry_create "a_tic"
   and a_qi : 'a_qi Grammar.Entry.e = grammar_entry_create "a_qi"
   and a_qic : 'a_qic Grammar.Entry.e = grammar_entry_create "a_qic"
   and joinident : 'joinident Grammar.Entry.e =
     grammar_entry_create "joinident"
   in
   [Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "struct");
       Gramext.Snterm
         (Grammar.Entry.obj (structure : 'structure Grammar.Entry.e));
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (st : 'structure) _ (loc : Ploc.t) ->
           (Qast.Node ("MeStr", [Qast.Loc; st]) : 'module_expr));
      [Gramext.Stoken ("", "functor"); Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__1));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__1));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__1));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__1));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__1))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
       Gramext.Stoken ("", ")"); Gramext.Stoken ("", "->"); Gramext.Sself],
      Gramext.action
        (fun (me : 'module_expr) _ _ (t : 'module_type) _ (i : 'e__1) _ _
             (loc : Ploc.t) ->
           (Qast.Node ("MeFun", [Qast.Loc; i; t; me]) : 'module_expr))];
     None, None,
     [[Gramext.Sself; Gramext.Sself],
      Gramext.action
        (fun (me2 : 'module_expr) (me1 : 'module_expr) (loc : Ploc.t) ->
           (Qast.Node ("MeApp", [Qast.Loc; me1; me2]) : 'module_expr))];
     None, None,
     [[Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (me2 : 'module_expr) _ (me1 : 'module_expr) (loc : Ploc.t) ->
           (Qast.Node ("MeAcc", [Qast.Loc; me1; me2]) : 'module_expr))];
     Some "simple", None,
     [[Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (me : 'module_expr) _ (loc : Ploc.t) -> (me : 'module_expr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (mt : 'module_type) _ (me : 'module_expr) _ (loc : Ploc.t) ->
           (Qast.Node ("MeTyc", [Qast.Loc; me; mt]) : 'module_expr));
      [Gramext.Stoken ("", "("); Gramext.Stoken ("", "value");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (e : 'expr) _ _ (loc : Ploc.t) ->
           (Qast.Node ("MeUnp", [Qast.Loc; e; Qast.Option None]) :
            'module_expr));
      [Gramext.Stoken ("", "("); Gramext.Stoken ("", "value");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (mt : 'module_type) _ (e : 'expr) _ _ (loc : Ploc.t) ->
           (Qast.Node ("MeUnp", [Qast.Loc; e; Qast.Option (Some mt)]) :
            'module_expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__2));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__2));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__2));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__2));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__2))])],
      Gramext.action
        (fun (i : 'e__2) (loc : Ploc.t) ->
           (Qast.Node ("MeUid", [Qast.Loc; i]) : 'module_expr))]];
    Grammar.Entry.obj (structure : 'structure Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (str_item : 'str_item Grammar.Entry.e));
                     Gramext.Stoken ("", ";")],
                    Gramext.action
                      (fun _ (s : 'str_item) (loc : Ploc.t) ->
                         (s : 'e__3))])],
             Gramext.action
               (fun (a : 'e__3 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__4));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__4));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__4))])],
      Gramext.action (fun (st : 'e__4) (loc : Ploc.t) -> (st : 'structure))]];
    Grammar.Entry.obj (str_item : 'str_item Grammar.Entry.e), None,
    [Some "top", None,
     [[Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("StExp", [Qast.Loc; e]) : 'str_item));
      [Gramext.Stoken ("", "#");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("STRING", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__18));
             [Gramext.Stoken ("ANTIQUOT", "_str")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_str", loc, a) : 'e__18));
             [Gramext.Stoken ("ANTIQUOT", "str")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("str", loc, a)) : 'e__18))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (str_item : 'str_item Grammar.Entry.e))],
                    Gramext.action
                      (fun (si : 'str_item) (loc : Ploc.t) ->
                         (Qast.Tuple [si; Qast.Loc] : 'e__19))])],
             Gramext.action
               (fun (a : 'e__19 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__20));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__20));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__20))])],
      Gramext.action
        (fun (sil : 'e__20) (s : 'e__18) _ (loc : Ploc.t) ->
           (Qast.Node ("StUse", [Qast.Loc; s; sil]) : 'str_item));
      [Gramext.Stoken ("", "#");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__16));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__16));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__16));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__16));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__16))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'expr option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__17));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__17));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__17))])],
      Gramext.action
        (fun (dp : 'e__17) (n : 'e__16) _ (loc : Ploc.t) ->
           (Qast.Node ("StDir", [Qast.Loc; n; dp]) : 'str_item));
      [Gramext.Stoken ("", "value");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "rec"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__14));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__14));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__14));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__14));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__14))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (let_binding : 'let_binding Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'let_binding list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__15));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__15));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__15))])],
      Gramext.action
        (fun (l : 'e__15) (r : 'e__14) _ (loc : Ploc.t) ->
           (Qast.Node ("StVal", [Qast.Loc; r; l]) : 'str_item));
      [Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (type_decl : 'type_decl Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'type_decl list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__13));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__13));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__13))])],
      Gramext.action
        (fun (tdl : 'e__13) _ (loc : Ploc.t) ->
           (Qast.Node ("StTyp", [Qast.Loc; tdl]) : 'str_item));
      [Gramext.Stoken ("", "open");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'mod_ident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__12));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__12));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__12));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__12));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__12))])],
      Gramext.action
        (fun (i : 'e__12) _ (loc : Ploc.t) ->
           (Qast.Node ("StOpn", [Qast.Loc; i]) : 'str_item));
      [Gramext.Stoken ("", "module"); Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'ident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__11));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__11));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__11))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (mod_type_fun_binding : 'mod_type_fun_binding Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'mod_type_fun_binding) (i : 'e__11) _ _ (loc : Ploc.t) ->
           (Qast.Node ("StMty", [Qast.Loc; i; mt]) : 'str_item));
      [Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "rec"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__9));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__9));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__9));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__9));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__9))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (mod_binding : 'mod_binding Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'mod_binding list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__10));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__10));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__10))])],
      Gramext.action
        (fun (l : 'e__10) (r : 'e__9) _ (loc : Ploc.t) ->
           (Qast.Node ("StMod", [Qast.Loc; r; l]) : 'str_item));
      [Gramext.Stoken ("", "include");
       Gramext.Snterm
         (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr) _ (loc : Ploc.t) ->
           (Qast.Node ("StInc", [Qast.Loc; me]) : 'str_item));
      [Gramext.Stoken ("", "external");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__7));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__7));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__7));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__7));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__7))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1 (Gramext.Stoken ("STRING", ""))],
             Gramext.action
               (fun (a : string list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List (List.map (fun a -> Qast.Str a) a)) :
                   'e__8));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__8));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__8))])],
      Gramext.action
        (fun (pd : 'e__8) _ (t : 'ctyp) _ (i : 'e__7) _ (loc : Ploc.t) ->
           (Qast.Node ("StExt", [Qast.Loc; i; t; pd]) : 'str_item));
      [Gramext.Stoken ("", "exception");
       Gramext.Snterm
         (Grammar.Entry.obj
            (constructor_declaration :
             'constructor_declaration Grammar.Entry.e));
       Gramext.Snterm
         (Grammar.Entry.obj (rebind_exn : 'rebind_exn Grammar.Entry.e))],
      Gramext.action
        (fun (b : 'rebind_exn) (ctl : 'constructor_declaration) _
             (loc : Ploc.t) ->
           (let (_, c, tl, _) =
              match ctl with
                Qast.Tuple [xx1; xx2; xx3; xx4] -> xx1, xx2, xx3, xx4
              | _ -> raise (Match_failure ("q_MLast.ml", 313, 20))
            in
            Qast.Node ("StExc", [Qast.Loc; c; tl; b]) :
            'str_item));
      [Gramext.Stoken ("", "declare");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (str_item : 'str_item Grammar.Entry.e));
                     Gramext.Stoken ("", ";")],
                    Gramext.action
                      (fun _ (s : 'str_item) (loc : Ploc.t) ->
                         (s : 'e__5))])],
             Gramext.action
               (fun (a : 'e__5 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__6));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__6));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__6))]);
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (st : 'e__6) _ (loc : Ploc.t) ->
           (Qast.Node ("StDcl", [Qast.Loc; st]) : 'str_item))]];
    Grammar.Entry.obj (rebind_exn : 'rebind_exn Grammar.Entry.e), None,
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> (Qast.VaVal (Qast.List []) : 'rebind_exn));
      [Gramext.Stoken ("", "=");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'mod_ident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__21));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__21));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__21));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__21));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__21))])],
      Gramext.action
        (fun (a : 'e__21) _ (loc : Ploc.t) -> (a : 'rebind_exn))]];
    Grammar.Entry.obj (mod_binding : 'mod_binding Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__22));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__22));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__22));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__22));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__22))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e))],
      Gramext.action
        (fun (me : 'mod_fun_binding) (i : 'e__22) (loc : Ploc.t) ->
           (Qast.Tuple [i; me] : 'mod_binding))]];
    Grammar.Entry.obj (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e),
    None,
    [None, Some Gramext.RightA,
     [[Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr) _ (loc : Ploc.t) -> (me : 'mod_fun_binding));
      [Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr) _ (mt : 'module_type) _ (loc : Ploc.t) ->
           (Qast.Node ("MeTyc", [Qast.Loc; me; mt]) : 'mod_fun_binding));
      [Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__23));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__23));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__23));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__23));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__23))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
       Gramext.Stoken ("", ")"); Gramext.Sself],
      Gramext.action
        (fun (mb : 'mod_fun_binding) _ (mt : 'module_type) _ (m : 'e__23) _
             (loc : Ploc.t) ->
           (Qast.Node ("MeFun", [Qast.Loc; m; mt; mb]) : 'mod_fun_binding))]];
    Grammar.Entry.obj
      (mod_type_fun_binding : 'mod_type_fun_binding Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'module_type) _ (loc : Ploc.t) ->
           (mt : 'mod_type_fun_binding));
      [Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__24));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__24));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__24));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__24));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__24))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
       Gramext.Stoken ("", ")"); Gramext.Sself],
      Gramext.action
        (fun (mt2 : 'mod_type_fun_binding) _ (mt1 : 'module_type) _
             (m : 'e__24) _ (loc : Ploc.t) ->
           (Qast.Node ("MtFun", [Qast.Loc; m; mt1; mt2]) :
            'mod_type_fun_binding))]];
    Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "functor"); Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__25));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__25));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__25));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__25));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__25))]);
       Gramext.Stoken ("", ":"); Gramext.Sself; Gramext.Stoken ("", ")");
       Gramext.Stoken ("", "->"); Gramext.Sself],
      Gramext.action
        (fun (mt : 'module_type) _ _ (t : 'module_type) _ (i : 'e__25) _ _
             (loc : Ploc.t) ->
           (Qast.Node ("MtFun", [Qast.Loc; i; t; mt]) : 'module_type))];
     None, None,
     [[Gramext.Sself; Gramext.Stoken ("", "with");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (with_constr : 'with_constr Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'with_constr list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__26));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__26));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__26))])],
      Gramext.action
        (fun (wcl : 'e__26) _ (mt : 'module_type) (loc : Ploc.t) ->
           (Qast.Node ("MtWit", [Qast.Loc; mt; wcl]) : 'module_type))];
     None, None,
     [[Gramext.Stoken ("", "module"); Gramext.Stoken ("", "type");
       Gramext.Stoken ("", "of");
       Gramext.Snterm
         (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr) _ _ _ (loc : Ploc.t) ->
           (Qast.Node ("MtTyo", [Qast.Loc; me]) : 'module_type));
      [Gramext.Stoken ("", "sig");
       Gramext.Snterm
         (Grammar.Entry.obj (signature : 'signature Grammar.Entry.e));
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (sg : 'signature) _ (loc : Ploc.t) ->
           (Qast.Node ("MtSig", [Qast.Loc; sg]) : 'module_type))];
     None, None,
     [[Gramext.Sself; Gramext.Sself],
      Gramext.action
        (fun (m2 : 'module_type) (m1 : 'module_type) (loc : Ploc.t) ->
           (Qast.Node ("MtApp", [Qast.Loc; m1; m2]) : 'module_type))];
     None, None,
     [[Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (m2 : 'module_type) _ (m1 : 'module_type) (loc : Ploc.t) ->
           (Qast.Node ("MtAcc", [Qast.Loc; m1; m2]) : 'module_type))];
     Some "simple", None,
     [[Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (mt : 'module_type) _ (loc : Ploc.t) -> (mt : 'module_type));
      [Gramext.Stoken ("", "'");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'ident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__29));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__29));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__29))])],
      Gramext.action
        (fun (i : 'e__29) _ (loc : Ploc.t) ->
           (Qast.Node ("MtQuo", [Qast.Loc; i]) : 'module_type));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__28));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__28));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__28));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__28));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__28))])],
      Gramext.action
        (fun (i : 'e__28) (loc : Ploc.t) ->
           (Qast.Node ("MtLid", [Qast.Loc; i]) : 'module_type));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__27));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__27));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__27));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__27));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__27))])],
      Gramext.action
        (fun (i : 'e__27) (loc : Ploc.t) ->
           (Qast.Node ("MtUid", [Qast.Loc; i]) : 'module_type))]];
    Grammar.Entry.obj (signature : 'signature Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (sig_item : 'sig_item Grammar.Entry.e));
                     Gramext.Stoken ("", ";")],
                    Gramext.action
                      (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                         (s : 'e__30))])],
             Gramext.action
               (fun (a : 'e__30 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__31));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__31));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__31))])],
      Gramext.action
        (fun (st : 'e__31) (loc : Ploc.t) -> (st : 'signature))]];
    Grammar.Entry.obj (sig_item : 'sig_item Grammar.Entry.e), None,
    [Some "top", None,
     [[Gramext.Stoken ("", "#");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("STRING", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__44));
             [Gramext.Stoken ("ANTIQUOT", "_str")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_str", loc, a) : 'e__44));
             [Gramext.Stoken ("ANTIQUOT", "str")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("str", loc, a)) : 'e__44))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (sig_item : 'sig_item Grammar.Entry.e))],
                    Gramext.action
                      (fun (si : 'sig_item) (loc : Ploc.t) ->
                         (Qast.Tuple [si; Qast.Loc] : 'e__45))])],
             Gramext.action
               (fun (a : 'e__45 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__46));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__46));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__46))])],
      Gramext.action
        (fun (sil : 'e__46) (s : 'e__44) _ (loc : Ploc.t) ->
           (Qast.Node ("SgUse", [Qast.Loc; s; sil]) : 'sig_item));
      [Gramext.Stoken ("", "#");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__42));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__42));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__42));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__42));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__42))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'expr option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__43));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__43));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__43))])],
      Gramext.action
        (fun (dp : 'e__43) (n : 'e__42) _ (loc : Ploc.t) ->
           (Qast.Node ("SgDir", [Qast.Loc; n; dp]) : 'sig_item));
      [Gramext.Stoken ("", "value");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__41));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__41));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__41));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__41));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__41))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (i : 'e__41) _ (loc : Ploc.t) ->
           (Qast.Node ("SgVal", [Qast.Loc; i; t]) : 'sig_item));
      [Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (type_decl : 'type_decl Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'type_decl list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__40));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__40));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__40))])],
      Gramext.action
        (fun (tdl : 'e__40) _ (loc : Ploc.t) ->
           (Qast.Node ("SgTyp", [Qast.Loc; tdl]) : 'sig_item));
      [Gramext.Stoken ("", "open");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'mod_ident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__39));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__39));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__39));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__39));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__39))])],
      Gramext.action
        (fun (i : 'e__39) _ (loc : Ploc.t) ->
           (Qast.Node ("SgOpn", [Qast.Loc; i]) : 'sig_item));
      [Gramext.Stoken ("", "module"); Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'ident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__38));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__38));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__38))]);
       Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'module_type) _ (i : 'e__38) _ _ (loc : Ploc.t) ->
           (Qast.Node ("SgMty", [Qast.Loc; i; mt]) : 'sig_item));
      [Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "rec"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__36));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__36));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__36));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__36));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__36))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (mod_decl_binding : 'mod_decl_binding Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'mod_decl_binding list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__37));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__37));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__37))])],
      Gramext.action
        (fun (l : 'e__37) (rf : 'e__36) _ (loc : Ploc.t) ->
           (Qast.Node ("SgMod", [Qast.Loc; rf; l]) : 'sig_item));
      [Gramext.Stoken ("", "include");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'module_type) _ (loc : Ploc.t) ->
           (Qast.Node ("SgInc", [Qast.Loc; mt]) : 'sig_item));
      [Gramext.Stoken ("", "external");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__34));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__34));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__34));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__34));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__34))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1 (Gramext.Stoken ("STRING", ""))],
             Gramext.action
               (fun (a : string list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List (List.map (fun a -> Qast.Str a) a)) :
                   'e__35));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__35));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__35))])],
      Gramext.action
        (fun (pd : 'e__35) _ (t : 'ctyp) _ (i : 'e__34) _ (loc : Ploc.t) ->
           (Qast.Node ("SgExt", [Qast.Loc; i; t; pd]) : 'sig_item));
      [Gramext.Stoken ("", "exception");
       Gramext.Snterm
         (Grammar.Entry.obj
            (constructor_declaration :
             'constructor_declaration Grammar.Entry.e))],
      Gramext.action
        (fun (ctl : 'constructor_declaration) _ (loc : Ploc.t) ->
           (let (_, c, tl, _) =
              match ctl with
                Qast.Tuple [xx1; xx2; xx3; xx4] -> xx1, xx2, xx3, xx4
              | _ -> raise (Match_failure ("q_MLast.ml", 383, 20))
            in
            Qast.Node ("SgExc", [Qast.Loc; c; tl]) :
            'sig_item));
      [Gramext.Stoken ("", "declare");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (sig_item : 'sig_item Grammar.Entry.e));
                     Gramext.Stoken ("", ";")],
                    Gramext.action
                      (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                         (s : 'e__32))])],
             Gramext.action
               (fun (a : 'e__32 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__33));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__33));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__33))]);
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (st : 'e__33) _ (loc : Ploc.t) ->
           (Qast.Node ("SgDcl", [Qast.Loc; st]) : 'sig_item))]];
    Grammar.Entry.obj (mod_decl_binding : 'mod_decl_binding Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__47));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__47));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__47));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__47));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__47))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (module_declaration : 'module_declaration Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'module_declaration) (i : 'e__47) (loc : Ploc.t) ->
           (Qast.Tuple [i; mt] : 'mod_decl_binding))]];
    Grammar.Entry.obj
      (module_declaration : 'module_declaration Grammar.Entry.e),
    None,
    [None, Some Gramext.RightA,
     [[Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__48));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__48));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__48));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__48));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__48))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
       Gramext.Stoken ("", ")"); Gramext.Sself],
      Gramext.action
        (fun (mt : 'module_declaration) _ (t : 'module_type) _ (i : 'e__48) _
             (loc : Ploc.t) ->
           (Qast.Node ("MtFun", [Qast.Loc; i; t; mt]) : 'module_declaration));
      [Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'module_type) _ (loc : Ploc.t) ->
           (mt : 'module_declaration))]];
    Grammar.Entry.obj (with_constr : 'with_constr Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'mod_ident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__55));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__55));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__55));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__55));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__55))]);
       Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr) _ (i : 'e__55) _ (loc : Ploc.t) ->
           (Qast.Node ("WcMos", [Qast.Loc; i; me]) : 'with_constr));
      [Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'mod_ident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__54));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__54));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__54));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__54));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__54))]);
       Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr) _ (i : 'e__54) _ (loc : Ploc.t) ->
           (Qast.Node ("WcMod", [Qast.Loc; i; me]) : 'with_constr));
      [Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'mod_ident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__52));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__52));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__52));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__52));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__52))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (type_parameter : 'type_parameter Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__53));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__53));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__53))]);
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (tpl : 'e__53) (i : 'e__52) _ (loc : Ploc.t) ->
           (Qast.Node ("WcTys", [Qast.Loc; i; tpl; t]) : 'with_constr));
      [Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'mod_ident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__49));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__49));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__49));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__49));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__49))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (type_parameter : 'type_parameter Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__50));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__50));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__50))]);
       Gramext.Stoken ("", "=");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "private"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__51));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__51));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__51));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__51));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__51))]);
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) (pf : 'e__51) _ (tpl : 'e__50) (i : 'e__49) _
             (loc : Ploc.t) ->
           (Qast.Node ("WcTyp", [Qast.Loc; i; tpl; pf; t]) : 'with_constr))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e), None,
    [Some "top", Some Gramext.RightA,
     [[Gramext.Stoken ("", "while"); Gramext.Sself; Gramext.Stoken ("", "do");
       Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (sequence : 'sequence Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'sequence) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__67));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__67));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__67))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (seq : 'e__67) _ _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExWhi", [Qast.Loc; e; seq]) : 'expr));
      [Gramext.Stoken ("", "for");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__64));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__64));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__64));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__64));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__64))]);
       Gramext.Stoken ("", "="); Gramext.Sself;
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj
                   (direction_flag : 'direction_flag Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'direction_flag) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__65));
             [Gramext.Stoken ("ANTIQUOT", "_to")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_to", loc, a) : 'e__65));
             [Gramext.Stoken ("ANTIQUOT", "to")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("to", loc, a)) : 'e__65))]);
       Gramext.Sself; Gramext.Stoken ("", "do"); Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (sequence : 'sequence Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'sequence) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__66));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__66));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__66))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (seq : 'e__66) _ _ (e2 : 'expr) (df : 'e__65) (e1 : 'expr) _
             (i : 'e__64) _ (loc : Ploc.t) ->
           (Qast.Node ("ExFor", [Qast.Loc; i; e1; e2; df; seq]) : 'expr));
      [Gramext.Stoken ("", "do"); Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (sequence : 'sequence Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'sequence) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__63));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__63));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__63))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (seq : 'e__63) _ _ (loc : Ploc.t) ->
           (mksequence2 Qast.Loc seq : 'expr));
      [Gramext.Stoken ("", "if"); Gramext.Sself; Gramext.Stoken ("", "then");
       Gramext.Sself; Gramext.Stoken ("", "else"); Gramext.Sself],
      Gramext.action
        (fun (e3 : 'expr) _ (e2 : 'expr) _ (e1 : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExIfe", [Qast.Loc; e1; e2; e3]) : 'expr));
      [Gramext.Stoken ("", "try"); Gramext.Sself; Gramext.Stoken ("", "with");
       Gramext.Snterm
         (Grammar.Entry.obj (match_case : 'match_case Grammar.Entry.e))],
      Gramext.action
        (fun (mc : 'match_case) _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExTry", [Qast.Loc; e; Qast.VaVal (Qast.List [mc])]) :
            'expr));
      [Gramext.Stoken ("", "try"); Gramext.Sself; Gramext.Stoken ("", "with");
       Gramext.Stoken ("", "[");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (match_case : 'match_case Grammar.Entry.e)),
                 Gramext.Stoken ("", "|"), false)],
             Gramext.action
               (fun (a : 'match_case list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__62));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__62));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__62))]);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (l : 'e__62) _ _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExTry", [Qast.Loc; e; l]) : 'expr));
      [Gramext.Stoken ("", "match"); Gramext.Sself;
       Gramext.Stoken ("", "with");
       Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Stoken ("", "->"); Gramext.Sself],
      Gramext.action
        (fun (e1 : 'expr) _ (p1 : 'ipatt) _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node
              ("ExMat",
               [Qast.Loc; e;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple [p1; Qast.VaVal (Qast.Option None); e1]])]) :
            'expr));
      [Gramext.Stoken ("", "match"); Gramext.Sself;
       Gramext.Stoken ("", "with"); Gramext.Stoken ("", "|");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (match_case : 'match_case Grammar.Entry.e)),
                 Gramext.Stoken ("", "|"), false)],
             Gramext.action
               (fun (a : 'match_case list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__61));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__61));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__61))]);
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (l : 'e__61) _ _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExMat", [Qast.Loc; e; l]) : 'expr));
      [Gramext.Stoken ("", "match"); Gramext.Sself;
       Gramext.Stoken ("", "with"); Gramext.Stoken ("", "[");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (match_case : 'match_case Grammar.Entry.e)),
                 Gramext.Stoken ("", "|"), false)],
             Gramext.action
               (fun (a : 'match_case list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__60));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__60));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__60))]);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (l : 'e__60) _ _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExMat", [Qast.Loc; e; l]) : 'expr));
      [Gramext.Stoken ("", "fun");
       Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Snterm
         (Grammar.Entry.obj (fun_def : 'fun_def Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'fun_def) (p : 'ipatt) _ (loc : Ploc.t) ->
           (Qast.Node
              ("ExFun",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple [p; Qast.VaVal (Qast.Option None); e]])]) :
            'expr));
      [Gramext.Stoken ("", "fun"); Gramext.Stoken ("", "[");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (match_case : 'match_case Grammar.Entry.e)),
                 Gramext.Stoken ("", "|"), false)],
             Gramext.action
               (fun (a : 'match_case list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__59));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__59));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__59))]);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (l : 'e__59) _ _ (loc : Ploc.t) ->
           (Qast.Node ("ExFun", [Qast.Loc; l]) : 'expr));
      [Gramext.Stoken ("", "let"); Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__58));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__58));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__58));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__58));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__58))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e));
       Gramext.Stoken ("", "in"); Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) _ (mb : 'mod_fun_binding) (m : 'e__58) _ _
             (loc : Ploc.t) ->
           (Qast.Node ("ExLmd", [Qast.Loc; m; mb; e]) : 'expr));
      [Gramext.Stoken ("", "let");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "rec"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__56));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__56));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__56));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__56));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__56))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (let_binding : 'let_binding Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'let_binding list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__57));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__57));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__57))]);
       Gramext.Stoken ("", "in"); Gramext.Sself],
      Gramext.action
        (fun (x : 'expr) _ (l : 'e__57) (r : 'e__56) _ (loc : Ploc.t) ->
           (Qast.Node ("ExLet", [Qast.Loc; r; l; x]) : 'expr))];
     Some "where", None,
     [[Gramext.Sself; Gramext.Stoken ("", "where");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "rec"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__68));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__68));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__68));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__68));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__68))]);
       Gramext.Snterm
         (Grammar.Entry.obj (let_binding : 'let_binding Grammar.Entry.e))],
      Gramext.action
        (fun (lb : 'let_binding) (rf : 'e__68) _ (e : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExLet", [Qast.Loc; rf; Qast.VaVal (Qast.List [lb]); e]) :
            'expr))];
     Some ":=", Some Gramext.NonA,
     [[Gramext.Sself; Gramext.Stoken ("", ":="); Gramext.Sself;
       Gramext.Snterm (Grammar.Entry.obj (dummy : 'dummy Grammar.Entry.e))],
      Gramext.action
        (fun _ (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("ExAss", [Qast.Loc; e1; e2]) : 'expr))];
     Some "||", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", "||"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "||")]);
                    e1]);
                e2]) :
            'expr))];
     Some "&&", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", "&&"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "&&")]);
                    e1]);
                e2]) :
            'expr))];
     Some "<", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "!="); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "!=")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "=="); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "==")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "<>"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "<>")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "="); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "=")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", ">="); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str ">=")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "<="); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "<=")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", ">"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str ">")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "<"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "<")]);
                    e1]);
                e2]) :
            'expr))];
     Some "^", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", "@"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "@")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "^"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "^")]);
                    e1]);
                e2]) :
            'expr))];
     Some "+", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "-."); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-.")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "+."); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "+.")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "-"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "+"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "+")]);
                    e1]);
                e2]) :
            'expr))];
     Some "*", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "mod"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "mod")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "lxor"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "lxor")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "lor"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "lor")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "land"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "land")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "/."); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "/.")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "*."); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "*.")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "/"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "/")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "*"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "*")]);
                    e1]);
                e2]) :
            'expr))];
     Some "**", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", "lsr"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "lsr")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "lsl"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "lsl")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "asr"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "asr")]);
                    e1]);
                e2]) :
            'expr));
      [Gramext.Sself; Gramext.Stoken ("", "**"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExApp",
                   [Qast.Loc;
                    Qast.Node
                      ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "**")]);
                    e1]);
                e2]) :
            'expr))];
     Some "unary minus", Some Gramext.NonA,
     [[Gramext.Stoken ("", "-."); Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-.")]);
                e]) :
            'expr));
      [Gramext.Stoken ("", "-"); Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-")]);
                e]) :
            'expr))];
     Some "apply", Some Gramext.LeftA,
     [[Gramext.Stoken ("", "lazy"); Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExLaz", [Qast.Loc; e]) : 'expr));
      [Gramext.Stoken ("", "assert"); Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExAsr", [Qast.Loc; e]) : 'expr));
      [Gramext.Sself; Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("ExApp", [Qast.Loc; e1; e2]) : 'expr))];
     Some ".", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("ExAcc", [Qast.Loc; e1; e2]) : 'expr));
      [Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (a : 'expr list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__69));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__69));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__69))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (el : 'e__69) _ _ (e : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("ExBae", [Qast.Loc; e; el]) : 'expr));
      [Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Stoken ("", "[");
       Gramext.Sself; Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("ExSte", [Qast.Loc; e1; e2]) : 'expr));
      [Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Stoken ("", "(");
       Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("ExAre", [Qast.Loc; e1; e2]) : 'expr))];
     Some "~-", Some Gramext.NonA,
     [[Gramext.Stoken ("", "~-."); Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "~-.")]);
                e]) :
            'expr));
      [Gramext.Stoken ("", "~-"); Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "~-")]);
                e]) :
            'expr))];
     Some "simple", None,
     [[Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (a : 'expr list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__83));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__83));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__83))]);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (el : 'e__83) _ (loc : Ploc.t) ->
           (Qast.Node ("ExTup", [Qast.Loc; el]) : 'expr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action (fun _ (e : 'expr) _ (loc : Ploc.t) -> (e : 'expr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ",");
       Gramext.Slist1sep
         (Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (el : 'expr list) _ (e : 'expr) _ (loc : Ploc.t) ->
           (mktupexp Qast.Loc e el : 'expr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'expr));
      [Gramext.Stoken ("", "("); Gramext.Stoken ("", "module");
       Gramext.Snterm
         (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (me : 'module_expr) _ _ (loc : Ploc.t) ->
           (Qast.Node ("ExPck", [Qast.Loc; me; Qast.Option None]) : 'expr));
      [Gramext.Stoken ("", "("); Gramext.Stoken ("", "module");
       Gramext.Snterm
         (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (mt : 'module_type) _ (me : 'module_expr) _ _ (loc : Ploc.t) ->
           (Qast.Node ("ExPck", [Qast.Loc; me; Qast.Option (Some mt)]) :
            'expr));
      [Gramext.Stoken ("", "("); Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           (Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
            'expr));
      [Gramext.Stoken ("", "{"); Gramext.Stoken ("", "("); Gramext.Sself;
       Gramext.Stoken ("", ")"); Gramext.Stoken ("", "with");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (label_expr : 'label_expr Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'label_expr list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__82));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__82));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__82))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (lel : 'e__82) _ _ (e : 'expr) _ _ (loc : Ploc.t) ->
           (Qast.Node ("ExRec", [Qast.Loc; lel; Qast.Option (Some e)]) :
            'expr));
      [Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (label_expr : 'label_expr Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'label_expr list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__81));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__81));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__81))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (lel : 'e__81) _ (loc : Ploc.t) ->
           (Qast.Node ("ExRec", [Qast.Loc; lel; Qast.Option None]) : 'expr));
      [Gramext.Stoken ("", "[|");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'expr list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__80));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__80));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__80))]);
       Gramext.Stoken ("", "|]")],
      Gramext.action
        (fun _ (el : 'e__80) _ (loc : Ploc.t) ->
           (Qast.Node ("ExArr", [Qast.Loc; el]) : 'expr));
      [Gramext.Stoken ("", "[");
       Gramext.Slist1sep
         (Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e)),
          Gramext.Stoken ("", ";"), false);
       Gramext.Snterm
         (Grammar.Entry.obj (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (last : 'cons_expr_opt) (el : 'expr list) _ (loc : Ploc.t) ->
           (mklistexp Qast.Loc last el : 'expr));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           (Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")]) :
            'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__79));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__79));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__79));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__79));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__79))])],
      Gramext.action
        (fun (i : 'e__79) (loc : Ploc.t) ->
           (Qast.Node ("ExUid", [Qast.Loc; i]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("GIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__78))])],
      Gramext.action
        (fun (i : 'e__78) (loc : Ploc.t) ->
           (Qast.Node ("ExLid", [Qast.Loc; i]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__77));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__77));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__77));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__77));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__77))])],
      Gramext.action
        (fun (i : 'e__77) (loc : Ploc.t) ->
           (Qast.Node ("ExLid", [Qast.Loc; i]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("CHAR", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__76));
             [Gramext.Stoken ("ANTIQUOT", "_chr")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_chr", loc, a) : 'e__76));
             [Gramext.Stoken ("ANTIQUOT", "chr")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("chr", loc, a)) : 'e__76))])],
      Gramext.action
        (fun (s : 'e__76) (loc : Ploc.t) ->
           (Qast.Node ("ExChr", [Qast.Loc; s]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("STRING", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__75));
             [Gramext.Stoken ("ANTIQUOT", "_str")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_str", loc, a) : 'e__75));
             [Gramext.Stoken ("ANTIQUOT", "str")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("str", loc, a)) : 'e__75))])],
      Gramext.action
        (fun (s : 'e__75) (loc : Ploc.t) ->
           (Qast.Node ("ExStr", [Qast.Loc; s]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("FLOAT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__74));
             [Gramext.Stoken ("ANTIQUOT", "_flo")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flo", loc, a) : 'e__74));
             [Gramext.Stoken ("ANTIQUOT", "flo")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flo", loc, a)) : 'e__74))])],
      Gramext.action
        (fun (s : 'e__74) (loc : Ploc.t) ->
           (Qast.Node ("ExFlo", [Qast.Loc; s]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("INT_n", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__73));
             [Gramext.Stoken ("ANTIQUOT", "_nativeint")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_nativeint", loc, a) : 'e__73));
             [Gramext.Stoken ("ANTIQUOT", "nativeint")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("nativeint", loc, a)) :
                   'e__73))])],
      Gramext.action
        (fun (s : 'e__73) (loc : Ploc.t) ->
           (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "n"]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("INT_L", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__72));
             [Gramext.Stoken ("ANTIQUOT", "_int64")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_int64", loc, a) : 'e__72));
             [Gramext.Stoken ("ANTIQUOT", "int64")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("int64", loc, a)) : 'e__72))])],
      Gramext.action
        (fun (s : 'e__72) (loc : Ploc.t) ->
           (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "L"]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("INT_l", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__71));
             [Gramext.Stoken ("ANTIQUOT", "_int32")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_int32", loc, a) : 'e__71));
             [Gramext.Stoken ("ANTIQUOT", "int32")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("int32", loc, a)) : 'e__71))])],
      Gramext.action
        (fun (s : 'e__71) (loc : Ploc.t) ->
           (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "l"]) : 'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("INT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__70));
             [Gramext.Stoken ("ANTIQUOT", "_int")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_int", loc, a) : 'e__70));
             [Gramext.Stoken ("ANTIQUOT", "int")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("int", loc, a)) : 'e__70))])],
      Gramext.action
        (fun (s : 'e__70) (loc : Ploc.t) ->
           (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str ""]) : 'expr))]];
    Grammar.Entry.obj (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e), None,
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> (Qast.Option None : 'cons_expr_opt));
      [Gramext.Stoken ("", "::");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Option (Some e) : 'cons_expr_opt))]];
    Grammar.Entry.obj (dummy : 'dummy Grammar.Entry.e), None,
    [None, None, [[], Gramext.action (fun (loc : Ploc.t) -> (() : 'dummy))]];
    Grammar.Entry.obj (sequence : 'sequence Grammar.Entry.e), None,
    [None, Some Gramext.RightA,
     [[Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) (loc : Ploc.t) -> (Qast.List [e] : 'sequence));
      [Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
       Gramext.Stoken ("", ";")],
      Gramext.action
        (fun _ (e : 'expr) (loc : Ploc.t) -> (Qast.List [e] : 'sequence));
      [Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
       Gramext.Stoken ("", ";"); Gramext.Sself],
      Gramext.action
        (fun (el : 'sequence) _ (e : 'expr) (loc : Ploc.t) ->
           (Qast.Cons (e, el) : 'sequence));
      [Gramext.Stoken ("", "let"); Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__86));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__86));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__86));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__86));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__86))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e));
       Gramext.Stoken ("", "in"); Gramext.Sself],
      Gramext.action
        (fun (el : 'sequence) _ (mb : 'mod_fun_binding) (m : 'e__86) _ _
             (loc : Ploc.t) ->
           (Qast.List
              [Qast.Node
                 ("ExLmd", [Qast.Loc; m; mb; mksequence Qast.Loc el])] :
            'sequence));
      [Gramext.Stoken ("", "let");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "rec"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__84));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__84));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__84));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__84));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__84))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (let_binding : 'let_binding Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'let_binding list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__85));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__85));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__85))]);
       Gramext.Stoken ("", "in"); Gramext.Sself],
      Gramext.action
        (fun (el : 'sequence) _ (l : 'e__85) (rf : 'e__84) _ (loc : Ploc.t) ->
           (Qast.List
              [Qast.Node
                 ("ExLet", [Qast.Loc; rf; l; mksequence Qast.Loc el])] :
            'sequence))]];
    Grammar.Entry.obj (let_binding : 'let_binding Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Snterm
         (Grammar.Entry.obj (fun_binding : 'fun_binding Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
           (Qast.Tuple [p; e] : 'let_binding))]];
    Grammar.Entry.obj (fun_binding : 'fun_binding Grammar.Entry.e), None,
    [None, Some Gramext.RightA,
     [[Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
           (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'fun_binding));
      [Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_binding));
      [Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (e : 'fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
           (Qast.Node
              ("ExFun",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple [p; Qast.VaVal (Qast.Option None); e]])]) :
            'fun_binding))]];
    Grammar.Entry.obj (match_case : 'match_case Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
       Gramext.Snterm
         (Grammar.Entry.obj (as_patt_opt : 'as_patt_opt Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (when_expr : 'when_expr Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'when_expr option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__87));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__87));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__87))]);
       Gramext.Stoken ("", "->");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (w : 'e__87) (aso : 'as_patt_opt) (p : 'patt)
             (loc : Ploc.t) ->
           (mkmatchcase Qast.Loc p aso w e : 'match_case))]];
    Grammar.Entry.obj (as_patt_opt : 'as_patt_opt Grammar.Entry.e), None,
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> (Qast.Option None : 'as_patt_opt));
      [Gramext.Stoken ("", "as");
       Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e))],
      Gramext.action
        (fun (p : 'patt) _ (loc : Ploc.t) ->
           (Qast.Option (Some p) : 'as_patt_opt))]];
    Grammar.Entry.obj (when_expr : 'when_expr Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "when");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'when_expr))]];
    Grammar.Entry.obj (label_expr : 'label_expr Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj
            (patt_label_ident : 'patt_label_ident Grammar.Entry.e));
       Gramext.Snterm
         (Grammar.Entry.obj (fun_binding : 'fun_binding Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'fun_binding) (i : 'patt_label_ident) (loc : Ploc.t) ->
           (Qast.Tuple [i; e] : 'label_expr))]];
    Grammar.Entry.obj (fun_def : 'fun_def Grammar.Entry.e), None,
    [None, Some Gramext.RightA,
     [[Gramext.Stoken ("", "->");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_def));
      [Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (e : 'fun_def) (p : 'ipatt) (loc : Ploc.t) ->
           (Qast.Node
              ("ExFun",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple [p; Qast.VaVal (Qast.Option None); e]])]) :
            'fun_def))]];
    Grammar.Entry.obj (patt : 'patt Grammar.Entry.e), None,
    [None, Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "|"); Gramext.Sself],
      Gramext.action
        (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
           (Qast.Node ("PaOrp", [Qast.Loc; p1; p2]) : 'patt))];
     None, Some Gramext.NonA,
     [[Gramext.Sself; Gramext.Stoken ("", ".."); Gramext.Sself],
      Gramext.action
        (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
           (Qast.Node ("PaRng", [Qast.Loc; p1; p2]) : 'patt))];
     None, Some Gramext.LeftA,
     [[Gramext.Stoken ("", "lazy"); Gramext.Sself],
      Gramext.action
        (fun (p : 'patt) _ (loc : Ploc.t) ->
           (Qast.Node ("PaLaz", [Qast.Loc; p]) : 'patt));
      [Gramext.Sself; Gramext.Sself],
      Gramext.action
        (fun (p2 : 'patt) (p1 : 'patt) (loc : Ploc.t) ->
           (Qast.Node ("PaApp", [Qast.Loc; p1; p2]) : 'patt))];
     None, Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
           (Qast.Node ("PaAcc", [Qast.Loc; p1; p2]) : 'patt))];
     Some "simple", None,
     [[Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Qast.Node ("PaAny", [Qast.Loc]) : 'patt));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Grammar.Entry.obj (paren_patt : 'paren_patt Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (p : 'paren_patt) _ (loc : Ploc.t) -> (p : 'patt));
      [Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (label_patt : 'label_patt Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'label_patt list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__99));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__99));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__99))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (lpl : 'e__99) _ (loc : Ploc.t) ->
           (Qast.Node ("PaRec", [Qast.Loc; lpl]) : 'patt));
      [Gramext.Stoken ("", "[|");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'patt list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__98));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__98));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__98))]);
       Gramext.Stoken ("", "|]")],
      Gramext.action
        (fun _ (pl : 'e__98) _ (loc : Ploc.t) ->
           (Qast.Node ("PaArr", [Qast.Loc; pl]) : 'patt));
      [Gramext.Stoken ("", "[");
       Gramext.Slist1sep
         (Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e)),
          Gramext.Stoken ("", ";"), false);
       Gramext.Snterm
         (Grammar.Entry.obj (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (last : 'cons_patt_opt) (pl : 'patt list) _ (loc : Ploc.t) ->
           (mklistpat Qast.Loc last pl : 'patt));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")]) :
            'patt));
      [Gramext.Stoken ("", "-"); Gramext.Stoken ("FLOAT", "")],
      Gramext.action
        (fun (s : string) _ (loc : Ploc.t) ->
           (Qast.Node ("PaFlo", [Qast.Loc; Qast.VaVal (neg_string s)]) :
            'patt));
      [Gramext.Stoken ("", "-"); Gramext.Stoken ("INT_n", "")],
      Gramext.action
        (fun (s : string) _ (loc : Ploc.t) ->
           (Qast.Node
              ("PaInt", [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "n"]) :
            'patt));
      [Gramext.Stoken ("", "-"); Gramext.Stoken ("INT_L", "")],
      Gramext.action
        (fun (s : string) _ (loc : Ploc.t) ->
           (Qast.Node
              ("PaInt", [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "L"]) :
            'patt));
      [Gramext.Stoken ("", "-"); Gramext.Stoken ("INT_l", "")],
      Gramext.action
        (fun (s : string) _ (loc : Ploc.t) ->
           (Qast.Node
              ("PaInt", [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "l"]) :
            'patt));
      [Gramext.Stoken ("", "-"); Gramext.Stoken ("INT", "")],
      Gramext.action
        (fun (s : string) _ (loc : Ploc.t) ->
           (Qast.Node
              ("PaInt", [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str ""]) :
            'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("CHAR", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__97));
             [Gramext.Stoken ("ANTIQUOT", "_chr")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_chr", loc, a) : 'e__97));
             [Gramext.Stoken ("ANTIQUOT", "chr")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("chr", loc, a)) : 'e__97))])],
      Gramext.action
        (fun (s : 'e__97) (loc : Ploc.t) ->
           (Qast.Node ("PaChr", [Qast.Loc; s]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("STRING", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__96));
             [Gramext.Stoken ("ANTIQUOT", "_str")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_str", loc, a) : 'e__96));
             [Gramext.Stoken ("ANTIQUOT", "str")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("str", loc, a)) : 'e__96))])],
      Gramext.action
        (fun (s : 'e__96) (loc : Ploc.t) ->
           (Qast.Node ("PaStr", [Qast.Loc; s]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("FLOAT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__95));
             [Gramext.Stoken ("ANTIQUOT", "_flo")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flo", loc, a) : 'e__95));
             [Gramext.Stoken ("ANTIQUOT", "flo")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flo", loc, a)) : 'e__95))])],
      Gramext.action
        (fun (s : 'e__95) (loc : Ploc.t) ->
           (Qast.Node ("PaFlo", [Qast.Loc; s]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("INT_n", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__94));
             [Gramext.Stoken ("ANTIQUOT", "_nativeint")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_nativeint", loc, a) : 'e__94));
             [Gramext.Stoken ("ANTIQUOT", "nativeint")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("nativeint", loc, a)) :
                   'e__94))])],
      Gramext.action
        (fun (s : 'e__94) (loc : Ploc.t) ->
           (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "n"]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("INT_L", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__93));
             [Gramext.Stoken ("ANTIQUOT", "_int64")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_int64", loc, a) : 'e__93));
             [Gramext.Stoken ("ANTIQUOT", "int64")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("int64", loc, a)) : 'e__93))])],
      Gramext.action
        (fun (s : 'e__93) (loc : Ploc.t) ->
           (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "L"]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("INT_l", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__92));
             [Gramext.Stoken ("ANTIQUOT", "_int32")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_int32", loc, a) : 'e__92));
             [Gramext.Stoken ("ANTIQUOT", "int32")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("int32", loc, a)) : 'e__92))])],
      Gramext.action
        (fun (s : 'e__92) (loc : Ploc.t) ->
           (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "l"]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("INT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__91));
             [Gramext.Stoken ("ANTIQUOT", "_int")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_int", loc, a) : 'e__91));
             [Gramext.Stoken ("ANTIQUOT", "int")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("int", loc, a)) : 'e__91))])],
      Gramext.action
        (fun (s : 'e__91) (loc : Ploc.t) ->
           (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str ""]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__90));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__90));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__90));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__90));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__90))])],
      Gramext.action
        (fun (s : 'e__90) (loc : Ploc.t) ->
           (Qast.Node ("PaUid", [Qast.Loc; s]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("GIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__89))])],
      Gramext.action
        (fun (s : 'e__89) (loc : Ploc.t) ->
           (Qast.Node ("PaLid", [Qast.Loc; s]) : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__88));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__88));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__88));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__88));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__88))])],
      Gramext.action
        (fun (s : 'e__88) (loc : Ploc.t) ->
           (Qast.Node ("PaLid", [Qast.Loc; s]) : 'patt))]];
    Grammar.Entry.obj (paren_patt : 'paren_patt Grammar.Entry.e), None,
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) ->
           (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
            'paren_patt));
      [Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__103));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__103));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__103));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__103));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__103))])],
      Gramext.action
        (fun (s : 'e__103) _ (loc : Ploc.t) ->
           (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option None]) :
            'paren_patt));
      [Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__102));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__102));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__102));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__102));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__102))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'module_type) _ (s : 'e__102) _ (loc : Ploc.t) ->
           (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option (Some mt)]) :
            'paren_patt));
      [Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__101));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__101));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__101));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__101));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__101))])],
      Gramext.action
        (fun (s : 'e__101) _ (loc : Ploc.t) ->
           (Qast.Node ("PaNty", [Qast.Loc; s]) : 'paren_patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (a : 'patt list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__100));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__100));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__100))])],
      Gramext.action
        (fun (pl : 'e__100) (loc : Ploc.t) ->
           (Qast.Node ("PaTup", [Qast.Loc; pl]) : 'paren_patt));
      [Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e))],
      Gramext.action (fun (p : 'patt) (loc : Ploc.t) -> (p : 'paren_patt));
      [Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
       Gramext.Stoken ("", ",");
       Gramext.Slist1sep
         (Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e)),
          Gramext.Stoken ("", ","), false)],
      Gramext.action
        (fun (pl : 'patt list) _ (p : 'patt) (loc : Ploc.t) ->
           (mktuppat Qast.Loc p pl : 'paren_patt));
      [Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
       Gramext.Stoken ("", "as");
       Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e))],
      Gramext.action
        (fun (p2 : 'patt) _ (p : 'patt) (loc : Ploc.t) ->
           (Qast.Node ("PaAli", [Qast.Loc; p; p2]) : 'paren_patt));
      [Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
           (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'paren_patt))]];
    Grammar.Entry.obj (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e), None,
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> (Qast.Option None : 'cons_patt_opt));
      [Gramext.Stoken ("", "::");
       Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e))],
      Gramext.action
        (fun (p : 'patt) _ (loc : Ploc.t) ->
           (Qast.Option (Some p) : 'cons_patt_opt))]];
    Grammar.Entry.obj (label_patt : 'label_patt Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj
            (patt_label_ident : 'patt_label_ident Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e))],
      Gramext.action
        (fun (p : 'patt) _ (i : 'patt_label_ident) (loc : Ploc.t) ->
           (Qast.Tuple [i; p] : 'label_patt))]];
    Grammar.Entry.obj (patt_label_ident : 'patt_label_ident Grammar.Entry.e),
    None,
    [None, Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (p2 : 'patt_label_ident) _ (p1 : 'patt_label_ident)
             (loc : Ploc.t) ->
           (Qast.Node ("PaAcc", [Qast.Loc; p1; p2]) : 'patt_label_ident))];
     Some "simple", Some Gramext.RightA,
     [[Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (Qast.Node ("PaAny", [Qast.Loc]) : 'patt_label_ident));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__105));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__105));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__105));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__105));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__105))])],
      Gramext.action
        (fun (i : 'e__105) (loc : Ploc.t) ->
           (Qast.Node ("PaLid", [Qast.Loc; i]) : 'patt_label_ident));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__104));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__104));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__104));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__104));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__104))])],
      Gramext.action
        (fun (i : 'e__104) (loc : Ploc.t) ->
           (Qast.Node ("PaUid", [Qast.Loc; i]) : 'patt_label_ident))]];
    Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Qast.Node ("PaAny", [Qast.Loc]) : 'ipatt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("GIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__108))])],
      Gramext.action
        (fun (s : 'e__108) (loc : Ploc.t) ->
           (Qast.Node ("PaLid", [Qast.Loc; s]) : 'ipatt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__107));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__107));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__107));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__107));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__107))])],
      Gramext.action
        (fun (s : 'e__107) (loc : Ploc.t) ->
           (Qast.Node ("PaLid", [Qast.Loc; s]) : 'ipatt));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Grammar.Entry.obj (paren_ipatt : 'paren_ipatt Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (p : 'paren_ipatt) _ (loc : Ploc.t) -> (p : 'ipatt));
      [Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (label_ipatt : 'label_ipatt Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'label_ipatt list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__106));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__106));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__106))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (lpl : 'e__106) _ (loc : Ploc.t) ->
           (Qast.Node ("PaRec", [Qast.Loc; lpl]) : 'ipatt))]];
    Grammar.Entry.obj (paren_ipatt : 'paren_ipatt Grammar.Entry.e), None,
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) ->
           (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
            'paren_ipatt));
      [Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__112));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__112));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__112));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__112));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__112))])],
      Gramext.action
        (fun (s : 'e__112) _ (loc : Ploc.t) ->
           (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option None]) :
            'paren_ipatt));
      [Gramext.Stoken ("", "module");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__111));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__111));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__111));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__111));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__111))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'module_type) _ (s : 'e__111) _ (loc : Ploc.t) ->
           (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option (Some mt)]) :
            'paren_ipatt));
      [Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__110));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__110));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__110));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__110));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__110))])],
      Gramext.action
        (fun (s : 'e__110) _ (loc : Ploc.t) ->
           (Qast.Node ("PaNty", [Qast.Loc; s]) : 'paren_ipatt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (a : 'ipatt list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__109));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__109));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__109))])],
      Gramext.action
        (fun (pl : 'e__109) (loc : Ploc.t) ->
           (Qast.Node ("PaTup", [Qast.Loc; pl]) : 'paren_ipatt));
      [Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e))],
      Gramext.action (fun (p : 'ipatt) (loc : Ploc.t) -> (p : 'paren_ipatt));
      [Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Stoken ("", ",");
       Gramext.Slist1sep
         (Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e)),
          Gramext.Stoken ("", ","), false)],
      Gramext.action
        (fun (pl : 'ipatt list) _ (p : 'ipatt) (loc : Ploc.t) ->
           (mktuppat Qast.Loc p pl : 'paren_ipatt));
      [Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Stoken ("", "as");
       Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e))],
      Gramext.action
        (fun (p2 : 'ipatt) _ (p : 'ipatt) (loc : Ploc.t) ->
           (Qast.Node ("PaAli", [Qast.Loc; p; p2]) : 'paren_ipatt));
      [Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
           (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'paren_ipatt))]];
    Grammar.Entry.obj (label_ipatt : 'label_ipatt Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj
            (patt_label_ident : 'patt_label_ident Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e))],
      Gramext.action
        (fun (p : 'ipatt) _ (i : 'patt_label_ident) (loc : Ploc.t) ->
           (Qast.Tuple [i; p] : 'label_ipatt))]];
    Grammar.Entry.obj (type_decl : 'type_decl Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (type_patt : 'type_patt Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'type_patt) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__113));
             [Gramext.Stoken ("ANTIQUOT", "_tp")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_tp", loc, a) : 'e__113));
             [Gramext.Stoken ("ANTIQUOT", "tp")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("tp", loc, a)) : 'e__113))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (type_parameter : 'type_parameter Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__114));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__114));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__114))]);
       Gramext.Stoken ("", "=");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "private"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__115));
             [Gramext.Stoken ("ANTIQUOT", "_priv")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_priv", loc, a) : 'e__115));
             [Gramext.Stoken ("ANTIQUOT", "priv")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) : 'e__115))]);
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (constrain : 'constrain Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'constrain list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__116));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__116));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__116))])],
      Gramext.action
        (fun (cl : 'e__116) (tk : 'ctyp) (pf : 'e__115) _ (tpl : 'e__114)
             (n : 'e__113) (loc : Ploc.t) ->
           (Qast.Record
              ["tdNam", n; "tdPrm", tpl; "tdPrv", pf; "tdDef", tk;
               "tdCon", cl] :
            'type_decl))]];
    Grammar.Entry.obj (type_patt : 'type_patt Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__117));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__117));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__117));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__117));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__117))])],
      Gramext.action
        (fun (n : 'e__117) (loc : Ploc.t) ->
           (Qast.Tuple [Qast.Loc; n] : 'type_patt))]];
    Grammar.Entry.obj (constrain : 'constrain Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "constraint");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
           (Qast.Tuple [t1; t2] : 'constrain))]];
    Grammar.Entry.obj (type_parameter : 'type_parameter Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj
                   (simple_type_parameter :
                    'simple_type_parameter Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__120))])],
      Gramext.action
        (fun (p : 'e__120) (loc : Ploc.t) ->
           (Qast.Tuple [p; Qast.Option None] : 'type_parameter));
      [Gramext.Stoken ("", "-");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj
                   (simple_type_parameter :
                    'simple_type_parameter Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__119))])],
      Gramext.action
        (fun (p : 'e__119) _ (loc : Ploc.t) ->
           (Qast.Tuple [p; Qast.Option (Some (Qast.Bool false))] :
            'type_parameter));
      [Gramext.Stoken ("", "+");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj
                   (simple_type_parameter :
                    'simple_type_parameter Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__118))])],
      Gramext.action
        (fun (p : 'e__118) _ (loc : Ploc.t) ->
           (Qast.Tuple [p; Qast.Option (Some (Qast.Bool true))] :
            'type_parameter))]];
    Grammar.Entry.obj
      (simple_type_parameter : 'simple_type_parameter Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Qast.Option None : 'simple_type_parameter));
      [Gramext.Stoken ("GIDENT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) ->
           (Qast.Option (Some (greek_ascii_equiv i)) :
            'simple_type_parameter));
      [Gramext.Stoken ("", "'");
       Gramext.Snterm (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
      Gramext.action
        (fun (i : 'ident) _ (loc : Ploc.t) ->
           (Qast.Option (Some i) : 'simple_type_parameter))]];
    Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e), None,
    [Some "top", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "==");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "private"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__121));
             [Gramext.Stoken ("ANTIQUOT", "_priv")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_priv", loc, a) : 'e__121));
             [Gramext.Stoken ("ANTIQUOT", "priv")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) : 'e__121))]);
       Gramext.Sself],
      Gramext.action
        (fun (t2 : 'ctyp) (pf : 'e__121) _ (t1 : 'ctyp) (loc : Ploc.t) ->
           (Qast.Node ("TyMan", [Qast.Loc; t1; pf; t2]) : 'ctyp))];
     Some "as", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "as"); Gramext.Sself],
      Gramext.action
        (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
           (Qast.Node ("TyAli", [Qast.Loc; t1; t2]) : 'ctyp))];
     None, Some Gramext.LeftA,
     [[Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1 (Gramext.Stoken ("LIDENT", ""))],
             Gramext.action
               (fun (a : string list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List (List.map (fun a -> Qast.Str a) a)) :
                   'e__123));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__123));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__123))]);
       Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (t : 'ctyp) _ (pl : 'e__123) _ (loc : Ploc.t) ->
           (Qast.Node ("TyPot", [Qast.Loc; pl; t]) : 'ctyp));
      [Gramext.Stoken ("", "!");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1
                (Gramext.Snterm
                   (Grammar.Entry.obj (typevar : 'typevar Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'typevar list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__122));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__122));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__122))]);
       Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (t : 'ctyp) _ (pl : 'e__122) _ (loc : Ploc.t) ->
           (Qast.Node ("TyPol", [Qast.Loc; pl; t]) : 'ctyp))];
     Some "arrow", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", "->"); Gramext.Sself],
      Gramext.action
        (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
           (Qast.Node ("TyArr", [Qast.Loc; t1; t2]) : 'ctyp))];
     Some "apply", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Sself],
      Gramext.action
        (fun (t2 : 'ctyp) (t1 : 'ctyp) (loc : Ploc.t) ->
           (Qast.Node ("TyApp", [Qast.Loc; t1; t2]) : 'ctyp))];
     None, Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
           (Qast.Node ("TyAcc", [Qast.Loc; t1; t2]) : 'ctyp))];
     Some "simple", None,
     [[Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (label_declaration :
                       'label_declaration Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'label_declaration list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__129));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__129));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__129))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (ldl : 'e__129) _ (loc : Ploc.t) ->
           (Qast.Node ("TyRec", [Qast.Loc; ldl]) : 'ctyp));
      [Gramext.Stoken ("", "[");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (constructor_declaration :
                       'constructor_declaration Grammar.Entry.e)),
                 Gramext.Stoken ("", "|"), false)],
             Gramext.action
               (fun (a : 'constructor_declaration list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__128));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__128));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__128))]);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (cdl : 'e__128) _ (loc : Ploc.t) ->
           (Qast.Node ("TySum", [Qast.Loc; cdl]) : 'ctyp));
      [Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e)),
                 Gramext.Stoken ("", "*"), false)],
             Gramext.action
               (fun (a : 'ctyp list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__127));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__127));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__127))]);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (tl : 'e__127) _ (loc : Ploc.t) ->
           (Qast.Node ("TyTup", [Qast.Loc; tl]) : 'ctyp));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'ctyp));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", "*");
       Gramext.Slist1sep
         (Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e)),
          Gramext.Stoken ("", "*"), false);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (tl : 'ctyp list) _ (t : 'ctyp) _ (loc : Ploc.t) ->
           (mktuptyp Qast.Loc t tl : 'ctyp));
      [Gramext.Stoken ("", "module");
       Gramext.Snterm
         (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e))],
      Gramext.action
        (fun (mt : 'module_type) _ (loc : Ploc.t) ->
           (Qast.Node ("TyPck", [Qast.Loc; mt]) : 'ctyp));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__126));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__126));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__126));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__126));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__126))])],
      Gramext.action
        (fun (i : 'e__126) (loc : Ploc.t) ->
           (Qast.Node ("TyUid", [Qast.Loc; i]) : 'ctyp));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__125));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__125));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__125));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__125));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__125))])],
      Gramext.action
        (fun (i : 'e__125) (loc : Ploc.t) ->
           (Qast.Node ("TyLid", [Qast.Loc; i]) : 'ctyp));
      [Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Qast.Node ("TyAny", [Qast.Loc]) : 'ctyp));
      [Gramext.Stoken ("GIDENT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) ->
           (Qast.Node
              ("TyQuo", [Qast.Loc; Qast.VaVal (greek_ascii_equiv i)]) :
            'ctyp));
      [Gramext.Stoken ("", "'");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'ident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__124));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__124));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__124))])],
      Gramext.action
        (fun (i : 'e__124) _ (loc : Ploc.t) ->
           (Qast.Node ("TyQuo", [Qast.Loc; i]) : 'ctyp))]];
    Grammar.Entry.obj
      (constructor_declaration : 'constructor_declaration Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__133));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__133));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__133));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__133));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__133))])],
      Gramext.action
        (fun (ci : 'e__133) (loc : Ploc.t) ->
           (Qast.Tuple
              [Qast.Loc; ci; Qast.VaVal (Qast.List []); Qast.Option None] :
            'constructor_declaration));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__132));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__132));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__132));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__132));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__132))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (ci : 'e__132) (loc : Ploc.t) ->
           (let (tl, rt) = generalized_type_of_type t in
            Qast.Tuple [Qast.Loc; ci; Qast.VaVal tl; Qast.Option (Some rt)] :
            'constructor_declaration));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__130));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__130));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__130));
             [Gramext.Stoken ("ANTIQUOT", "_uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_uid", loc, a) : 'e__130));
             [Gramext.Stoken ("ANTIQUOT", "uid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) : 'e__130))]);
       Gramext.Stoken ("", "of");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'ctyp list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__131));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__131));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__131))])],
      Gramext.action
        (fun (cal : 'e__131) _ (ci : 'e__130) (loc : Ploc.t) ->
           (Qast.Tuple [Qast.Loc; ci; cal; Qast.Option None] :
            'constructor_declaration))]];
    Grammar.Entry.obj
      (label_declaration : 'label_declaration Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("LIDENT", ""); Gramext.Stoken ("", ":");
       Gramext.Sflag (Gramext.Stoken ("", "mutable"));
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) (mf : bool) _ (i : string) (loc : Ploc.t) ->
           (mklabdecl Qast.Loc i mf t : 'label_declaration))]];
    Grammar.Entry.obj (ident : 'ident Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("UIDENT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident));
      [Gramext.Stoken ("LIDENT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident))]];
    Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e), None,
    [None, Some Gramext.RightA,
     [[Gramext.Stoken ("UIDENT", ""); Gramext.Stoken ("", ".");
       Gramext.Sself],
      Gramext.action
        (fun (j : 'mod_ident) _ (i : string) (loc : Ploc.t) ->
           (Qast.Cons (mkident i, j) : 'mod_ident));
      [Gramext.Stoken ("LIDENT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) ->
           (Qast.List [mkident i] : 'mod_ident));
      [Gramext.Stoken ("UIDENT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) ->
           (Qast.List [mkident i] : 'mod_ident))]];
    (* Objects and Classes *)
    Grammar.Entry.obj (str_item : 'str_item Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "class"); Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (class_type_declaration :
                       'class_type_declaration Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'class_type_declaration list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__135));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__135));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__135))])],
      Gramext.action
        (fun (ctd : 'e__135) _ _ (loc : Ploc.t) ->
           (Qast.Node ("StClt", [Qast.Loc; ctd]) : 'str_item));
      [Gramext.Stoken ("", "class");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (class_declaration :
                       'class_declaration Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'class_declaration list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__134));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__134));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__134))])],
      Gramext.action
        (fun (cd : 'e__134) _ (loc : Ploc.t) ->
           (Qast.Node ("StCls", [Qast.Loc; cd]) : 'str_item))]];
    Grammar.Entry.obj (sig_item : 'sig_item Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "class"); Gramext.Stoken ("", "type");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (class_type_declaration :
                       'class_type_declaration Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'class_type_declaration list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__137));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__137));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__137))])],
      Gramext.action
        (fun (ctd : 'e__137) _ _ (loc : Ploc.t) ->
           (Qast.Node ("SgClt", [Qast.Loc; ctd]) : 'sig_item));
      [Gramext.Stoken ("", "class");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (class_description :
                       'class_description Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'class_description list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__136));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__136));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__136))])],
      Gramext.action
        (fun (cd : 'e__136) _ (loc : Ploc.t) ->
           (Qast.Node ("SgCls", [Qast.Loc; cd]) : 'sig_item))]];
    Grammar.Entry.obj
      (class_declaration : 'class_declaration Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "virtual"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__138));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__138));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__138));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__138));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__138))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__139));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__139));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__139));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__139));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__139))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (class_type_parameters : 'class_type_parameters Grammar.Entry.e));
       Gramext.Snterm
         (Grammar.Entry.obj
            (class_fun_binding : 'class_fun_binding Grammar.Entry.e))],
      Gramext.action
        (fun (cfb : 'class_fun_binding) (ctp : 'class_type_parameters)
             (i : 'e__139) (vf : 'e__138) (loc : Ploc.t) ->
           (Qast.Record
              ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", i;
               "ciExp", cfb] :
            'class_declaration))]];
    Grammar.Entry.obj
      (class_fun_binding : 'class_fun_binding Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (cfb : 'class_fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
           (Qast.Node ("CeFun", [Qast.Loc; p; cfb]) : 'class_fun_binding));
      [Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (class_type : 'class_type Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj (class_expr : 'class_expr Grammar.Entry.e))],
      Gramext.action
        (fun (ce : 'class_expr) _ (ct : 'class_type) _ (loc : Ploc.t) ->
           (Qast.Node ("CeTyc", [Qast.Loc; ce; ct]) : 'class_fun_binding));
      [Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj (class_expr : 'class_expr Grammar.Entry.e))],
      Gramext.action
        (fun (ce : 'class_expr) _ (loc : Ploc.t) ->
           (ce : 'class_fun_binding))]];
    Grammar.Entry.obj
      (class_type_parameters : 'class_type_parameters Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "[");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (type_parameter : 'type_parameter Grammar.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__140));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__140));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__140))]);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (tpl : 'e__140) _ (loc : Ploc.t) ->
           (Qast.Tuple [Qast.Loc; tpl] : 'class_type_parameters));
      [],
      Gramext.action
        (fun (loc : Ploc.t) ->
           (Qast.Tuple [Qast.Loc; Qast.VaVal (Qast.List [])] :
            'class_type_parameters))]];
    Grammar.Entry.obj (class_fun_def : 'class_fun_def Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "->");
       Gramext.Snterm
         (Grammar.Entry.obj (class_expr : 'class_expr Grammar.Entry.e))],
      Gramext.action
        (fun (ce : 'class_expr) _ (loc : Ploc.t) -> (ce : 'class_fun_def));
      [Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (ce : 'class_fun_def) (p : 'ipatt) (loc : Ploc.t) ->
           (Qast.Node ("CeFun", [Qast.Loc; p; ce]) : 'class_fun_def))]];
    Grammar.Entry.obj (class_expr : 'class_expr Grammar.Entry.e), None,
    [Some "top", None,
     [[Gramext.Stoken ("", "let");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "rec"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__141));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__141));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__141));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__141));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__141))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (let_binding : 'let_binding Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'let_binding list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__142));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__142));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__142))]);
       Gramext.Stoken ("", "in"); Gramext.Sself],
      Gramext.action
        (fun (ce : 'class_expr) _ (lb : 'e__142) (rf : 'e__141) _
             (loc : Ploc.t) ->
           (Qast.Node ("CeLet", [Qast.Loc; rf; lb; ce]) : 'class_expr));
      [Gramext.Stoken ("", "fun");
       Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Snterm
         (Grammar.Entry.obj
            (class_fun_def : 'class_fun_def Grammar.Entry.e))],
      Gramext.action
        (fun (ce : 'class_fun_def) (p : 'ipatt) _ (loc : Ploc.t) ->
           (Qast.Node ("CeFun", [Qast.Loc; p; ce]) : 'class_expr))];
     Some "apply", Some Gramext.LeftA,
     [[Gramext.Sself;
       Gramext.Snterml
         (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e), "label")],
      Gramext.action
        (fun (e : 'expr) (ce : 'class_expr) (loc : Ploc.t) ->
           (Qast.Node ("CeApp", [Qast.Loc; ce; e]) : 'class_expr))];
     Some "simple", None,
     [[Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (ce : 'class_expr) _ (loc : Ploc.t) -> (ce : 'class_expr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (class_type : 'class_type Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (ct : 'class_type) _ (ce : 'class_expr) _ (loc : Ploc.t) ->
           (Qast.Node ("CeTyc", [Qast.Loc; ce; ct]) : 'class_expr));
      [Gramext.Stoken ("", "[");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (a : 'ctyp list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__145));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__145));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__145))]);
       Gramext.Stoken ("", "]");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj
                   (class_longident : 'class_longident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'class_longident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__146));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__146));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__146))])],
      Gramext.action
        (fun (ci : 'e__146) _ (ctcl : 'e__145) _ (loc : Ploc.t) ->
           (Qast.Node ("CeCon", [Qast.Loc; ci; ctcl]) : 'class_expr));
      [Gramext.Stoken ("", "object");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (class_self_patt : 'class_self_patt Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'class_self_patt option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__144));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__144));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__144))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (class_structure : 'class_structure Grammar.Entry.e));
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (cf : 'class_structure) (cspo : 'e__144) _ (loc : Ploc.t) ->
           (Qast.Node ("CeStr", [Qast.Loc; cspo; cf]) : 'class_expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj
                   (class_longident : 'class_longident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'class_longident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__143));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__143));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__143))])],
      Gramext.action
        (fun (ci : 'e__143) (loc : Ploc.t) ->
           (Qast.Node ("CeCon", [Qast.Loc; ci; Qast.VaVal (Qast.List [])]) :
            'class_expr))]];
    Grammar.Entry.obj (class_structure : 'class_structure Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (class_str_item : 'class_str_item Grammar.Entry.e));
                     Gramext.Stoken ("", ";")],
                    Gramext.action
                      (fun _ (cf : 'class_str_item) (loc : Ploc.t) ->
                         (cf : 'e__147))])],
             Gramext.action
               (fun (a : 'e__147 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__148));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__148));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__148))])],
      Gramext.action
        (fun (cf : 'e__148) (loc : Ploc.t) -> (cf : 'class_structure))]];
    Grammar.Entry.obj (class_self_patt : 'class_self_patt Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (t : 'ctyp) _ (p : 'patt) _ (loc : Ploc.t) ->
           (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'class_self_patt));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (p : 'patt) _ (loc : Ploc.t) -> (p : 'class_self_patt))]];
    Grammar.Entry.obj (class_str_item : 'class_str_item Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "initializer");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (se : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("CrIni", [Qast.Loc; se]) : 'class_str_item));
      [Gramext.Stoken ("", "type");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
           (Qast.Node ("CrCtr", [Qast.Loc; t1; t2]) : 'class_str_item));
      [Gramext.Stoken ("", "method");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "!"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__159));
             [Gramext.Stoken ("ANTIQUOT", "_!")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_!", loc, a) : 'e__159));
             [Gramext.Stoken ("ANTIQUOT", "!")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("!", loc, a)) : 'e__159))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "private"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__160));
             [Gramext.Stoken ("ANTIQUOT", "_priv")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_priv", loc, a) : 'e__160));
             [Gramext.Stoken ("ANTIQUOT", "priv")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) : 'e__160))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'lident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__161));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__161));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__161));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__161));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__161))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj (polyt : 'polyt Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'polyt option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__162));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__162));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__162))]);
       Gramext.Snterm
         (Grammar.Entry.obj (fun_binding : 'fun_binding Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'fun_binding) (topt : 'e__162) (l : 'e__161) (pf : 'e__160)
             (ovf : 'e__159) _ (loc : Ploc.t) ->
           (Qast.Node ("CrMth", [Qast.Loc; ovf; pf; l; topt; e]) :
            'class_str_item));
      [Gramext.Stoken ("", "method"); Gramext.Stoken ("", "virtual");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "private"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__157));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__157));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__157));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__157));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__157))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'lident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__158));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__158));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__158));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__158));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__158))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (l : 'e__158) (pf : 'e__157) _ _ (loc : Ploc.t) ->
           (Qast.Node ("CrVir", [Qast.Loc; pf; l; t]) : 'class_str_item));
      [Gramext.Stoken ("", "value"); Gramext.Stoken ("", "virtual");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "mutable"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__155));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__155));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__155));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__155));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__155))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'lident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__156));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__156));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__156));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__156));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__156))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (lab : 'e__156) (mf : 'e__155) _ _
             (loc : Ploc.t) ->
           (Qast.Node ("CrVav", [Qast.Loc; mf; lab; t]) : 'class_str_item));
      [Gramext.Stoken ("", "value");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "!"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__152));
             [Gramext.Stoken ("ANTIQUOT", "_!")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_!", loc, a) : 'e__152));
             [Gramext.Stoken ("ANTIQUOT", "!")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("!", loc, a)) : 'e__152))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "mutable"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__153));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__153));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__153));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__153));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__153))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'lident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__154));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__154));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__154));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__154));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__154))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (cvalue_binding : 'cvalue_binding Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'cvalue_binding) (lab : 'e__154) (mf : 'e__153)
             (ovf : 'e__152) _ (loc : Ploc.t) ->
           (Qast.Node ("CrVal", [Qast.Loc; ovf; mf; lab; e]) :
            'class_str_item));
      [Gramext.Stoken ("", "inherit");
       Gramext.Snterm
         (Grammar.Entry.obj (class_expr : 'class_expr Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (as_lident : 'as_lident Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'as_lident option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__151));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__151));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__151))])],
      Gramext.action
        (fun (pb : 'e__151) (ce : 'class_expr) _ (loc : Ploc.t) ->
           (Qast.Node ("CrInh", [Qast.Loc; ce; pb]) : 'class_str_item));
      [Gramext.Stoken ("", "declare");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (class_str_item : 'class_str_item Grammar.Entry.e));
                     Gramext.Stoken ("", ";")],
                    Gramext.action
                      (fun _ (s : 'class_str_item) (loc : Ploc.t) ->
                         (s : 'e__149))])],
             Gramext.action
               (fun (a : 'e__149 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__150));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__150));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__150))]);
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (st : 'e__150) _ (loc : Ploc.t) ->
           (Qast.Node ("CrDcl", [Qast.Loc; st]) : 'class_str_item))]];
    Grammar.Entry.obj (as_lident : 'as_lident Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "as"); Gramext.Stoken ("LIDENT", "")],
      Gramext.action
        (fun (i : string) _ (loc : Ploc.t) -> (mkident i : 'as_lident))]];
    Grammar.Entry.obj (polyt : 'polyt Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action (fun (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'polyt))]];
    Grammar.Entry.obj (cvalue_binding : 'cvalue_binding Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", ":>");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
           (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option None; t]) :
            'cvalue_binding));
      [Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ":>");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (t2 : 'ctyp) _ (t : 'ctyp) _ (loc : Ploc.t) ->
           (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option (Some t); t2]) :
            'cvalue_binding));
      [Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
           (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'cvalue_binding));
      [Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'cvalue_binding))]];
    Grammar.Entry.obj (lident : 'lident Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("LIDENT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) -> (mkident i : 'lident))]];
    Grammar.Entry.obj (class_type : 'class_type Grammar.Entry.e), None,
    [Some "top", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", "[");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (a : 'ctyp list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__166));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__166));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__166))]);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (tl : 'e__166) _ (ct : 'class_type) (loc : Ploc.t) ->
           (Qast.Node ("CtCon", [Qast.Loc; ct; tl]) : 'class_type));
      [Gramext.Stoken ("", "object");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (class_self_type : 'class_self_type Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'class_self_type option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__163));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__163));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__163))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (class_sig_item : 'class_sig_item Grammar.Entry.e));
                     Gramext.Stoken ("", ";")],
                    Gramext.action
                      (fun _ (csf : 'class_sig_item) (loc : Ploc.t) ->
                         (csf : 'e__164))])],
             Gramext.action
               (fun (a : 'e__164 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__165));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__165));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__165))]);
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (csf : 'e__165) (cst : 'e__163) _ (loc : Ploc.t) ->
           (Qast.Node ("CtSig", [Qast.Loc; cst; csf]) : 'class_type));
      [Gramext.Stoken ("", "[");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "]"); Gramext.Stoken ("", "->"); Gramext.Sself],
      Gramext.action
        (fun (ct : 'class_type) _ _ (t : 'ctyp) _ (loc : Ploc.t) ->
           (Qast.Node ("CtFun", [Qast.Loc; t; ct]) : 'class_type))];
     Some "apply", None,
     [[Gramext.Sself; Gramext.Sself],
      Gramext.action
        (fun (ct2 : 'class_type) (ct1 : 'class_type) (loc : Ploc.t) ->
           (Qast.Node ("CtApp", [Qast.Loc; ct1; ct2]) : 'class_type))];
     Some "dot", None,
     [[Gramext.Sself; Gramext.Stoken ("", "."); Gramext.Sself],
      Gramext.action
        (fun (ct2 : 'class_type) _ (ct1 : 'class_type) (loc : Ploc.t) ->
           (Qast.Node ("CtAcc", [Qast.Loc; ct1; ct2]) : 'class_type))];
     Some "simple", None,
     [[Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (ct : 'class_type) _ (loc : Ploc.t) -> (ct : 'class_type));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("UIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__168));
             [Gramext.Stoken ("ANTIQUOT", "_id")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_id", loc, a) : 'e__168));
             [Gramext.Stoken ("ANTIQUOT", "id")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("id", loc, a)) : 'e__168))])],
      Gramext.action
        (fun (i : 'e__168) (loc : Ploc.t) ->
           (Qast.Node ("CtIde", [Qast.Loc; i]) : 'class_type));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__167));
             [Gramext.Stoken ("ANTIQUOT", "_id")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_id", loc, a) : 'e__167));
             [Gramext.Stoken ("ANTIQUOT", "id")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("id", loc, a)) : 'e__167))])],
      Gramext.action
        (fun (i : 'e__167) (loc : Ploc.t) ->
           (Qast.Node ("CtIde", [Qast.Loc; i]) : 'class_type))]];
    Grammar.Entry.obj (class_self_type : 'class_self_type Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'class_self_type))]];
    Grammar.Entry.obj (class_sig_item : 'class_sig_item Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "type");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
           (Qast.Node ("CgCtr", [Qast.Loc; t1; t2]) : 'class_sig_item));
      [Gramext.Stoken ("", "method");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "private"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__175));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__175));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__175));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__175));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__175))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'lident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__176));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__176));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__176));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__176));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__176))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (l : 'e__176) (pf : 'e__175) _ (loc : Ploc.t) ->
           (Qast.Node ("CgMth", [Qast.Loc; pf; l; t]) : 'class_sig_item));
      [Gramext.Stoken ("", "method"); Gramext.Stoken ("", "virtual");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "private"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__173));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__173));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__173));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__173));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__173))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'lident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__174));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__174));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__174));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__174));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__174))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (l : 'e__174) (pf : 'e__173) _ _ (loc : Ploc.t) ->
           (Qast.Node ("CgVir", [Qast.Loc; pf; l; t]) : 'class_sig_item));
      [Gramext.Stoken ("", "value");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "mutable"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__171));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__171));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__171));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__171));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__171))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'lident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__172));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__172));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__172));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__172));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__172))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (l : 'e__172) (mf : 'e__171) _ (loc : Ploc.t) ->
           (Qast.Node ("CgVal", [Qast.Loc; mf; l; t]) : 'class_sig_item));
      [Gramext.Stoken ("", "inherit");
       Gramext.Snterm
         (Grammar.Entry.obj (class_type : 'class_type Grammar.Entry.e))],
      Gramext.action
        (fun (cs : 'class_type) _ (loc : Ploc.t) ->
           (Qast.Node ("CgInh", [Qast.Loc; cs]) : 'class_sig_item));
      [Gramext.Stoken ("", "declare");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0
                (Gramext.srules
                   [[Gramext.Snterm
                       (Grammar.Entry.obj
                          (class_sig_item : 'class_sig_item Grammar.Entry.e));
                     Gramext.Stoken ("", ";")],
                    Gramext.action
                      (fun _ (s : 'class_sig_item) (loc : Ploc.t) ->
                         (s : 'e__169))])],
             Gramext.action
               (fun (a : 'e__169 list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__170));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__170));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__170))]);
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (st : 'e__170) _ (loc : Ploc.t) ->
           (Qast.Node ("CgDcl", [Qast.Loc; st]) : 'class_sig_item))]];
    Grammar.Entry.obj
      (class_description : 'class_description Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "virtual"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__177));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__177));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__177));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__177));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__177))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__178));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__178));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__178));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__178));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__178))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (class_type_parameters : 'class_type_parameters Grammar.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Grammar.Entry.obj (class_type : 'class_type Grammar.Entry.e))],
      Gramext.action
        (fun (ct : 'class_type) _ (ctp : 'class_type_parameters) (n : 'e__178)
             (vf : 'e__177) (loc : Ploc.t) ->
           (Qast.Record
              ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", n;
               "ciExp", ct] :
            'class_description))]];
    Grammar.Entry.obj
      (class_type_declaration : 'class_type_declaration Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "virtual"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__179));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__179));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__179));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__179));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__179))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__180));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__180));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__180));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__180));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__180))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (class_type_parameters : 'class_type_parameters Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj (class_type : 'class_type Grammar.Entry.e))],
      Gramext.action
        (fun (cs : 'class_type) _ (ctp : 'class_type_parameters) (n : 'e__180)
             (vf : 'e__179) (loc : Ploc.t) ->
           (Qast.Record
              ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", n;
               "ciExp", cs] :
            'class_type_declaration))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.Level "apply"),
    [None, Some Gramext.LeftA,
     [[Gramext.Stoken ("", "object");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (class_self_patt : 'class_self_patt Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'class_self_patt option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__182));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__182));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__182))]);
       Gramext.Snterm
         (Grammar.Entry.obj
            (class_structure : 'class_structure Grammar.Entry.e));
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (cf : 'class_structure) (cspo : 'e__182) _ (loc : Ploc.t) ->
           (Qast.Node ("ExObj", [Qast.Loc; cspo; cf]) : 'expr));
      [Gramext.Stoken ("", "new");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj
                   (class_longident : 'class_longident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'class_longident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__181));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__181));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__181))])],
      Gramext.action
        (fun (i : 'e__181) _ (loc : Ploc.t) ->
           (Qast.Node ("ExNew", [Qast.Loc; i]) : 'expr))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.Level "."),
    [None, None,
     [[Gramext.Sself; Gramext.Stoken ("", "#");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'lident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__183));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__183));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__183));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__183));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__183))])],
      Gramext.action
        (fun (lab : 'e__183) _ (e : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("ExSnd", [Qast.Loc; e; lab]) : 'expr))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.Level "simple"),
    [None, None,
     [[Gramext.Stoken ("", "{<");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (field_expr : 'field_expr Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'field_expr list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__184));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__184));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__184))]);
       Gramext.Stoken ("", ">}")],
      Gramext.action
        (fun _ (fel : 'e__184) _ (loc : Ploc.t) ->
           (Qast.Node ("ExOvr", [Qast.Loc; fel]) : 'expr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ":>");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option None; t]) : 'expr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ":>");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (t2 : 'ctyp) _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option (Some t); t2]) :
            'expr))]];
    Grammar.Entry.obj (field_expr : 'field_expr Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm (Grammar.Entry.obj (lident : 'lident Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (l : 'lident) (loc : Ploc.t) ->
           (Qast.Tuple [l; e] : 'field_expr))]];
    Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e),
    Some (Gramext.Level "simple"),
    [None, None,
     [[Gramext.Stoken ("", "<");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (field : 'field Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'field list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__186));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__186));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__186))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", ".."))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__187));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__187));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__187));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__187));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__187))]);
       Gramext.Stoken ("", ">")],
      Gramext.action
        (fun _ (v : 'e__187) (ml : 'e__186) _ (loc : Ploc.t) ->
           (Qast.Node ("TyObj", [Qast.Loc; ml; v]) : 'ctyp));
      [Gramext.Stoken ("", "#");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj
                   (class_longident : 'class_longident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'class_longident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__185));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__185));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__185))])],
      Gramext.action
        (fun (id : 'e__185) _ (loc : Ploc.t) ->
           (Qast.Node ("TyCls", [Qast.Loc; id]) : 'ctyp))]];
    Grammar.Entry.obj (field : 'field Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("LIDENT", ""); Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (lab : string) (loc : Ploc.t) ->
           (Qast.Tuple [mkident lab; t] : 'field))]];
    Grammar.Entry.obj (typevar : 'typevar Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "'");
       Gramext.Snterm (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
      Gramext.action (fun (i : 'ident) _ (loc : Ploc.t) -> (i : 'typevar))]];
    Grammar.Entry.obj (class_longident : 'class_longident Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("LIDENT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) ->
           (Qast.List [mkident i] : 'class_longident));
      [Gramext.Stoken ("UIDENT", ""); Gramext.Stoken ("", ".");
       Gramext.Sself],
      Gramext.action
        (fun (l : 'class_longident) _ (m : string) (loc : Ploc.t) ->
           (Qast.Cons (mkident m, l) : 'class_longident))]];
    (* Labels *)
    Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e),
    Some (Gramext.After "arrow"),
    [None, Some Gramext.NonA,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_qic : 'a_qic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__189));
             [Gramext.Stoken ("QUESTIONIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__189));
             [Gramext.Stoken ("ANTIQUOT", "?_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("?_:", loc, a) : 'e__189));
             [Gramext.Stoken ("ANTIQUOT", "?:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) : 'e__189))]);
       Gramext.Sself],
      Gramext.action
        (fun (t : 'ctyp) (i : 'e__189) (loc : Ploc.t) ->
           (Qast.Node ("TyOlb", [Qast.Loc; i; t]) : 'ctyp));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_tic : 'a_tic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__188));
             [Gramext.Stoken ("TILDEIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__188));
             [Gramext.Stoken ("ANTIQUOT", "~_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("~_:", loc, a) : 'e__188));
             [Gramext.Stoken ("ANTIQUOT", "~:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) : 'e__188))]);
       Gramext.Sself],
      Gramext.action
        (fun (t : 'ctyp) (i : 'e__188) (loc : Ploc.t) ->
           (Qast.Node ("TyLab", [Qast.Loc; i; t]) : 'ctyp))]];
    Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e),
    Some (Gramext.Level "simple"),
    [None, None,
     [[Gramext.Stoken ("", "["); Gramext.Stoken ("", "<");
       Gramext.Snterm
         (Grammar.Entry.obj
            (poly_variant_list : 'poly_variant_list Grammar.Entry.e));
       Gramext.Stoken ("", ">");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (name_tag : 'name_tag Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'name_tag list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__190));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__190));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__190))]);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (ntl : 'e__190) _ (rfl : 'poly_variant_list) _ _
             (loc : Ploc.t) ->
           (Qast.Node
              ("TyVrn",
               [Qast.Loc; rfl; Qast.Option (Some (Qast.Option (Some ntl)))]) :
            'ctyp));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("", "<");
       Gramext.Snterm
         (Grammar.Entry.obj
            (poly_variant_list : 'poly_variant_list Grammar.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
           (Qast.Node
              ("TyVrn",
               [Qast.Loc; rfl;
                Qast.Option
                  (Some (Qast.Option (Some (Qast.VaVal (Qast.List [])))))]) :
            'ctyp));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("", ">");
       Gramext.Snterm
         (Grammar.Entry.obj
            (poly_variant_list : 'poly_variant_list Grammar.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
           (Qast.Node
              ("TyVrn",
               [Qast.Loc; rfl; Qast.Option (Some (Qast.Option None))]) :
            'ctyp));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("", "=");
       Gramext.Snterm
         (Grammar.Entry.obj
            (poly_variant_list : 'poly_variant_list Grammar.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
           (Qast.Node ("TyVrn", [Qast.Loc; rfl; Qast.Option None]) :
            'ctyp))]];
    Grammar.Entry.obj
      (poly_variant_list : 'poly_variant_list Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist0sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (poly_variant : 'poly_variant Grammar.Entry.e)),
                 Gramext.Stoken ("", "|"), false)],
             Gramext.action
               (fun (a : 'poly_variant list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__191));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__191));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__191))])],
      Gramext.action
        (fun (rfl : 'e__191) (loc : Ploc.t) -> (rfl : 'poly_variant_list))]];
    Grammar.Entry.obj (poly_variant : 'poly_variant Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) (loc : Ploc.t) ->
           (Qast.Node ("PvInh", [Qast.Loc; t]) : 'poly_variant));
      [Gramext.Stoken ("", "`");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'ident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__193));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__193));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__193))]);
       Gramext.Stoken ("", "of");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sflag (Gramext.Stoken ("", "&"))],
             Gramext.action
               (fun (a : bool) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Bool a) : 'e__194));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__194));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__194));
             [Gramext.Stoken ("ANTIQUOT", "_flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_flag", loc, a) : 'e__194));
             [Gramext.Stoken ("ANTIQUOT", "flag")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) : 'e__194))]);
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e)),
                 Gramext.Stoken ("", "&"), false)],
             Gramext.action
               (fun (a : 'ctyp list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__195));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__195));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__195))])],
      Gramext.action
        (fun (l : 'e__195) (ao : 'e__194) _ (i : 'e__193) _ (loc : Ploc.t) ->
           (Qast.Node ("PvTag", [Qast.Loc; i; ao; l]) : 'poly_variant));
      [Gramext.Stoken ("", "`");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'ident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__192));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__192));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__192))])],
      Gramext.action
        (fun (i : 'e__192) _ (loc : Ploc.t) ->
           (Qast.Node
              ("PvTag",
               [Qast.Loc; i; Qast.VaVal (Qast.Bool true);
                Qast.VaVal (Qast.List [])]) :
            'poly_variant))]];
    Grammar.Entry.obj (name_tag : 'name_tag Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "`");
       Gramext.Snterm (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
      Gramext.action (fun (i : 'ident) _ (loc : Ploc.t) -> (i : 'name_tag))]];
    Grammar.Entry.obj (patt : 'patt Grammar.Entry.e),
    Some (Gramext.Level "simple"),
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj
            (patt_option_label : 'patt_option_label Grammar.Entry.e))],
      Gramext.action
        (fun (p : 'patt_option_label) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in p : 'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_ti : 'a_ti Grammar.Entry.e))],
             Gramext.action (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__202));
             [Gramext.Stoken ("TILDEIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__202));
             [Gramext.Stoken ("ANTIQUOT", "~_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("~_", loc, a) : 'e__202));
             [Gramext.Stoken ("ANTIQUOT", "~")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("~", loc, a)) : 'e__202))])],
      Gramext.action
        (fun (i : 'e__202) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in
            Qast.Node
              ("PaLab",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple
                        [Qast.Node ("PaLid", [Qast.Loc; i]);
                         Qast.VaVal (Qast.Option None)]])]) :
            'patt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_tic : 'a_tic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__201));
             [Gramext.Stoken ("TILDEIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__201));
             [Gramext.Stoken ("ANTIQUOT", "~_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("~_:", loc, a) : 'e__201));
             [Gramext.Stoken ("ANTIQUOT", "~:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) : 'e__201))]);
       Gramext.Sself],
      Gramext.action
        (fun (p : 'patt) (i : 'e__201) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in
            Qast.Node
              ("PaLab",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple
                        [Qast.Node ("PaLid", [Qast.Loc; i]);
                         Qast.VaVal (Qast.Option (Some p))]])]) :
            'patt));
      [Gramext.Stoken ("", "?"); Gramext.Stoken ("", "{");
       Gramext.Snterm
         (Grammar.Entry.obj (patt_tcon : 'patt_tcon Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.srules
                   [[Gramext.Stoken ("", "=");
                     Gramext.Snterm
                       (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
                    Gramext.action
                      (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'e__199))])],
             Gramext.action
               (fun (a : 'e__199 option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__200));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__200));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__200))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (eo : 'e__200) (p : 'patt_tcon) _ _ (loc : Ploc.t) ->
           (Qast.Node ("PaOlb", [Qast.Loc; p; eo]) : 'patt));
      [Gramext.Stoken ("", "~"); Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (patt_tcon_opt_eq_patt :
                       'patt_tcon_opt_eq_patt Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'patt_tcon_opt_eq_patt list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__198));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__198));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__198))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (lppo : 'e__198) _ _ (loc : Ploc.t) ->
           (Qast.Node ("PaLab", [Qast.Loc; lppo]) : 'patt));
      [Gramext.Stoken ("", "#");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (mod_ident : 'mod_ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'mod_ident) (loc : Ploc.t) ->
                  (Qast.VaVal a : 'e__197));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__197));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__197));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__197));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__197))])],
      Gramext.action
        (fun (sl : 'e__197) _ (loc : Ploc.t) ->
           (Qast.Node ("PaTyp", [Qast.Loc; sl]) : 'patt));
      [Gramext.Stoken ("", "`");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'ident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__196));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__196));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__196))])],
      Gramext.action
        (fun (s : 'e__196) _ (loc : Ploc.t) ->
           (Qast.Node ("PaVrn", [Qast.Loc; s]) : 'patt))]];
    Grammar.Entry.obj
      (patt_tcon_opt_eq_patt : 'patt_tcon_opt_eq_patt Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj (patt_tcon : 'patt_tcon Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.srules
                   [[Gramext.Stoken ("", "=");
                     Gramext.Snterm
                       (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e))],
                    Gramext.action
                      (fun (p : 'patt) _ (loc : Ploc.t) -> (p : 'e__203))])],
             Gramext.action
               (fun (a : 'e__203 option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__204));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__204));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__204))])],
      Gramext.action
        (fun (po : 'e__204) (p : 'patt_tcon) (loc : Ploc.t) ->
           (Qast.Tuple [p; po] : 'patt_tcon_opt_eq_patt))]];
    Grammar.Entry.obj (patt_tcon : 'patt_tcon Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
           (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'patt_tcon));
      [Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e))],
      Gramext.action (fun (p : 'patt) (loc : Ploc.t) -> (p : 'patt_tcon))]];
    Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj
            (patt_option_label : 'patt_option_label Grammar.Entry.e))],
      Gramext.action
        (fun (p : 'patt_option_label) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in p : 'ipatt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_ti : 'a_ti Grammar.Entry.e))],
             Gramext.action (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__209));
             [Gramext.Stoken ("TILDEIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__209));
             [Gramext.Stoken ("ANTIQUOT", "~_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("~_", loc, a) : 'e__209));
             [Gramext.Stoken ("ANTIQUOT", "~")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("~", loc, a)) : 'e__209))])],
      Gramext.action
        (fun (i : 'e__209) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in
            Qast.Node
              ("PaLab",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple
                        [Qast.Node ("PaLid", [Qast.Loc; i]);
                         Qast.VaVal (Qast.Option None)]])]) :
            'ipatt));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_tic : 'a_tic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__208));
             [Gramext.Stoken ("TILDEIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__208));
             [Gramext.Stoken ("ANTIQUOT", "~_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("~_:", loc, a) : 'e__208));
             [Gramext.Stoken ("ANTIQUOT", "~:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) : 'e__208))]);
       Gramext.Sself],
      Gramext.action
        (fun (p : 'ipatt) (i : 'e__208) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in
            Qast.Node
              ("PaLab",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple
                        [Qast.Node ("PaLid", [Qast.Loc; i]);
                         Qast.VaVal (Qast.Option (Some p))]])]) :
            'ipatt));
      [Gramext.Stoken ("", "?"); Gramext.Stoken ("", "{");
       Gramext.Snterm
         (Grammar.Entry.obj (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.srules
                   [[Gramext.Stoken ("", "=");
                     Gramext.Snterm
                       (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
                    Gramext.action
                      (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'e__206))])],
             Gramext.action
               (fun (a : 'e__206 option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__207));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__207));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__207))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (eo : 'e__207) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
           (Qast.Node ("PaOlb", [Qast.Loc; p; eo]) : 'ipatt));
      [Gramext.Stoken ("", "~"); Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (ipatt_tcon_opt_eq_patt :
                       'ipatt_tcon_opt_eq_patt Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'ipatt_tcon_opt_eq_patt list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__205));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__205));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__205))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (lppo : 'e__205) _ _ (loc : Ploc.t) ->
           (Qast.Node ("PaLab", [Qast.Loc; lppo]) : 'ipatt))]];
    Grammar.Entry.obj
      (ipatt_tcon_opt_eq_patt : 'ipatt_tcon_opt_eq_patt Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.srules
                   [[Gramext.Stoken ("", "=");
                     Gramext.Snterm
                       (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e))],
                    Gramext.action
                      (fun (p : 'patt) _ (loc : Ploc.t) -> (p : 'e__210))])],
             Gramext.action
               (fun (a : 'e__210 option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__211));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__211));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__211))])],
      Gramext.action
        (fun (po : 'e__211) (p : 'ipatt_tcon) (loc : Ploc.t) ->
           (Qast.Tuple [p; po] : 'ipatt_tcon_opt_eq_patt))]];
    Grammar.Entry.obj (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e))],
      Gramext.action
        (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
           (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'ipatt_tcon));
      [Gramext.Snterm (Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e))],
      Gramext.action (fun (p : 'ipatt) (loc : Ploc.t) -> (p : 'ipatt_tcon))]];
    Grammar.Entry.obj
      (patt_option_label : 'patt_option_label Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "?"); Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__224));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__224));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__224));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__224));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__224))]);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (i : 'e__224) _ _ (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                Qast.VaVal (Qast.Option None)]) :
            'patt_option_label));
      [Gramext.Stoken ("", "?"); Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__223));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__223));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__223));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__223));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__223))]);
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (e : 'expr) _ (i : 'e__223) _ _ (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                Qast.VaVal (Qast.Option (Some e))]) :
            'patt_option_label));
      [Gramext.Stoken ("", "?"); Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__222));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__222));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__222));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__222));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__222))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (t : 'ctyp) _ (i : 'e__222) _ _ (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc;
                Qast.Node
                  ("PaTyc",
                   [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                Qast.VaVal (Qast.Option None)]) :
            'patt_option_label));
      [Gramext.Stoken ("", "?"); Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__221));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__221));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__221));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__221));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__221))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (e : 'expr) _ (t : 'ctyp) _ (i : 'e__221) _ _ (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc;
                Qast.Node
                  ("PaTyc",
                   [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                Qast.VaVal (Qast.Option (Some e))]) :
            'patt_option_label));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_qi : 'a_qi Grammar.Entry.e))],
             Gramext.action (fun (a : 'a_qi) (loc : Ploc.t) -> (a : 'e__220));
             [Gramext.Stoken ("QUESTIONIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__220));
             [Gramext.Stoken ("ANTIQUOT", "?_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("?_", loc, a) : 'e__220));
             [Gramext.Stoken ("ANTIQUOT", "?")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("?", loc, a)) : 'e__220))])],
      Gramext.action
        (fun (i : 'e__220) (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                Qast.VaVal (Qast.Option None)]) :
            'patt_option_label));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_qic : 'a_qic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__218));
             [Gramext.Stoken ("QUESTIONIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__218));
             [Gramext.Stoken ("ANTIQUOT", "?_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("?_:", loc, a) : 'e__218));
             [Gramext.Stoken ("ANTIQUOT", "?:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) : 'e__218))]);
       Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__219));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__219));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__219));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__219));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__219))]);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (j : 'e__219) _ (i : 'e__218) (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                Qast.VaVal
                  (Qast.Option
                     (Some (Qast.Node ("ExLid", [Qast.Loc; j]))))]) :
            'patt_option_label));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_qic : 'a_qic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__216));
             [Gramext.Stoken ("QUESTIONIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__216));
             [Gramext.Stoken ("ANTIQUOT", "?_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("?_:", loc, a) : 'e__216));
             [Gramext.Stoken ("ANTIQUOT", "?:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) : 'e__216))]);
       Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__217));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__217));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__217));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__217));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__217))]);
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (e : 'expr) _ (j : 'e__217) _ (i : 'e__216) (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                Qast.VaVal
                  (Qast.Option
                     (Some
                        (Qast.Node
                           ("ExOlb",
                            [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; j]);
                             Qast.VaVal (Qast.Option (Some e))]))))]) :
            'patt_option_label));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_qic : 'a_qic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__214));
             [Gramext.Stoken ("QUESTIONIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__214));
             [Gramext.Stoken ("ANTIQUOT", "?_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("?_:", loc, a) : 'e__214));
             [Gramext.Stoken ("ANTIQUOT", "?:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) : 'e__214))]);
       Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__215));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__215));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__215));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__215));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__215))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (t : 'ctyp) _ (j : 'e__215) _ (i : 'e__214) (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc;
                Qast.Node
                  ("PaTyc",
                   [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                Qast.VaVal
                  (Qast.Option
                     (Some
                        (Qast.Node
                           ("ExOlb",
                            [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; j]);
                             Qast.VaVal (Qast.Option None)]))))]) :
            'patt_option_label));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_qic : 'a_qic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__212));
             [Gramext.Stoken ("QUESTIONIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__212));
             [Gramext.Stoken ("ANTIQUOT", "?_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("?_:", loc, a) : 'e__212));
             [Gramext.Stoken ("ANTIQUOT", "?:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) : 'e__212))]);
       Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__213));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__213));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__213));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__213));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__213))]);
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (e : 'expr) _ (t : 'ctyp) _ (j : 'e__213) _ (i : 'e__212)
             (loc : Ploc.t) ->
           (Qast.Node
              ("PaOlb",
               [Qast.Loc;
                Qast.Node
                  ("PaTyc",
                   [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                Qast.VaVal
                  (Qast.Option
                     (Some
                        (Qast.Node
                           ("ExOlb",
                            [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; j]);
                             Qast.VaVal (Qast.Option (Some e))]))))]) :
            'patt_option_label))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.After "apply"),
    [Some "label", Some Gramext.NonA,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_qi : 'a_qi Grammar.Entry.e))],
             Gramext.action (fun (a : 'a_qi) (loc : Ploc.t) -> (a : 'e__230));
             [Gramext.Stoken ("QUESTIONIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__230));
             [Gramext.Stoken ("ANTIQUOT", "?_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("?_", loc, a) : 'e__230));
             [Gramext.Stoken ("ANTIQUOT", "?")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("?", loc, a)) : 'e__230))])],
      Gramext.action
        (fun (i : 'e__230) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in
            Qast.Node
              ("ExOlb",
               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                Qast.VaVal (Qast.Option None)]) :
            'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_qic : 'a_qic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__229));
             [Gramext.Stoken ("QUESTIONIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__229));
             [Gramext.Stoken ("ANTIQUOT", "?_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("?_:", loc, a) : 'e__229));
             [Gramext.Stoken ("ANTIQUOT", "?:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) : 'e__229))]);
       Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) (i : 'e__229) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in
            Qast.Node
              ("ExOlb",
               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                Qast.VaVal (Qast.Option (Some e))]) :
            'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_ti : 'a_ti Grammar.Entry.e))],
             Gramext.action (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__228));
             [Gramext.Stoken ("TILDEIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__228));
             [Gramext.Stoken ("ANTIQUOT", "~_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("~_", loc, a) : 'e__228));
             [Gramext.Stoken ("ANTIQUOT", "~")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("~", loc, a)) : 'e__228))])],
      Gramext.action
        (fun (i : 'e__228) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in
            Qast.Node
              ("ExLab",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple
                        [Qast.Node ("PaLid", [Qast.Loc; i]);
                         Qast.VaVal (Qast.Option None)]])]) :
            'expr));
      [Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (a_tic : 'a_tic Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__227));
             [Gramext.Stoken ("TILDEIDENTCOLON", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__227));
             [Gramext.Stoken ("ANTIQUOT", "~_:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("~_:", loc, a) : 'e__227));
             [Gramext.Stoken ("ANTIQUOT", "~:")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) : 'e__227))]);
       Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) (i : 'e__227) (loc : Ploc.t) ->
           (let _ = warning_deprecated_since_6_00 loc in
            Qast.Node
              ("ExLab",
               [Qast.Loc;
                Qast.VaVal
                  (Qast.List
                     [Qast.Tuple
                        [Qast.Node ("PaLid", [Qast.Loc; i]);
                         Qast.VaVal (Qast.Option (Some e))]])]) :
            'expr));
      [Gramext.Stoken ("", "?"); Gramext.Stoken ("", "{");
       Gramext.Snterm
         (Grammar.Entry.obj (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (fun_binding : 'fun_binding Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'fun_binding option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__226));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__226));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__226))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (eo : 'e__226) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
           (Qast.Node ("ExOlb", [Qast.Loc; p; eo]) : 'expr));
      [Gramext.Stoken ("", "~"); Gramext.Stoken ("", "{");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (ipatt_tcon_fun_binding :
                       'ipatt_tcon_fun_binding Grammar.Entry.e)),
                 Gramext.Stoken ("", ";"), false)],
             Gramext.action
               (fun (a : 'ipatt_tcon_fun_binding list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__225));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__225));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__225))]);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (lpeo : 'e__225) _ _ (loc : Ploc.t) ->
           (Qast.Node ("ExLab", [Qast.Loc; lpeo]) : 'expr))]];
    Grammar.Entry.obj
      (ipatt_tcon_fun_binding : 'ipatt_tcon_fun_binding Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e));
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (fun_binding : 'fun_binding Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'fun_binding option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__231));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__231));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__231))])],
      Gramext.action
        (fun (eo : 'e__231) (p : 'ipatt_tcon) (loc : Ploc.t) ->
           (Qast.Tuple [p; eo] : 'ipatt_tcon_fun_binding))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.Level "simple"),
    [None, None,
     [[Gramext.Stoken ("", "`");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Snterm
                (Grammar.Entry.obj (ident : 'ident Grammar.Entry.e))],
             Gramext.action
               (fun (a : 'ident) (loc : Ploc.t) -> (Qast.VaVal a : 'e__232));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__232));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__232))])],
      Gramext.action
        (fun (s : 'e__232) _ (loc : Ploc.t) ->
           (Qast.Node ("ExVrn", [Qast.Loc; s]) : 'expr))]];
    Grammar.Entry.obj (direction_flag : 'direction_flag Grammar.Entry.e),
    None,
    [None, None,
     [[Gramext.Stoken ("", "downto")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Qast.Bool false : 'direction_flag));
      [Gramext.Stoken ("", "to")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Qast.Bool true : 'direction_flag))]];
    Grammar.Entry.obj (str_item : 'str_item Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "def");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (joinautomaton : 'joinautomaton Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'joinautomaton list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__233));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__233));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__233))])],
      Gramext.action
        (fun (jal : 'e__233) _ (loc : Ploc.t) ->
           (Qast.Node ("StDef", [Qast.Loc; jal]) : 'str_item))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.Level "top"),
    [None, None,
     [[Gramext.Stoken ("", "def");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (joinautomaton : 'joinautomaton Grammar.Entry.e)),
                 Gramext.Stoken ("", "and"), false)],
             Gramext.action
               (fun (a : 'joinautomaton list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__234));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__234));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__234))]);
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e), "top")],
      Gramext.action
        (fun (e : 'expr) _ (jal : 'e__234) _ (loc : Ploc.t) ->
           (Qast.Node ("ExJdf", [Qast.Loc; jal; e]) : 'expr))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.Level "apply"),
    [None, None,
     [[Gramext.Stoken ("", "reply");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'expr option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__235));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__235));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__235))]);
       Gramext.Stoken ("", "to");
       Gramext.Snterm
         (Grammar.Entry.obj (joinident : 'joinident Grammar.Entry.e))],
      Gramext.action
        (fun (ji : 'joinident) _ (eo : 'e__235) _ (loc : Ploc.t) ->
           (Qast.Node ("ExRpl", [Qast.Loc; eo; ji]) : 'expr))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.Before ":="),
    [None, None,
     [[Gramext.Stoken ("", "spawn"); Gramext.Sself],
      Gramext.action
        (fun (e : 'expr) _ (loc : Ploc.t) ->
           (Qast.Node ("ExSpw", [Qast.Loc; e]) : 'expr))]];
    Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
    Some (Gramext.Level "&&"),
    [None, None,
     [[Gramext.Sself; Gramext.Stoken ("", "&"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
           (Qast.Node ("ExPar", [Qast.Loc; e1; e2]) : 'expr))]];
    Grammar.Entry.obj (joinautomaton : 'joinautomaton Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (joinclause : 'joinclause Grammar.Entry.e)),
                 Gramext.Stoken ("", "or"), false)],
             Gramext.action
               (fun (a : 'joinclause list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__236));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__236));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__236))])],
      Gramext.action
        (fun (jcl : 'e__236) (loc : Ploc.t) ->
           (Qast.Record ["jcLoc", Qast.Loc; "jcVal", jcl] :
            'joinautomaton))]];
    Grammar.Entry.obj (joinclause : 'joinclause Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Slist1sep
                (Gramext.Snterm
                   (Grammar.Entry.obj
                      (joinpattern : 'joinpattern Grammar.Entry.e)),
                 Gramext.Stoken ("", "&"), false)],
             Gramext.action
               (fun (a : 'joinpattern list) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.List a) : 'e__237));
             [Gramext.Stoken ("ANTIQUOT", "_list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_list", loc, a) : 'e__237));
             [Gramext.Stoken ("ANTIQUOT", "list")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("list", loc, a)) : 'e__237))]);
       Gramext.Stoken ("", "=");
       Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))],
      Gramext.action
        (fun (e : 'expr) _ (jpl : 'e__237) (loc : Ploc.t) ->
           (Qast.Tuple [Qast.Loc; jpl; e] : 'joinclause))]];
    Grammar.Entry.obj (joinpattern : 'joinpattern Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Snterm
         (Grammar.Entry.obj (joinident : 'joinident Grammar.Entry.e));
       Gramext.Stoken ("", "(");
       Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.Snterm
                   (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e)))],
             Gramext.action
               (fun (a : 'patt option) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Option a) : 'e__238));
             [Gramext.Stoken ("ANTIQUOT", "_opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_opt", loc, a) : 'e__238));
             [Gramext.Stoken ("ANTIQUOT", "opt")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) : 'e__238))]);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (op : 'e__238) _ (ji : 'joinident) (loc : Ploc.t) ->
           (Qast.Tuple [Qast.Loc; ji; op] : 'joinpattern))]];
    Grammar.Entry.obj (joinident : 'joinident Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Sfacto
         (Gramext.srules
            [[Gramext.Stoken ("LIDENT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.Str a) : 'e__239));
             [Gramext.Stoken ("ANTIQUOT", "_")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_", loc, a) : 'e__239));
             [Gramext.Stoken ("ANTIQUOT", "")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__239));
             [Gramext.Stoken ("ANTIQUOT", "_lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaAnt ("_lid", loc, a) : 'e__239));
             [Gramext.Stoken ("ANTIQUOT", "lid")],
             Gramext.action
               (fun (a : string) (loc : Ploc.t) ->
                  (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) : 'e__239))])],
      Gramext.action
        (fun (i : 'e__239) (loc : Ploc.t) ->
           (Qast.Tuple [Qast.Loc; i] : 'joinident))]];
    (* -- end copy from pa_r to q_MLast -- *)
    Grammar.Entry.obj (a_ti : 'a_ti Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "~"); Gramext.Stoken ("ANTIQUOT", "")],
      Gramext.action
        (fun (a : string) _ (loc : Ploc.t) ->
           (Qast.VaAnt ("~", loc, a) : 'a_ti))]];
    Grammar.Entry.obj (a_tic : 'a_tic Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "~"); Gramext.Stoken ("ANTIQUOT", "");
       Gramext.Stoken ("", ":")],
      Gramext.action
        (fun _ (a : string) _ (loc : Ploc.t) ->
           (Qast.VaAnt ("~", loc, a) : 'a_tic))]];
    Grammar.Entry.obj (a_qi : 'a_qi Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "?"); Gramext.Stoken ("ANTIQUOT", "")],
      Gramext.action
        (fun (a : string) _ (loc : Ploc.t) ->
           (Qast.VaAnt ("?", loc, a) : 'a_qi))]];
    Grammar.Entry.obj (a_qic : 'a_qic Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("", "?"); Gramext.Stoken ("ANTIQUOT", "");
       Gramext.Stoken ("", ":")],
      Gramext.action
        (fun _ (a : string) _ (loc : Ploc.t) ->
           (Qast.VaAnt ("?", loc, a) : 'a_qic))]];
    Grammar.Entry.obj (joinident : 'joinident Grammar.Entry.e), None,
    [None, None,
     [[Gramext.Stoken ("ANTIQUOT", "jid")],
      Gramext.action
        (fun (a : string) (loc : Ploc.t) ->
           (Qast.VaAnt ("jid", loc, a) : 'joinident))]]]);;

(* Antiquotations *)

let antiquot_xtr loc n a =
  if !(Pcaml.strict_mode) then
    Qast.Node (n, [Qast.Loc; Qast.VaAnt ("xtr", loc, a); Qast.Option None])
  else Qast.Apply ("failwith", [Qast.Str "antiquotation not authorized"])
;;

Grammar.extend
  [Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e),
   Some (Gramext.Level "simple"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'module_expr));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "MeXtr" a : 'module_expr));
     [Gramext.Stoken ("ANTIQUOT", "mexp")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("mexp", loc, a) : 'module_expr))]];
   Grammar.Entry.obj (str_item : 'str_item Grammar.Entry.e),
   Some (Gramext.Level "top"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'str_item));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "StXtr" a : 'str_item));
     [Gramext.Stoken ("ANTIQUOT", "stri")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("stri", loc, a) : 'str_item))]];
   Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e),
   Some (Gramext.Level "simple"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'module_type));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "MtXtr" a : 'module_type));
     [Gramext.Stoken ("ANTIQUOT", "mtyp")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("mtyp", loc, a) : 'module_type))]];
   Grammar.Entry.obj (sig_item : 'sig_item Grammar.Entry.e),
   Some (Gramext.Level "top"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'sig_item));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "SgXtr" a : 'sig_item));
     [Gramext.Stoken ("ANTIQUOT", "sigi")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("sigi", loc, a) : 'sig_item))]];
   Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
   Some (Gramext.Level "simple"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "anti")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.Node ("ExAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
           'expr));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "ExXtr" a : 'expr));
     [Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) -> (Qast.VaAnt ("", loc, a) : 'expr));
     [Gramext.Stoken ("ANTIQUOT", "exp")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("exp", loc, a) : 'expr))]];
   Grammar.Entry.obj (patt : 'patt Grammar.Entry.e),
   Some (Gramext.Level "simple"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "anti")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.Node ("PaAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
           'patt));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "PaXtr" a : 'patt));
     [Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) -> (Qast.VaAnt ("", loc, a) : 'patt));
     [Gramext.Stoken ("ANTIQUOT", "pat")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("pat", loc, a) : 'patt))]];
   Grammar.Entry.obj (ipatt : 'ipatt Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "anti")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.Node ("PaAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
           'ipatt));
     [Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'ipatt));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "PaXtr" a : 'ipatt));
     [Gramext.Stoken ("ANTIQUOT", "pat")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("pat", loc, a) : 'ipatt))]];
   Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e),
   Some (Gramext.Level "simple"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) -> (Qast.VaAnt ("", loc, a) : 'ctyp));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "TyXtr" a : 'ctyp));
     [Gramext.Stoken ("ANTIQUOT", "typ")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("typ", loc, a) : 'ctyp))]];
   Grammar.Entry.obj (class_expr : 'class_expr Grammar.Entry.e),
   Some (Gramext.Level "simple"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'class_expr));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "CeXtr" a : 'class_expr))]];
   Grammar.Entry.obj (class_str_item : 'class_str_item Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'class_str_item))]];
   Grammar.Entry.obj (class_sig_item : 'class_sig_item Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'class_sig_item))]];
   Grammar.Entry.obj (class_type : 'class_type Grammar.Entry.e),
   Some (Gramext.Level "simple"),
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT", "")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (Qast.VaAnt ("", loc, a) : 'class_type));
     [Gramext.Stoken ("ANTIQUOT", "xtr")],
     Gramext.action
       (fun (a : string) (loc : Ploc.t) ->
          (antiquot_xtr loc "CtXtr" a : 'class_type))]]];;

let quot_mod = ref [];;
let any_quot_mod = ref "MLast";;

let set_qmod s =
  match try Some (String.index s ',') with Not_found -> None with
    Some i ->
      let q = String.sub s 0 i in
      let m = String.sub s (i + 1) (String.length s - i - 1) in
      quot_mod := (q, m) :: !quot_mod
  | None -> any_quot_mod := s
;;

Pcaml.add_directive "qmod"
  (function
     Some (MLast.ExStr (_, s)) -> set_qmod s
   | Some _ | None -> failwith "bad directive 1");;

let separate_locate s =
  let len = String.length s in
  if len > 0 && s.[0] = '@' then String.sub s 1 (len - 1), true else s, false
;;

let apply_entry e q =
  let f s = Grammar.Entry.parse e (Stream.of_string s) in
  let m () = try List.assoc q !quot_mod with Not_found -> !any_quot_mod in
  let expr s =
    let (s, locate) = separate_locate s in Qast.to_expr (m ()) (f s)
  in
  let patt s =
    let (s, locate) = separate_locate s in
    let qast =
      let qast = f s in
      if locate then
        match qast with
          Qast.Node (n, Qast.Loc :: nl) -> Qast.Node (n, Qast.TrueLoc :: nl)
        | x -> x
      else qast
    in
    Qast.to_patt (m ()) qast
  in
  Quotation.ExAst (expr, patt)
;;

let sig_item_eoi = Grammar.Entry.create gram "sig_item_eoi" in
let str_item_eoi = Grammar.Entry.create gram "str_item_eoi" in
let ctyp_eoi = Grammar.Entry.create gram "ctyp_eoi" in
let patt_eoi = Grammar.Entry.create gram "patt_eoi" in
let expr_eoi = Grammar.Entry.create gram "expr_eoi" in
let module_type_eoi = Grammar.Entry.create gram "module_type_eoi" in
let module_expr_eoi = Grammar.Entry.create gram "module_expr_eoi" in
let class_type_eoi = Grammar.Entry.create gram "class_type_eoi" in
let class_expr_eoi = Grammar.Entry.create gram "class_expr_eoi" in
let class_sig_item_eoi = Grammar.Entry.create gram "class_sig_item_eoi" in
let class_str_item_eoi = Grammar.Entry.create gram "class_str_item_eoi" in
let with_constr_eoi = Grammar.Entry.create gram "with_constr_eoi" in
let poly_variant_eoi = Grammar.Entry.create gram "poly_variant_eoi" in
let type_decl_eoi = Grammar.Entry.create gram "type_decl_eoi" in
Grammar.extend
  [Grammar.Entry.obj (sig_item_eoi : 'sig_item_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (sig_item : 'sig_item Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'sig_item) (loc : Ploc.t) -> (x : 'sig_item_eoi))]];
   Grammar.Entry.obj (str_item_eoi : 'str_item_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (str_item : 'str_item Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'str_item) (loc : Ploc.t) -> (x : 'str_item_eoi))]];
   Grammar.Entry.obj (ctyp_eoi : 'ctyp_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm (Grammar.Entry.obj (ctyp : 'ctyp Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action (fun _ (x : 'ctyp) (loc : Ploc.t) -> (x : 'ctyp_eoi))]];
   Grammar.Entry.obj (patt_eoi : 'patt_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm (Grammar.Entry.obj (patt : 'patt Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action (fun _ (x : 'patt) (loc : Ploc.t) -> (x : 'patt_eoi))]];
   Grammar.Entry.obj (expr_eoi : 'expr_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action (fun _ (x : 'expr) (loc : Ploc.t) -> (x : 'expr_eoi))]];
   Grammar.Entry.obj (module_type_eoi : 'module_type_eoi Grammar.Entry.e),
   None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (module_type : 'module_type Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'module_type) (loc : Ploc.t) -> (x : 'module_type_eoi))]];
   Grammar.Entry.obj (module_expr_eoi : 'module_expr_eoi Grammar.Entry.e),
   None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (module_expr : 'module_expr Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'module_expr) (loc : Ploc.t) -> (x : 'module_expr_eoi))]];
   Grammar.Entry.obj (class_type_eoi : 'class_type_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (class_type : 'class_type Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'class_type) (loc : Ploc.t) -> (x : 'class_type_eoi))]];
   Grammar.Entry.obj (class_expr_eoi : 'class_expr_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (class_expr : 'class_expr Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'class_expr) (loc : Ploc.t) -> (x : 'class_expr_eoi))]];
   Grammar.Entry.obj
     (class_sig_item_eoi : 'class_sig_item_eoi Grammar.Entry.e),
   None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj
           (class_sig_item : 'class_sig_item Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'class_sig_item) (loc : Ploc.t) ->
          (x : 'class_sig_item_eoi))]];
   Grammar.Entry.obj
     (class_str_item_eoi : 'class_str_item_eoi Grammar.Entry.e),
   None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj
           (class_str_item : 'class_str_item Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'class_str_item) (loc : Ploc.t) ->
          (x : 'class_str_item_eoi))]];
   Grammar.Entry.obj (with_constr_eoi : 'with_constr_eoi Grammar.Entry.e),
   None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (with_constr : 'with_constr Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'with_constr) (loc : Ploc.t) -> (x : 'with_constr_eoi))]];
   Grammar.Entry.obj (poly_variant_eoi : 'poly_variant_eoi Grammar.Entry.e),
   None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (poly_variant : 'poly_variant Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'poly_variant) (loc : Ploc.t) ->
          (x : 'poly_variant_eoi))]];
   Grammar.Entry.obj (type_decl_eoi : 'type_decl_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Snterm
        (Grammar.Entry.obj (type_decl : 'type_decl Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (x : 'type_decl) (loc : Ploc.t) -> (x : 'type_decl_eoi))]]];
List.iter (fun (q, f) -> Quotation.add q (f q))
  ["sig_item", apply_entry sig_item_eoi; "str_item", apply_entry str_item_eoi;
   "ctyp", apply_entry ctyp_eoi; "patt", apply_entry patt_eoi;
   "expr", apply_entry expr_eoi; "module_type", apply_entry module_type_eoi;
   "module_expr", apply_entry module_expr_eoi;
   "class_type", apply_entry class_type_eoi;
   "class_expr", apply_entry class_expr_eoi;
   "class_sig_item", apply_entry class_sig_item_eoi;
   "class_str_item", apply_entry class_str_item_eoi;
   "with_constr", apply_entry with_constr_eoi;
   "poly_variant", apply_entry poly_variant_eoi;
   "type_decl", apply_entry type_decl_eoi];;

let expr_eoi = Grammar.Entry.create Pcaml.gram "expr_eoi" in
Grammar.extend
  [Grammar.Entry.obj (expr_eoi : 'expr_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT_LOC", ""); Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (a : string) (loc : Ploc.t) ->
          (let loc = Ploc.make_unlined (0, 0) in
           if !(Pcaml.strict_mode) then
             let a =
               let i = String.index a ':' in
               let i = String.index_from a (i + 1) ':' in
               let a = String.sub a (i + 1) (String.length a - i - 1) in
               Grammar.Entry.parse Pcaml.expr_eoi (Stream.of_string a)
             in
             MLast.ExApp
               (loc,
                MLast.ExAcc
                  (loc, MLast.ExUid (loc, "Ploc"),
                   MLast.ExUid (loc, "VaAnt")),
                MLast.ExAnt (loc, a))
           else
             MLast.ExApp
               (loc, MLast.ExLid (loc, "failwith"),
                MLast.ExStr (loc, "antiquot")) :
           'expr_eoi));
     [Gramext.Snterm
        (Grammar.Entry.obj (Pcaml.expr : 'Pcaml__expr Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (e : 'Pcaml__expr) (loc : Ploc.t) ->
          (let loc = Ploc.make_unlined (0, 0) in
           if !(Pcaml.strict_mode) then
             MLast.ExApp
               (loc,
                MLast.ExAcc
                  (loc, MLast.ExUid (loc, "Ploc"),
                   MLast.ExUid (loc, "VaVal")),
                MLast.ExAnt (loc, e))
           else MLast.ExAnt (loc, e) :
           'expr_eoi))]]];
let expr s =
  Ploc.call_with Plexer.force_antiquot_loc true (Grammar.Entry.parse expr_eoi)
    (Stream.of_string s)
in
let patt_eoi = Grammar.Entry.create Pcaml.gram "patt_eoi" in
Grammar.extend
  [Grammar.Entry.obj (patt_eoi : 'patt_eoi Grammar.Entry.e), None,
   [None, None,
    [[Gramext.Stoken ("ANTIQUOT_LOC", ""); Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (a : string) (loc : Ploc.t) ->
          (let loc = Ploc.make_unlined (0, 0) in
           if !(Pcaml.strict_mode) then
             let a =
               let i = String.index a ':' in
               let i = String.index_from a (i + 1) ':' in
               let a = String.sub a (i + 1) (String.length a - i - 1) in
               Grammar.Entry.parse Pcaml.patt_eoi (Stream.of_string a)
             in
             MLast.PaApp
               (loc,
                MLast.PaAcc
                  (loc, MLast.PaUid (loc, "Ploc"),
                   MLast.PaUid (loc, "VaAnt")),
                MLast.PaAnt (loc, a))
           else MLast.PaAny loc :
           'patt_eoi));
     [Gramext.Snterm
        (Grammar.Entry.obj (Pcaml.patt : 'Pcaml__patt Grammar.Entry.e));
      Gramext.Stoken ("EOI", "")],
     Gramext.action
       (fun _ (p : 'Pcaml__patt) (loc : Ploc.t) ->
          (let loc = Ploc.make_unlined (0, 0) in
           if !(Pcaml.strict_mode) then
             MLast.PaApp
               (loc,
                MLast.PaAcc
                  (loc, MLast.PaUid (loc, "Ploc"),
                   MLast.PaUid (loc, "VaVal")),
                MLast.PaAnt (loc, p))
           else MLast.PaAnt (loc, p) :
           'patt_eoi))]]];
let patt s =
  Ploc.call_with Plexer.force_antiquot_loc true (Grammar.Entry.parse patt_eoi)
    (Stream.of_string s)
in
Quotation.add "vala" (Quotation.ExAst (expr, patt));;
