(* camlp5r *)
(* q_MLast.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "pa_extend_m.cmo" *)
(* #load "q_MLast.cmo" *)
(* #load "pa_macro.cmo" *)

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

let functor_parameter = Grammar.Entry.create gram "functor_parameter";;
let module_type = Grammar.Entry.create gram "module_type";;
let extended_longident = Grammar.Entry.create gram "extended_longident";;
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
let type_extension = Grammar.Entry.create gram "type_extension";;
let extension_constructor =
  Grammar.Entry.create gram "extension_constructor"
;;
let match_case = Grammar.Entry.create gram "match_case";;
let constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration"
;;
let label_declaration = Grammar.Entry.create gram "label_declaration";;

let with_constr = Grammar.Entry.create gram "with_constr";;
let poly_variant = Grammar.Entry.create gram "poly_variant";;
let attribute_body = Grammar.Entry.create gram "attribute_body";;
let ctyp_ident = Grammar.Entry.create gram "ctyp_ident";;

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

let mklabdecl _ i mf t attrs =
  Qast.Tuple [Qast.Loc; Qast.Str i; Qast.Bool mf; t; attrs]
;;
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

let check_let_exception_f strm =
  match Stream.npeek 2 strm with
    ["", "let"; "", "exception"] -> ()
  | _ -> raise Stream.Failure
;;

let check_let_exception =
  Grammar.Entry.of_parser gram "check_let_exception" check_let_exception_f
;;

let check_let_not_exception_f strm =
  match Stream.npeek 2 strm with
    ["", "let"; "", "exception"] -> raise Stream.Failure
  | ["", "let"; _] -> ()
  | _ -> raise Stream.Failure
;;

let check_let_not_exception =
  Grammar.Entry.of_parser gram "check_let_not_exception"
    check_let_not_exception_f
;;

let stream_peek_nth n strm =
  let rec loop n =
    function
      [] -> None
    | [x] -> if n == 1 then Some x else None
    | _ :: l -> loop (n - 1) l
  in
  loop n (Stream.npeek n strm)
;;

(* returns True if the stream is a type-decl, and not an extension.
   returns False if the stream is an extension and not a type-decl.
   Since a type-decl might not have an "=" (if it's a list of decls)
   the default is "type-decl".
*)
let word_keywordp s =
  let rec wrec (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('a'..'z' | 'A'..'Z' | '_' | '0'..'9') ->
        Stream.junk strm__; let strm = strm__ in wrec strm
    | _ -> let strm = strm__ in Stream.empty strm; true
  in
  let check (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('a'..'z' | 'A'..'Z' | '_') ->
        Stream.junk strm__; let strm = strm__ in wrec strm
    | _ -> false
  in
  try check (Stream.of_string s) with Stream.Failure | Stream.Error _ -> false
;;

let is_type_decl_not_extension strm =
  let rec wrec n =
    match stream_peek_nth n strm with
      None -> assert false
    | Some ("", "=" | "", ";" | "", ";;") -> true
    | Some ("", s) when word_keywordp s -> true
    | Some ("EOI", "") -> true
    | Some ("", "+=") -> false
    | Some
        ("", _ | "UIDENT", _ | "LIDENT", _ | "GIDENT", _ | "ANTIQUOT", _) ->
        wrec (n + 1)
    | Some (a, b) ->
        raise
          (Stream.Error
             (Printf.sprintf
                "unexpected tokens in a type-decl/extension: (\"%s\",\"%s\")"
                a b))
  in
  wrec 1
;;

let check_type_decl_f strm =
  if is_type_decl_not_extension strm then () else raise Stream.Failure
;;

let check_type_decl =
  Grammar.Entry.of_parser gram "check_type_decl" check_type_decl_f
;;

let check_type_extension_f strm =
  if not (is_type_decl_not_extension strm) then () else raise Stream.Failure
;;

let check_type_extension =
  Grammar.Entry.of_parser gram "check_type_extension" check_type_extension_f
;;

let stream_npeek n (strm : (string * string) Stream.t) = Stream.npeek n strm;;
let prefix_eq s0 s1 =
  let s0len = String.length s0 in
  s0len <= String.length s1 && s0 = String.sub s1 0 s0len
;;

let check_dot_uid_f strm =
  match stream_npeek 5 strm with
    ("", ".") :: ("UIDENT", _) :: _ -> ()
  | ("", ".") :: ("ANTIQUOT", qs) :: _
    when
      prefix_eq "longid:" qs || prefix_eq "_longid:" qs ||
      prefix_eq "uid:" qs || prefix_eq "_uid:" qs ->
      ()
  | ("", ".") :: ("", "$") ::
    ("LIDENT", ("uid" | "_uid" | "longid" | "_longid")) :: ("", ":") ::
    ("LIDENT", _) :: _ ->
      ()
  | _ -> raise Stream.Failure
;;

let check_dot_uid =
  Grammar.Entry.of_parser gram "check_dot_uid" check_dot_uid_f
;;

(* -- begin copy from pa_r to q_MLast -- *)

Grammar.safe_extend
  (let _ = (sig_item : 'sig_item Grammar.Entry.e)
   and _ = (str_item : 'str_item Grammar.Entry.e)
   and _ = (ctyp : 'ctyp Grammar.Entry.e)
   and _ = (patt : 'patt Grammar.Entry.e)
   and _ = (expr : 'expr Grammar.Entry.e)
   and _ = (functor_parameter : 'functor_parameter Grammar.Entry.e)
   and _ = (module_type : 'module_type Grammar.Entry.e)
   and _ = (module_expr : 'module_expr Grammar.Entry.e)
   and _ = (extended_longident : 'extended_longident Grammar.Entry.e)
   and _ = (signature : 'signature Grammar.Entry.e)
   and _ = (structure : 'structure Grammar.Entry.e)
   and _ = (class_type : 'class_type Grammar.Entry.e)
   and _ = (class_expr : 'class_expr Grammar.Entry.e)
   and _ = (class_sig_item : 'class_sig_item Grammar.Entry.e)
   and _ = (class_str_item : 'class_str_item Grammar.Entry.e)
   and _ = (let_binding : 'let_binding Grammar.Entry.e)
   and _ = (type_decl : 'type_decl Grammar.Entry.e)
   and _ = (type_extension : 'type_extension Grammar.Entry.e)
   and _ = (extension_constructor : 'extension_constructor Grammar.Entry.e)
   and _ =
     (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
   and _ = (label_declaration : 'label_declaration Grammar.Entry.e)
   and _ = (match_case : 'match_case Grammar.Entry.e)
   and _ = (ipatt : 'ipatt Grammar.Entry.e)
   and _ = (with_constr : 'with_constr Grammar.Entry.e)
   and _ = (poly_variant : 'poly_variant Grammar.Entry.e)
   and _ = (attribute_body : 'attribute_body Grammar.Entry.e)
   and _ = (check_type_decl : 'check_type_decl Grammar.Entry.e)
   and _ = (check_type_extension : 'check_type_extension Grammar.Entry.e)
   and _ = (check_dot_uid : 'check_dot_uid Grammar.Entry.e)
   and _ = (ctyp_ident : 'ctyp_ident Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry sig_item) s
   in
   let attribute_id : 'attribute_id Grammar.Entry.e =
     grammar_entry_create "attribute_id"
   and attribute_structure : 'attribute_structure Grammar.Entry.e =
     grammar_entry_create "attribute_structure"
   and attribute_signature : 'attribute_signature Grammar.Entry.e =
     grammar_entry_create "attribute_signature"
   and floating_attribute : 'floating_attribute Grammar.Entry.e =
     grammar_entry_create "floating_attribute"
   and item_attribute : 'item_attribute Grammar.Entry.e =
     grammar_entry_create "item_attribute"
   and alg_attribute : 'alg_attribute Grammar.Entry.e =
     grammar_entry_create "alg_attribute"
   and item_attributes : 'item_attributes Grammar.Entry.e =
     grammar_entry_create "item_attributes"
   and alg_attributes : 'alg_attributes Grammar.Entry.e =
     grammar_entry_create "alg_attributes"
   and item_extension : 'item_extension Grammar.Entry.e =
     grammar_entry_create "item_extension"
   and alg_extension : 'alg_extension Grammar.Entry.e =
     grammar_entry_create "alg_extension"
   and rebind_exn : 'rebind_exn Grammar.Entry.e =
     grammar_entry_create "rebind_exn"
   and mod_binding : 'mod_binding Grammar.Entry.e =
     grammar_entry_create "mod_binding"
   and mod_fun_binding : 'mod_fun_binding Grammar.Entry.e =
     grammar_entry_create "mod_fun_binding"
   and mod_decl_binding : 'mod_decl_binding Grammar.Entry.e =
     grammar_entry_create "mod_decl_binding"
   and module_declaration : 'module_declaration Grammar.Entry.e =
     grammar_entry_create "module_declaration"
   and uidopt : 'uidopt Grammar.Entry.e = grammar_entry_create "uidopt"
   and closed_case_list : 'closed_case_list Grammar.Entry.e =
     grammar_entry_create "closed_case_list"
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
   and mod_ident_patt : 'mod_ident_patt Grammar.Entry.e =
     (* why is this called what it's called? *)
     grammar_entry_create "mod_ident_patt"
   and type_patt : 'type_patt Grammar.Entry.e =
     grammar_entry_create "type_patt"
   and constrain : 'constrain Grammar.Entry.e =
     grammar_entry_create "constrain"
   and type_parameter : 'type_parameter Grammar.Entry.e =
     grammar_entry_create "type_parameter"
   and simple_type_parameter : 'simple_type_parameter Grammar.Entry.e =
     grammar_entry_create "simple_type_parameter"
   and cons_ident : 'cons_ident Grammar.Entry.e =
     grammar_entry_create "cons_ident"
   and constructor_declaration_sans_alg_attrs : 'constructor_declaration_sans_alg_attrs Grammar.Entry.e =
     grammar_entry_create "constructor_declaration_sans_alg_attrs"
   and ident : 'ident Grammar.Entry.e = grammar_entry_create "ident"
   and mod_ident : 'mod_ident Grammar.Entry.e =
     grammar_entry_create "mod_ident"
   and direction_flag : 'direction_flag Grammar.Entry.e =
     grammar_entry_create "direction_flag"
   and typevar : 'typevar Grammar.Entry.e = grammar_entry_create "typevar"
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
   and a_ti : 'a_ti Grammar.Entry.e =
     (* -- end copy from pa_r to q_MLast -- *)
     grammar_entry_create "a_ti"
   and a_tic : 'a_tic Grammar.Entry.e = grammar_entry_create "a_tic"
   and a_qi : 'a_qi Grammar.Entry.e = grammar_entry_create "a_qi"
   and a_qic : 'a_qic Grammar.Entry.e = grammar_entry_create "a_qic" in
   [Grammar.extension (attribute_id : 'attribute_id Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (i : string) (loc : Ploc.t) -> (i : 'e__1)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (i : string) (loc : Ploc.t) -> (i : 'e__1)))])
                (Grammar.s_token ("", ".")) false),
           (fun (l : 'e__1 list) (loc : Ploc.t) ->
              (Qast.VaVal (Qast.Str (String.concat "." l)) :
               'attribute_id)))]];
    Grammar.extension
      (attribute_structure : 'attribute_structure Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (str_item :
                                            'str_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                      (s : 'e__2)))])),
                       (fun (a : 'e__2 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__3)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_structure")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_structure", loc, a) : 'e__3)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "structure")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("structure", loc, a)) :
                           'e__3)))])),
           (fun (st : 'e__3) (loc : Ploc.t) ->
              (st : 'attribute_structure)))]];
    Grammar.extension
      (attribute_signature : 'attribute_signature Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (sig_item :
                                            'sig_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                      (s : 'e__4)))])),
                       (fun (a : 'e__4 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__5)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_signature")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_signature", loc, a) : 'e__5)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "signature")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("signature", loc, a)) :
                           'e__5)))])),
           (fun (st : 'e__5) (loc : Ploc.t) ->
              (st : 'attribute_signature)))]];
    Grammar.extension (attribute_body : 'attribute_body Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (attribute_id :
                                         'attribute_id Grammar.Entry.e)),
                                   (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__13)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token
                                        ("ANTIQUOT", "_attrid")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_attrid", loc, a) :
                                       'e__13)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "attrid")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("attrid", loc, a)) :
                                       'e__13)))])))
                      (Grammar.s_token ("", "?")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (patt : 'patt Grammar.Entry.e)),
                             (fun (a : 'patt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__14)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_patt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_patt", loc, a) : 'e__14)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "patt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("patt", loc, a)) :
                                 'e__14)))])))
                (Grammar.s_token ("", "when")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
                       (fun (a : 'expr) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__15)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_expr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_expr", loc, a) : 'e__15)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "expr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("expr", loc, a)) :
                           'e__15)))])),
           (fun (e : 'e__15) _ (p : 'e__14) _ (id : 'e__13) (loc : Ploc.t) ->
              (Qast.Tuple
                 [id;
                  Qast.Node ("PaAttr", [Qast.Loc; p; Qast.Option (Some e)])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (attribute_id :
                                   'attribute_id Grammar.Entry.e)),
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__11)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__11)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__11)))])))
                (Grammar.s_token ("", "?")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
                       (fun (a : 'patt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__12)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_patt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_patt", loc, a) : 'e__12)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "patt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("patt", loc, a)) :
                           'e__12)))])),
           (fun (p : 'e__12) _ (id : 'e__11) (loc : Ploc.t) ->
              (Qast.Tuple
                 [id; Qast.Node ("PaAttr", [Qast.Loc; p; Qast.Option None])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (attribute_id :
                                   'attribute_id Grammar.Entry.e)),
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__9)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__9)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__9)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
                       (fun (a : 'ctyp) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__10)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_type")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_type", loc, a) : 'e__10)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "type")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("type", loc, a)) :
                           'e__10)))])),
           (fun (ty : 'e__10) _ (id : 'e__9) (loc : Ploc.t) ->
              (Qast.Tuple [id; Qast.Node ("TyAttr", [Qast.Loc; ty])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (attribute_id :
                                   'attribute_id Grammar.Entry.e)),
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__8)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__8)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__8)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm
                (attribute_signature : 'attribute_signature Grammar.Entry.e)),
           (fun (si : 'attribute_signature) _ (id : 'e__8) (loc : Ploc.t) ->
              (Qast.Tuple [id; Qast.Node ("SiAttr", [Qast.Loc; si])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (attribute_id : 'attribute_id Grammar.Entry.e)),
                       (fun (a : 'attribute_id) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__7)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_attrid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_attrid", loc, a) : 'e__7)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "attrid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                           'e__7)))])),
           (fun (id : 'e__7) (loc : Ploc.t) ->
              (Qast.Tuple
                 [id;
                  Qast.Node
                    ("StAttr", [Qast.Loc; Qast.VaVal (Qast.List [])])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_id :
                                'attribute_id Grammar.Entry.e)),
                          (fun (a : 'attribute_id) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__6)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attrid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attrid", loc, a) : 'e__6)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attrid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                              'e__6)))])))
             (Grammar.s_nterm
                (attribute_structure : 'attribute_structure Grammar.Entry.e)),
           (fun (st : 'attribute_structure) (id : 'e__6) (loc : Ploc.t) ->
              (Qast.Tuple [id; Qast.Node ("StAttr", [Qast.Loc; st])] :
               'attribute_body)))]];
    Grammar.extension
      (floating_attribute : 'floating_attribute Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[@@@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__16)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__16)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__16)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__16) _ (loc : Ploc.t) ->
              (attr : 'floating_attribute)))]];
    Grammar.extension (item_attribute : 'item_attribute Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[@@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__17)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__17)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__17)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__17) _ (loc : Ploc.t) ->
              (attr : 'item_attribute)))]];
    Grammar.extension (alg_attribute : 'alg_attribute Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__18)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__18)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__18)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__18) _ (loc : Ploc.t) ->
              (attr : 'alg_attribute)))]];
    Grammar.extension (item_attributes : 'item_attributes Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__19)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_itemattrs")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_itemattrs", loc, a) : 'e__19)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "itemattrs")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("itemattrs", loc, a)) :
                           'e__19)))])),
           (fun (l : 'e__19) (loc : Ploc.t) -> (l : 'item_attributes)))]];
    Grammar.extension (alg_attributes : 'alg_attributes Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (alg_attribute :
                                'alg_attribute Grammar.Entry.e))),
                       (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__20)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_algattrs")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_algattrs", loc, a) : 'e__20)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "algattrs")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("algattrs", loc, a)) :
                           'e__20)))])),
           (fun (l : 'e__20) (loc : Ploc.t) -> (l : 'alg_attributes)))]];
    Grammar.extension (item_extension : 'item_extension Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[%%")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__21)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_extension")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_extension", loc, a) : 'e__21)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "extension")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("extension", loc, a)) :
                              'e__21)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (e : 'e__21) _ (loc : Ploc.t) -> (e : 'item_extension)))]];
    Grammar.extension (alg_extension : 'alg_extension Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[%")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__22)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_extension")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_extension", loc, a) : 'e__22)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "extension")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("extension", loc, a)) :
                              'e__22)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (e : 'e__22) _ (loc : Ploc.t) -> (e : 'alg_extension)))]];
    Grammar.extension (functor_parameter : 'functor_parameter Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Option None : 'functor_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (uidopt : 'uidopt Grammar.Entry.e)),
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__23)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__23)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__23)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'module_type) _ (i : 'e__23) _ (loc : Ploc.t) ->
              (Qast.Option (Some (Qast.Tuple [i; t])) :
               'functor_parameter)))]];
    Grammar.extension (module_expr : 'module_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "functor")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (functor_parameter :
                                   'functor_parameter Grammar.Entry.e)),
                             (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__24)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_fp")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_fp", loc, a) : 'e__24)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "fp")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                                 'e__24)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "_functor_parameter")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_functor_parameter", loc, a) :
                                 'e__24)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "functor_parameter")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.VaAnt
                                      ("functor_parameter", loc, a)) :
                                 'e__24)))])))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (me : 'module_expr) _ (arg : 'e__24) _ (loc : Ploc.t) ->
              (Qast.Node ("MeFun", [Qast.Loc; arg; me]) : 'module_expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__25)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__25)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__25)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__25) _ (e : 'module_expr) (loc : Ploc.t) ->
              (Qast.Node ("MeAtt", [Qast.Loc; e; attr]) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_cut
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "struct")))
                   (Grammar.s_nterm
                      (structure : 'structure Grammar.Entry.e))))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'structure) _ (loc : Ploc.t) ->
              (Qast.Node ("MeStr", [Qast.Loc; st]) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (me2 : 'module_expr) (me1 : 'module_expr) (loc : Ploc.t) ->
              (Qast.Node ("MeApp", [Qast.Loc; me1; me2]) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (me2 : 'module_expr) _ (me1 : 'module_expr) (loc : Ploc.t) ->
              (Qast.Node ("MeAcc", [Qast.Loc; me1; me2]) : 'module_expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("MeExten", [Qast.Loc; e]) : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (me : 'module_expr) _ (loc : Ploc.t) ->
              (me : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (mt : 'module_type) _ (me : 'module_expr) _
                (loc : Ploc.t) ->
              (Qast.Node ("MeTyc", [Qast.Loc; me; mt]) : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "value")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("MeUnp",
                  [Qast.Loc; e; Qast.Option None; Qast.Option None]) :
               'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "(")))
                         (Grammar.s_token ("", "value")))
                      (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (mt : 'module_type) _ (e : 'expr) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("MeUnp",
                  [Qast.Loc; e; Qast.Option (Some mt); Qast.Option None]) :
               'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "(")))
                               (Grammar.s_token ("", "value")))
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm
                         (module_type : 'module_type Grammar.Entry.e)))
                   (Grammar.s_token ("", ":>")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (mt2 : 'module_type) _ (mt1 : 'module_type) _ (e : 'expr) _
                _ (loc : Ploc.t) ->
              (Qast.Node
                 ("MeUnp",
                  [Qast.Loc; e; Qast.Option (Some mt1);
                   Qast.Option (Some mt2)]) :
               'module_expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__26)))])),
           (fun (i : 'e__26) (loc : Ploc.t) ->
              (Qast.Node ("MeUid", [Qast.Loc; i]) : 'module_expr)))]];
    Grammar.extension (structure : 'structure Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (str_item :
                                            'str_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                      (s : 'e__27)))])),
                       (fun (a : 'e__27 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__28)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__28)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__28)))])),
           (fun (st : 'e__28) (loc : Ploc.t) -> (st : 'structure)))]];
    Grammar.extension
      (extension_constructor : 'extension_constructor Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (Qast.Node
                 ("EcTuple", [ci; Qast.VaVal (Qast.List []); alg_attrs]) :
               'extension_constructor)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (cons_ident : 'cons_ident Grammar.Entry.e)))
                   (Grammar.s_token ("", "of")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ctyp : 'ctyp Grammar.Entry.e))
                               (Grammar.s_token ("", "and")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__29)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__29)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__29)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (tl : 'e__29) _
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (Qast.Node ("EcTuple", [ci; tl; alg_attrs]) :
               'extension_constructor)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (cons_ident : 'cons_ident Grammar.Entry.e)))
                (Grammar.s_nterm (rebind_exn : 'rebind_exn Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (b : 'rebind_exn)
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (Qast.Node ("EcRebind", [ci; b; alg_attrs]) :
               'extension_constructor)))]];
    Grammar.extension (str_item : 'str_item Grammar.Entry.e) None
      [Some "top", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__30)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__30)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__30)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__30) _ (si : 'str_item) (loc : Ploc.t) ->
              (Qast.Node ("StAtt", [Qast.Loc; si; attr]) : 'str_item)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (Qast.Node ("StExten", [Qast.Loc; e]) : 'str_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (Qast.Node ("StFlAtt", [Qast.Loc; attr]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("StExp", [Qast.Loc; e; attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("STRING", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__47)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_str")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_str", loc, a) : 'e__47)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "str")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                              'e__47)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (str_item :
                                         'str_item Grammar.Entry.e)),
                                   (fun (si : 'str_item) (loc : Ploc.t) ->
                                      (Qast.Tuple [si; Qast.Loc] :
                                       'e__48)))])),
                       (fun (a : 'e__48 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__49)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__49)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__49)))])),
           (fun (sil : 'e__49) (s : 'e__47) _ (loc : Ploc.t) ->
              (Qast.Node ("StUse", [Qast.Loc; s; sil]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__45)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__45)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__45)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__45)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__45)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
                       (fun (a : 'expr option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__46)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__46)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__46)))])),
           (fun (dp : 'e__46) (n : 'e__45) _ (loc : Ploc.t) ->
              (Qast.Node ("StDir", [Qast.Loc; n; dp]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "value")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "rec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__43)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__43)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__43)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__43)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__43)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (let_binding : 'let_binding Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'let_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__44)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__44)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__44)))])),
           (fun (l : 'e__44) (r : 'e__43) _ (loc : Ploc.t) ->
              (Qast.Node ("StVal", [Qast.Loc; r; l]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
                (Grammar.s_nterm
                   (check_type_extension :
                    'check_type_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (type_extension : 'type_extension Grammar.Entry.e)),
           (fun (te : 'type_extension) _ _ (loc : Ploc.t) ->
              (Qast.Node ("StTypExten", [Qast.Loc; te]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_nterm
                      (check_type_decl : 'check_type_decl Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "nonrec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__41)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__41)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__41)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__41)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__41)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (type_decl : 'type_decl Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'type_decl list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__42)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__42)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__42)))])),
           (fun (tdl : 'e__42) (nrfl : 'e__41) _ _ (loc : Ploc.t) ->
              (Qast.Node ("StTyp", [Qast.Loc; nrfl; tdl]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "open")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_flag (Grammar.s_token ("", "!"))),
                             (fun (a : bool) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Bool a) : 'e__40)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_!")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_!", loc, a) : 'e__40)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "!")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                 'e__40)))])))
                (Grammar.s_nterm
                   (module_expr : 'module_expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (me : 'module_expr) (ovf : 'e__40)
                _ (loc : Ploc.t) ->
              (Qast.Node ("StOpn", [Qast.Loc; ovf; me; attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_token ("", "type")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (ident : 'ident Grammar.Entry.e)),
                          (fun (a : 'ident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__39)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__39)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__39)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (i : 'e__39) _ _ (loc : Ploc.t) ->
              (Qast.Node ("StMtyAbs", [Qast.Loc; i; attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (ident : 'ident Grammar.Entry.e)),
                                (fun (a : 'ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__38)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__38)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__38)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (mt : 'module_type) _ (i : 'e__38)
                _ _ (loc : Ploc.t) ->
              (Qast.Node ("StMty", [Qast.Loc; i; mt; attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "module")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "rec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__36)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__36)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__36)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__36)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__36)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (mod_binding : 'mod_binding Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'mod_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__37)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__37)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__37)))])),
           (fun (l : 'e__37) (r : 'e__36) _ (loc : Ploc.t) ->
              (Qast.Node ("StMod", [Qast.Loc; r; l]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "include")))
                (Grammar.s_nterm
                   (module_expr : 'module_expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (me : 'module_expr) _
                (loc : Ploc.t) ->
              (Qast.Node ("StInc", [Qast.Loc; me; attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "external")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) : 'e__34)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__34)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__34)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__34)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__34)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_token ("STRING", ""))),
                          (fun (a : string list) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.List
                                   (List.map (fun a -> Qast.Str a) a)) :
                              'e__35)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__35)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__35)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (pd : 'e__35) _ (t : 'ctyp) _
                (i : 'e__34) _ (loc : Ploc.t) ->
              (Qast.Node ("StExt", [Qast.Loc; i; t; pd; attrs]) :
               'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "exception")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (extension_constructor :
                                'extension_constructor Grammar.Entry.e)),
                          (fun (a : 'extension_constructor) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__33)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_excon")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_excon", loc, a) : 'e__33)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "excon")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("excon", loc, a)) :
                              'e__33)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (item_attrs : 'item_attributes) (ec : 'e__33) _
                (loc : Ploc.t) ->
              (Qast.Node ("StExc", [Qast.Loc; ec; item_attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (str_item :
                                               'str_item Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                         (s : 'e__31)))])),
                          (fun (a : 'e__31 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__32)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__32)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__32)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__32) _ (loc : Ploc.t) ->
              (Qast.Node ("StDcl", [Qast.Loc; st]) : 'str_item)))]];
    Grammar.extension (rebind_exn : 'rebind_exn Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (mod_ident : 'mod_ident Grammar.Entry.e)),
                       (fun (a : 'mod_ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__50)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__50)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__50)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__50)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__50)))])),
           (fun (a : 'e__50) _ (loc : Ploc.t) -> (a : 'rebind_exn)))]];
    Grammar.extension (mod_binding : 'mod_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (uidopt : 'uidopt Grammar.Entry.e)),
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__51)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__51)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__51)))])))
                (Grammar.s_nterm
                   (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (me : 'mod_fun_binding)
                (i : 'e__51) (loc : Ploc.t) ->
              (Qast.Tuple [i; me; attrs] : 'mod_binding)))]];
    Grammar.extension (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)
      None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (loc : Ploc.t) ->
              (me : 'mod_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm
                      (module_type : 'module_type Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (mt : 'module_type) _ (loc : Ploc.t) ->
              (Qast.Node ("MeTyc", [Qast.Loc; me; mt]) : 'mod_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (functor_parameter :
                                'functor_parameter Grammar.Entry.e)),
                          (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__52)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_fp")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_fp", loc, a) : 'e__52)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "fp")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                              'e__52)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "_functor_parameter")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_functor_parameter", loc, a) :
                              'e__52)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "functor_parameter")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.VaAnt ("functor_parameter", loc, a)) :
                              'e__52)))])))
             Grammar.s_self,
           (fun (mb : 'mod_fun_binding) (arg : 'e__52) (loc : Ploc.t) ->
              (Qast.Node ("MeFun", [Qast.Loc; arg; mb]) :
               'mod_fun_binding)))]];
    Grammar.extension (module_type : 'module_type Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "functor")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (functor_parameter :
                                   'functor_parameter Grammar.Entry.e)),
                             (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__53)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_fp")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_fp", loc, a) : 'e__53)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "fp")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                                 'e__53)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "_functor_parameter")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_functor_parameter", loc, a) :
                                 'e__53)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "functor_parameter")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.VaAnt
                                      ("functor_parameter", loc, a)) :
                                 'e__53)))])))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (mt : 'module_type) _ (arg : 'e__53) _ (loc : Ploc.t) ->
              (Qast.Node ("MtFun", [Qast.Loc; arg; mt]) : 'module_type)))];
       Some "->", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (mt2 : 'module_type) _ (mt1 : 'module_type) (loc : Ploc.t) ->
              (Qast.Node
                 ("MtFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.Option
                        (Some
                           (Qast.Tuple
                              [Qast.VaVal (Qast.Option None); mt1])));
                   mt2]) :
               'module_type)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__54)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__54)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__54)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__54) _ (e : 'module_type) (loc : Ploc.t) ->
              (Qast.Node ("MtAtt", [Qast.Loc; e; attr]) : 'module_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (with_constr : 'with_constr Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'with_constr list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__55)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__55)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__55)))])),
           (fun (wcl : 'e__55) _ (mt : 'module_type) (loc : Ploc.t) ->
              (Qast.Node ("MtWit", [Qast.Loc; mt; wcl]) : 'module_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_token ("", "type")))
                (Grammar.s_token ("", "of")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ _ _ (loc : Ploc.t) ->
              (Qast.Node ("MtTyo", [Qast.Loc; me]) : 'module_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_cut
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "sig")))
                   (Grammar.s_nterm
                      (signature : 'signature Grammar.Entry.e))))
             (Grammar.s_token ("", "end")),
           (fun _ (sg : 'signature) _ (loc : Ploc.t) ->
              (Qast.Node ("MtSig", [Qast.Loc; sg]) : 'module_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (mt : 'module_type) _ (loc : Ploc.t) ->
              (mt : 'module_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__58)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__58)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__58)))])),
           (fun (i : 'e__58) _ (loc : Ploc.t) ->
              (Qast.Node ("MtQuo", [Qast.Loc; i]) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("MtExten", [Qast.Loc; e]) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__57)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__57)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__57)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__57)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__57)))])),
           (fun (i : 'e__57) (loc : Ploc.t) ->
              (Qast.Node ("MtLid", [Qast.Loc; i]) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (extended_longident : 'extended_longident Grammar.Entry.e)),
           (fun (li : 'extended_longident) (loc : Ploc.t) ->
              (Qast.Node ("MtLong", [Qast.Loc; li]) : 'module_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__56)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__56)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__56)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__56)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__56)))])),
           (fun (i : 'e__56) _ (li : 'extended_longident) (loc : Ploc.t) ->
              (Qast.Node ("MtLongLid", [Qast.Loc; li; i]) : 'module_type)))]];
    Grammar.extension (signature : 'signature Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (sig_item :
                                            'sig_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                      (s : 'e__59)))])),
                       (fun (a : 'e__59 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__60)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__60)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__60)))])),
           (fun (st : 'e__60) (loc : Ploc.t) -> (st : 'signature)))]];
    Grammar.extension (sig_item : 'sig_item Grammar.Entry.e) None
      [Some "top", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__61)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__61)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__61)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__61) _ (si : 'sig_item) (loc : Ploc.t) ->
              (Qast.Node ("SgAtt", [Qast.Loc; si; attr]) : 'sig_item)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (Qast.Node ("SgExten", [Qast.Loc; e]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (Qast.Node ("SgFlAtt", [Qast.Loc; attr]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("STRING", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__76)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_str")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_str", loc, a) : 'e__76)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "str")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                              'e__76)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (sig_item :
                                         'sig_item Grammar.Entry.e)),
                                   (fun (si : 'sig_item) (loc : Ploc.t) ->
                                      (Qast.Tuple [si; Qast.Loc] :
                                       'e__77)))])),
                       (fun (a : 'e__77 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__78)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__78)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__78)))])),
           (fun (sil : 'e__78) (s : 'e__76) _ (loc : Ploc.t) ->
              (Qast.Node ("SgUse", [Qast.Loc; s; sil]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__74)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__74)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__74)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__74)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__74)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
                       (fun (a : 'expr option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__75)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__75)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__75)))])),
           (fun (dp : 'e__75) (n : 'e__74) _ (loc : Ploc.t) ->
              (Qast.Node ("SgDir", [Qast.Loc; n; dp]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "value")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__73)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__73)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__73)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__73)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__73)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (i : 'e__73) _
                (loc : Ploc.t) ->
              (Qast.Node ("SgVal", [Qast.Loc; i; t; attrs]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
                (Grammar.s_nterm
                   (check_type_extension :
                    'check_type_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (type_extension : 'type_extension Grammar.Entry.e)),
           (fun (te : 'type_extension) _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgTypExten", [Qast.Loc; te]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
                (Grammar.s_nterm
                   (check_type_decl : 'check_type_decl Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (type_decl : 'type_decl Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'type_decl list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__72)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__72)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__72)))])),
           (fun (tdl : 'e__72) _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgTyp", [Qast.Loc; Qast.VaVal (Qast.Bool false); tdl]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "open")))
                (Grammar.s_nterm
                   (extended_longident :
                    'extended_longident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (i : 'extended_longident) _
                (loc : Ploc.t) ->
              (Qast.Node ("SgOpn", [Qast.Loc; i; attrs]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_token ("", "type")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (ident : 'ident Grammar.Entry.e)),
                          (fun (a : 'ident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__71)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__71)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__71)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (i : 'e__71) _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgMtyAbs", [Qast.Loc; i; attrs]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (ident : 'ident Grammar.Entry.e)),
                                (fun (a : 'ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__70)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__70)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__70)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (mt : 'module_type) _ (i : 'e__70)
                _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgMty", [Qast.Loc; i; mt; attrs]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_token ("", "alias")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("UIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__68)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__68)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__68)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uid", loc, a) : 'e__68)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                    'e__68)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (mod_ident : 'mod_ident Grammar.Entry.e)),
                          (fun (a : 'mod_ident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__69)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__69)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__69)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__69)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__69)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (li : 'e__69) _ (i : 'e__68) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("SgMtyAlias", [Qast.Loc; i; li; attrs]) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "module")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "rec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__66)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__66)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__66)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__66)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__66)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (mod_decl_binding :
                                'mod_decl_binding Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'mod_decl_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__67)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__67)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__67)))])),
           (fun (l : 'e__67) (rf : 'e__66) _ (loc : Ploc.t) ->
              (Qast.Node ("SgMod", [Qast.Loc; rf; l]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "include")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (mt : 'module_type) _
                (loc : Ploc.t) ->
              (Qast.Node ("SgInc", [Qast.Loc; mt; attrs]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "external")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) : 'e__64)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__64)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__64)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__64)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__64)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_token ("STRING", ""))),
                          (fun (a : string list) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.List
                                   (List.map (fun a -> Qast.Str a) a)) :
                              'e__65)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__65)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__65)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (pd : 'e__65) _ (t : 'ctyp) _
                (i : 'e__64) _ (loc : Ploc.t) ->
              (Qast.Node ("SgExt", [Qast.Loc; i; t; pd; attrs]) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "exception")))
                   (Grammar.s_nterm
                      (constructor_declaration_sans_alg_attrs :
                       'constructor_declaration_sans_alg_attrs
                         Grammar.Entry.e)))
                (Grammar.s_nterm
                   (alg_attributes : 'alg_attributes Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (item_attrs : 'item_attributes) (alg_attrs : 'alg_attributes)
                (ctl : 'constructor_declaration_sans_alg_attrs) _
                (loc : Ploc.t) ->
              (let (_, c, tl, _) =
                 match ctl with
                   Qast.Tuple [xx1; xx2; xx3; xx4] -> xx1, xx2, xx3, xx4
                 | _ -> raise (Match_failure ("q_MLast.ml", 602, 20))
               in
               Qast.Node ("SgExc", [Qast.Loc; c; tl; alg_attrs; item_attrs]) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (sig_item :
                                               'sig_item Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                         (s : 'e__62)))])),
                          (fun (a : 'e__62 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__63)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__63)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__63)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__63) _ (loc : Ploc.t) ->
              (Qast.Node ("SgDcl", [Qast.Loc; st]) : 'sig_item)))]];
    Grammar.extension (mod_decl_binding : 'mod_decl_binding Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (uidopt : 'uidopt Grammar.Entry.e)),
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__79)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__79)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__79)))])))
                (Grammar.s_nterm
                   (module_declaration :
                    'module_declaration Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (mt : 'module_declaration)
                (i : 'e__79) (loc : Ploc.t) ->
              (Qast.Tuple [i; mt; attrs] : 'mod_decl_binding)))]];
    Grammar.extension
      (module_declaration : 'module_declaration Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (functor_parameter :
                                'functor_parameter Grammar.Entry.e)),
                          (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_fp")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_fp", loc, a) : 'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "fp")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                              'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "_functor_parameter")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_functor_parameter", loc, a) :
                              'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "functor_parameter")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.VaAnt ("functor_parameter", loc, a)) :
                              'e__80)))])))
             Grammar.s_self,
           (fun (mt : 'module_declaration) (arg : 'e__80) (loc : Ploc.t) ->
              (Qast.Node ("MtFun", [Qast.Loc; arg; mt]) :
               'module_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (loc : Ploc.t) ->
              (mt : 'module_declaration)))]];
    Grammar.extension (with_constr : 'with_constr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (mod_ident : 'mod_ident Grammar.Entry.e)),
                             (fun (a : 'mod_ident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__87)))])))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (i : 'e__87) _ (loc : Ploc.t) ->
              (Qast.Node ("WcMos", [Qast.Loc; i; me]) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (mod_ident : 'mod_ident Grammar.Entry.e)),
                             (fun (a : 'mod_ident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__86)))])))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (i : 'e__86) _ (loc : Ploc.t) ->
              (Qast.Node ("WcMod", [Qast.Loc; i; me]) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (mod_ident :
                                      'mod_ident Grammar.Entry.e)),
                                (fun (a : 'mod_ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_list", loc, a) : 'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                    'e__84)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list0
                                  (Grammar.s_nterm
                                     (type_parameter :
                                      'type_parameter Grammar.Entry.e))),
                             (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__85)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__85)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__85)))])))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (tpl : 'e__85) (i : 'e__84) _ (loc : Ploc.t) ->
              (Qast.Node ("WcTys", [Qast.Loc; i; tpl; t]) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "type")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (mod_ident :
                                         'mod_ident Grammar.Entry.e)),
                                   (fun (a : 'mod_ident) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_list")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_list", loc, a) :
                                       'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "list")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("list", loc, a)) :
                                       'e__81)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_list0
                                     (Grammar.s_nterm
                                        (type_parameter :
                                         'type_parameter Grammar.Entry.e))),
                                (fun (a : 'type_parameter list)
                                     (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.List a) : 'e__82)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_list", loc, a) : 'e__82)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                    'e__82)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag
                               (Grammar.s_token ("", "private"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__83)))])))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) (pf : 'e__83) _ (tpl : 'e__82) (i : 'e__81) _
                (loc : Ploc.t) ->
              (Qast.Node ("WcTyp", [Qast.Loc; i; tpl; pf; t]) :
               'with_constr)))]];
    Grammar.extension (uidopt : 'uidopt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) -> (Qast.Option None : 'uidopt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__88)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__88)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__88)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__88)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__88)))])),
           (fun (m : 'e__88) (loc : Ploc.t) ->
              (Qast.Option (Some m) : 'uidopt)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e) None
      [Some "top", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "while")))
                         Grammar.s_self)
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sequence : 'sequence Grammar.Entry.e)),
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__98)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__98)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__98)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'e__98) _ _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExWhi", [Qast.Loc; e; seq]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("", "for")))
                                     (Grammar.s_nterm
                                        (patt : 'patt Grammar.Entry.e)))
                                  (Grammar.s_token ("", "=")))
                               Grammar.s_self)
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (direction_flag :
                                            'direction_flag Grammar.Entry.e)),
                                      (fun (a : 'direction_flag)
                                           (loc : Ploc.t) ->
                                         (Qast.VaVal a : 'e__96)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_to")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_to", loc, a) :
                                          'e__96)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "to")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("to", loc, a)) :
                                          'e__96)))])))
                         Grammar.s_self)
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sequence : 'sequence Grammar.Entry.e)),
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__97)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__97)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__97)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'e__97) _ _ (e2 : 'expr) (df : 'e__96) (e1 : 'expr) _
                (i : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("ExFor", [Qast.Loc; i; e1; e2; df; seq]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sequence : 'sequence Grammar.Entry.e)),
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__95)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__95)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__95)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'e__95) _ _ (loc : Ploc.t) ->
              (mksequence2 Qast.Loc seq : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "if")))
                         Grammar.s_self)
                      (Grammar.s_token ("", "then")))
                   Grammar.s_self)
                (Grammar.s_token ("", "else")))
             Grammar.s_self,
           (fun (e3 : 'expr) _ (e2 : 'expr) _ (e1 : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExIfe", [Qast.Loc; e1; e2; e3]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "try")))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm (match_case : 'match_case Grammar.Entry.e)),
           (fun (mc : 'match_case) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExTry", [Qast.Loc; e; Qast.VaVal (Qast.List [mc])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "try")))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTry", [Qast.Loc; e; l]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "match")))
                         Grammar.s_self)
                      (Grammar.s_token ("", "with")))
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (e1 : 'expr) _ (p1 : 'ipatt) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExMat",
                  [Qast.Loc; e;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p1; Qast.VaVal (Qast.Option None); e1]])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "match")))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExMat", [Qast.Loc; e; l]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm (fun_def : 'fun_def Grammar.Entry.e)),
           (fun (e : 'fun_def) (p : 'ipatt) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p; Qast.VaVal (Qast.Option None); e]])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) _ (loc : Ploc.t) ->
              (Qast.Node ("ExFun", [Qast.Loc; l]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (check_let_not_exception :
                                'check_let_not_exception Grammar.Entry.e)))
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_token ("", "open")))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (e : 'expr) _ (m : 'module_expr) _ _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExLop", [Qast.Loc; m; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (check_let_not_exception :
                                   'check_let_not_exception Grammar.Entry.e)))
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "module")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (uidopt : 'uidopt Grammar.Entry.e)),
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__94)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__94)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__94)))])))
                   (Grammar.s_nterm
                      (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (e : 'expr) _ (mb : 'mod_fun_binding) (m : 'e__94) _ _ _
                (loc : Ploc.t) ->
              (Qast.Node ("ExLmd", [Qast.Loc; m; mb; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (check_let_not_exception :
                                'check_let_not_exception Grammar.Entry.e)))
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "rec"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__92)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__92)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__92)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__92)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__92)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__93)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__93)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__93)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (x : 'expr) _ (l : 'e__93) (r : 'e__92) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExLet", [Qast.Loc; r; l; x]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (check_let_exception :
                                   'check_let_exception Grammar.Entry.e)))
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "exception")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("UIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__91)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__91)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__91)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uid", loc, a) : 'e__91)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                    'e__91)))])))
                   (Grammar.s_nterm
                      (alg_attributes : 'alg_attributes Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (x : 'expr) _ (alg_attrs : 'alg_attributes) (id : 'e__91) _ _
                _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExLEx",
                  [Qast.Loc; id; Qast.VaVal (Qast.List []); x; alg_attrs]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (check_let_exception :
                                         'check_let_exception
                                           Grammar.Entry.e)))
                                  (Grammar.s_token ("", "let")))
                               (Grammar.s_token ("", "exception")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("UIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) : 'e__89)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__89)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__89)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_uid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_uid", loc, a) :
                                          'e__89)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "uid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("uid", loc, a)) :
                                          'e__89)))])))
                         (Grammar.s_token ("", "of")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_list1
                                     (Grammar.s_nterml
                                        (ctyp : 'ctyp Grammar.Entry.e)
                                        "below_alg_attribute")),
                                (fun (a : 'ctyp list) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.List a) : 'e__90)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_list", loc, a) : 'e__90)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                    'e__90)))])))
                   (Grammar.s_nterm
                      (alg_attributes : 'alg_attributes Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (x : 'expr) _ (alg_attrs : 'alg_attributes) (tyl : 'e__90) _
                (id : 'e__89) _ _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExLEx", [Qast.Loc; id; tyl; x; alg_attrs]) :
               'expr)))];
       Some "where", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "where")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "rec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__99)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__99)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__99)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__99)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__99)))])))
             (Grammar.s_nterm (let_binding : 'let_binding Grammar.Entry.e)),
           (fun (lb : 'let_binding) (rf : 'e__99) _ (e : 'expr)
                (loc : Ploc.t) ->
              (Qast.Node
                 ("ExLet", [Qast.Loc; rf; Qast.VaVal (Qast.List [lb]); e]) :
               'expr)))];
       Some ":=", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", ":=")))
                Grammar.s_self)
             (Grammar.s_nterm (dummy : 'dummy Grammar.Entry.e)),
           (fun _ (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAss", [Qast.Loc; e1; e2]) : 'expr)))];
       Some "||", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "||")))
             Grammar.s_self,
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
               'expr)))];
       Some "&&", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "&&")))
             Grammar.s_self,
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
               'expr)))];
       Some "<", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "!=")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "==")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<>")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "=")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ">=")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<=")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ">")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<")))
             Grammar.s_self,
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
               'expr)))];
       Some "^", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "@")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "^")))
             Grammar.s_self,
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
               'expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__100)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__100)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__100)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__100) _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAtt", [Qast.Loc; e; attr]) : 'expr)))];
       Some "+", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-.")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "+.")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "+")))
             Grammar.s_self,
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
               'expr)))];
       Some "*", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "mod")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lxor")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lor")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "land")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "/.")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "*.")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "/")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "*")))
             Grammar.s_self,
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
               'expr)))];
       Some "**", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lsr")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lsl")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "asr")))
             Grammar.s_self,
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
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "**")))
             Grammar.s_self,
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
               'expr)))];
       Some "unary minus", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-.")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-.")]);
                   e]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-")]);
                   e]) :
               'expr)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "lazy")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExLaz", [Qast.Loc; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "assert")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExAsr", [Qast.Loc; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (e2 : 'expr) (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExApp", [Qast.Loc; e1; e2]) : 'expr)))];
       Some ".", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAcc", [Qast.Loc; e1; e2]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ",")) false),
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__101)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__101)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__101)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (el : 'e__101) _ _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExBae", [Qast.Loc; e; el]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "[")))
                Grammar.s_self)
             (Grammar.s_token ("", "]")),
           (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExSte", [Qast.Loc; e1; e2]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAre", [Qast.Loc; e1; e2]) : 'expr)))];
       Some "~-", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-.")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "~-.")]);
                   e]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "~-")]);
                   e]) :
               'expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ",")) false),
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__115)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__115)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__115)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (el : 'e__115) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTup", [Qast.Loc; el]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (loc : Ploc.t) -> (e : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ",")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))
                   (Grammar.s_token ("", ",")) false))
             (Grammar.s_token ("", ")")),
           (fun _ (el : 'expr list) _ (e : 'expr) _ (loc : Ploc.t) ->
              (mktupexp Qast.Loc e el : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "module")))
                (Grammar.s_nterm
                   (module_expr : 'module_expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (me : 'module_expr) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExPck", [Qast.Loc; me; Qast.Option None]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "(")))
                         (Grammar.s_token ("", "module")))
                      (Grammar.s_nterm
                         (module_expr : 'module_expr Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (mt : 'module_type) _ (me : 'module_expr) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("ExPck", [Qast.Loc; me; Qast.Option (Some mt)]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "{")))
                            (Grammar.s_token ("", "(")))
                         Grammar.s_self)
                      (Grammar.s_token ("", ")")))
                   (Grammar.s_token ("", "with")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_expr : 'label_expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__114)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__114)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__114)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lel : 'e__114) _ _ (e : 'expr) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExRec", [Qast.Loc; lel; Qast.Option (Some e)]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_expr : 'label_expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__113)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__113)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__113)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lel : 'e__113) _ (loc : Ploc.t) ->
              (Qast.Node ("ExRec", [Qast.Loc; lel; Qast.Option None]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[|")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__112)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__112)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__112)))])))
             (Grammar.s_token ("", "|]")),
           (fun _ (el : 'e__112) _ (loc : Ploc.t) ->
              (Qast.Node ("ExArr", [Qast.Loc; el]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))
                      (Grammar.s_token ("", ";")) false))
                (Grammar.s_nterm
                   (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (last : 'cons_expr_opt) (el : 'expr list) _
                (loc : Ploc.t) ->
              (mklistexp Qast.Loc last el : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")]) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ".")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("ExUnr", [Qast.Loc]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__111)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__111)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__111)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__111)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__111)))])),
           (fun (i : 'e__111) (loc : Ploc.t) ->
              (Qast.Node ("ExUid", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__110)))])),
           (fun (i : 'e__110) (loc : Ploc.t) ->
              (Qast.Node ("ExLid", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__109)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__109)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__109)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__109)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__109)))])),
           (fun (i : 'e__109) (loc : Ploc.t) ->
              (Qast.Node ("ExLid", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("ExExten", [Qast.Loc; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("CHAR", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__108)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_chr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_chr", loc, a) : 'e__108)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "chr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("chr", loc, a)) :
                           'e__108)))])),
           (fun (s : 'e__108) (loc : Ploc.t) ->
              (Qast.Node ("ExChr", [Qast.Loc; s]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("STRING", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__107)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_str")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_str", loc, a) : 'e__107)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "str")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                           'e__107)))])),
           (fun (s : 'e__107) (loc : Ploc.t) ->
              (Qast.Node ("ExStr", [Qast.Loc; s]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("FLOAT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__106)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_flo")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_flo", loc, a) : 'e__106)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "flo")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("flo", loc, a)) :
                           'e__106)))])),
           (fun (s : 'e__106) (loc : Ploc.t) ->
              (Qast.Node ("ExFlo", [Qast.Loc; s]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_n", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__105)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_nativeint")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_nativeint", loc, a) : 'e__105)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "nativeint")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("nativeint", loc, a)) :
                           'e__105)))])),
           (fun (s : 'e__105) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "n"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_L", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__104)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int64")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int64", loc, a) : 'e__104)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int64")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int64", loc, a)) :
                           'e__104)))])),
           (fun (s : 'e__104) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "L"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_l", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__103)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int32")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int32", loc, a) : 'e__103)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int32")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int32", loc, a)) :
                           'e__103)))])),
           (fun (s : 'e__103) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "l"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__102)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int", loc, a) : 'e__102)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int", loc, a)) :
                           'e__102)))])),
           (fun (s : 'e__102) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str ""]) : 'expr)))]];
    Grammar.extension (closed_case_list : 'closed_case_list Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "|")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (match_case : 'match_case Grammar.Entry.e))
                               (Grammar.s_token ("", "|")) false),
                          (fun (a : 'match_case list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__117)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__117)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__117)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (l : 'e__117) _ (loc : Ploc.t) -> (l : 'closed_case_list)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (match_case : 'match_case Grammar.Entry.e))
                               (Grammar.s_token ("", "|")) false),
                          (fun (a : 'match_case list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__116)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__116)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__116)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (l : 'e__116) _ (loc : Ploc.t) ->
              (l : 'closed_case_list)))]];
    Grammar.extension (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (Qast.Option None : 'cons_expr_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Option (Some e) : 'cons_expr_opt)))]];
    Grammar.extension (dummy : 'dummy Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> (() : 'dummy)))]];
    Grammar.extension (sequence : 'sequence Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) (loc : Ploc.t) -> (Qast.List [e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           (fun _ (e : 'expr) (loc : Ploc.t) -> (Qast.List [e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Cons (e, el) : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_token ("", "open")))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (m : 'module_expr) _ _ (loc : Ploc.t) ->
              (Qast.List
                 [Qast.Node
                    ("ExLop", [Qast.Loc; m; mksequence Qast.Loc el])] :
               'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "module")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (uidopt : 'uidopt Grammar.Entry.e)),
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__120)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__120)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__120)))])))
                   (Grammar.s_nterm
                      (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (mb : 'mod_fun_binding) (m : 'e__120) _ _
                (loc : Ploc.t) ->
              (Qast.List
                 [Qast.Node
                    ("ExLmd", [Qast.Loc; m; mb; mksequence Qast.Loc el])] :
               'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "rec"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__118)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__118)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__118)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__118)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__118)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__119)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__119)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__119)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (l : 'e__119) (rf : 'e__118) _
                (loc : Ploc.t) ->
              (Qast.List
                 [Qast.Node
                    ("ExLet", [Qast.Loc; rf; l; mksequence Qast.Loc el])] :
               'sequence)))]];
    Grammar.extension (let_binding : 'let_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_nterm
                   (fun_binding : 'fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (e : 'fun_binding) (p : 'ipatt)
                (loc : Ploc.t) ->
              (Qast.Tuple [p; e; attrs] : 'let_binding)))]];
    Grammar.extension (fun_binding : 'fun_binding Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e : 'fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p; Qast.VaVal (Qast.Option None); e]])]) :
               'fun_binding)))]];
    Grammar.extension (match_case : 'match_case Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                      (Grammar.s_nterm
                         (as_patt_opt : 'as_patt_opt Grammar.Entry.e)))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (when_expr :
                                      'when_expr Grammar.Entry.e))),
                             (fun (a : 'when_expr option) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__121)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__121)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__121)))])))
                (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (w : 'e__121) (aso : 'as_patt_opt) (p : 'patt)
                (loc : Ploc.t) ->
              (mkmatchcase Qast.Loc p aso w e : 'match_case)))]];
    Grammar.extension (as_patt_opt : 'as_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (Qast.Option None : 'as_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Option (Some p) : 'as_patt_opt)))]];
    Grammar.extension (when_expr : 'when_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "when")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'when_expr)))]];
    Grammar.extension (label_expr : 'label_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (patt_label_ident : 'patt_label_ident Grammar.Entry.e)))
             (Grammar.s_nterm (fun_binding : 'fun_binding Grammar.Entry.e)),
           (fun (e : 'fun_binding) (i : 'patt_label_ident) (loc : Ploc.t) ->
              (Qast.Tuple [i; e] : 'label_expr)))]];
    Grammar.extension (fun_def : 'fun_def Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e : 'fun_def) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p; Qast.VaVal (Qast.Option None); e]])]) :
               'fun_def)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "|")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaOrp", [Qast.Loc; p1; p2]) : 'patt)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__122)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__122)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__122)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__122) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaAtt", [Qast.Loc; p1; attr]) : 'patt)))];
       None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("", "exception")))
             Grammar.s_self,
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaExc", [Qast.Loc; p]) : 'patt)))];
       None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "..")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaRng", [Qast.Loc; p1; p2]) : 'patt)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "lazy")))
             Grammar.s_self,
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaLaz", [Qast.Loc; p]) : 'patt)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (p2 : 'patt) (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaApp", [Qast.Loc; p1; p2]) : 'patt)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaAcc", [Qast.Loc; p1; p2]) : 'patt)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (paren_patt : 'paren_patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (p : 'paren_patt) _ (loc : Ploc.t) -> (p : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_patt : 'label_patt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_patt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__134)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__134)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__134)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lpl : 'e__134) _ (loc : Ploc.t) ->
              (Qast.Node ("PaRec", [Qast.Loc; lpl]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[|")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (patt : 'patt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'patt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__133)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__133)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__133)))])))
             (Grammar.s_token ("", "|]")),
           (fun _ (pl : 'e__133) _ (loc : Ploc.t) ->
              (Qast.Node ("PaArr", [Qast.Loc; pl]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                      (Grammar.s_token ("", ";")) false))
                (Grammar.s_nterm
                   (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (last : 'cons_patt_opt) (pl : 'patt list) _
                (loc : Ploc.t) ->
              (mklistpat Qast.Loc last pl : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("FLOAT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node ("PaFlo", [Qast.Loc; Qast.VaVal (neg_string s)]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_n", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "n"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_L", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "L"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_l", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "l"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str ""]) :
               'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("CHAR", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__132)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_chr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_chr", loc, a) : 'e__132)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "chr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("chr", loc, a)) :
                           'e__132)))])),
           (fun (s : 'e__132) (loc : Ploc.t) ->
              (Qast.Node ("PaChr", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("STRING", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__131)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_str")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_str", loc, a) : 'e__131)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "str")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                           'e__131)))])),
           (fun (s : 'e__131) (loc : Ploc.t) ->
              (Qast.Node ("PaStr", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("FLOAT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__130)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_flo")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_flo", loc, a) : 'e__130)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "flo")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("flo", loc, a)) :
                           'e__130)))])),
           (fun (s : 'e__130) (loc : Ploc.t) ->
              (Qast.Node ("PaFlo", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_n", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__129)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_nativeint")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_nativeint", loc, a) : 'e__129)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "nativeint")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("nativeint", loc, a)) :
                           'e__129)))])),
           (fun (s : 'e__129) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "n"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_L", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__128)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int64")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int64", loc, a) : 'e__128)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int64")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int64", loc, a)) :
                           'e__128)))])),
           (fun (s : 'e__128) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "L"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_l", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__127)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int32")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int32", loc, a) : 'e__127)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int32")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int32", loc, a)) :
                           'e__127)))])),
           (fun (s : 'e__127) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "l"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__126)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int", loc, a) : 'e__126)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int", loc, a)) :
                           'e__126)))])),
           (fun (s : 'e__126) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str ""]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__125)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__125)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__125)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__125)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__125)))])),
           (fun (s : 'e__125) (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__124)))])),
           (fun (s : 'e__124) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__123)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__123)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__123)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__123)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__123)))])),
           (fun (s : 'e__123) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("PaExten", [Qast.Loc; e]) : 'patt)))]];
    Grammar.extension (paren_patt : 'paren_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
                       (fun (a : 'uidopt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__138)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uidopt", loc, a) : 'e__138)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uidopt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                           'e__138)))])),
           (fun (s : 'e__138) _ (loc : Ploc.t) ->
              (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option None]) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (uidopt : 'uidopt Grammar.Entry.e)),
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__137)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__137)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__137)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (s : 'e__137) _ (loc : Ploc.t) ->
              (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option (Some mt)]) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__136)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__136)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__136)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__136)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__136)))])),
           (fun (s : 'e__136) _ (loc : Ploc.t) ->
              (Qast.Node ("PaNty", [Qast.Loc; s]) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                            (Grammar.s_token ("", ",")) false),
                       (fun (a : 'patt list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__135)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__135)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__135)))])),
           (fun (pl : 'e__135) (loc : Ploc.t) ->
              (Qast.Node ("PaTup", [Qast.Loc; pl]) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) (loc : Ploc.t) -> (p : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ",")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           (fun (pl : 'patt list) _ (p : 'patt) (loc : Ploc.t) ->
              (mktuppat Qast.Loc p pl : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p2 : 'patt) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaAli", [Qast.Loc; p; p2]) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'paren_patt)))]];
    Grammar.extension (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (Qast.Option None : 'cons_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Option (Some p) : 'cons_patt_opt)))]];
    Grammar.extension (label_patt : 'label_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (patt_label_ident : 'patt_label_ident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (i : 'patt_label_ident) (loc : Ploc.t) ->
              (Qast.Tuple [i; p] : 'label_patt)))]];
    Grammar.extension (patt_label_ident : 'patt_label_ident Grammar.Entry.e)
      None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (p2 : 'patt_label_ident) _ (p1 : 'patt_label_ident)
                (loc : Ploc.t) ->
              (Qast.Node ("PaAcc", [Qast.Loc; p1; p2]) :
               'patt_label_ident)))];
       Some "simple", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__140)))])),
           (fun (i : 'e__140) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; i]) : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__139)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__139)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__139)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__139)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__139)))])),
           (fun (i : 'e__139) (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; i]) : 'patt_label_ident)))]];
    Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__143)))])),
           (fun (s : 'e__143) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__142)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__142)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__142)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__142)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__142)))])),
           (fun (s : 'e__142) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("PaExten", [Qast.Loc; e]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm
                   (paren_ipatt : 'paren_ipatt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (p : 'paren_ipatt) _ (loc : Ploc.t) -> (p : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_ipatt :
                                   'label_ipatt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_ipatt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__141)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__141)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__141)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lpl : 'e__141) _ (loc : Ploc.t) ->
              (Qast.Node ("PaRec", [Qast.Loc; lpl]) : 'ipatt)))]];
    Grammar.extension (paren_ipatt : 'paren_ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
                       (fun (a : 'uidopt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__147)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uidopt", loc, a) : 'e__147)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uidopt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                           'e__147)))])),
           (fun (s : 'e__147) _ (loc : Ploc.t) ->
              (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option None]) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (uidopt : 'uidopt Grammar.Entry.e)),
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__146)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__146)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__146)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (s : 'e__146) _ (loc : Ploc.t) ->
              (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option (Some mt)]) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__145)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__145)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__145)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__145)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__145)))])),
           (fun (s : 'e__145) _ (loc : Ploc.t) ->
              (Qast.Node ("PaNty", [Qast.Loc; s]) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))
                            (Grammar.s_token ("", ",")) false),
                       (fun (a : 'ipatt list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__144)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__144)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__144)))])),
           (fun (pl : 'e__144) (loc : Ploc.t) ->
              (Qast.Node ("PaTup", [Qast.Loc; pl]) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p : 'ipatt) (loc : Ploc.t) -> (p : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ",")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           (fun (pl : 'ipatt list) _ (p : 'ipatt) (loc : Ploc.t) ->
              (mktuppat Qast.Loc p pl : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p2 : 'ipatt) _ (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("PaAli", [Qast.Loc; p; p2]) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'paren_ipatt)))]];
    Grammar.extension (label_ipatt : 'label_ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (patt_label_ident : 'patt_label_ident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p : 'ipatt) _ (i : 'patt_label_ident) (loc : Ploc.t) ->
              (Qast.Tuple [i; p] : 'label_ipatt)))]];
    Grammar.extension (type_decl : 'type_decl Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_facto
                                  (Grammar.s_rules
                                     [Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (type_patt :
                                               'type_patt Grammar.Entry.e)),
                                         (fun (a : 'type_patt)
                                              (loc : Ploc.t) ->
                                            (Qast.VaVal a : 'e__148)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "_tp")),
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaAnt ("_tp", loc, a) :
                                             'e__148)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "tp")),
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal
                                               (Qast.VaAnt ("tp", loc, a)) :
                                             'e__148)))])))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_list0
                                           (Grammar.s_nterm
                                              (type_parameter :
                                               'type_parameter
                                                 Grammar.Entry.e))),
                                      (fun (a : 'type_parameter list)
                                           (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.List a) :
                                          'e__149)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_list")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_list", loc, a) :
                                          'e__149)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "list")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("list", loc, a)) :
                                          'e__149)))])))
                         (Grammar.s_token ("", "=")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "private"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__150)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_priv")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_priv", loc, a) : 'e__150)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "priv")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) :
                                    'e__150)))])))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_nterm
                                  (constrain : 'constrain Grammar.Entry.e))),
                          (fun (a : 'constrain list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__151)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__151)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__151)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (cl : 'e__151) (tk : 'ctyp)
                (pf : 'e__150) _ (tpl : 'e__149) (n : 'e__148)
                (loc : Ploc.t) ->
              (Qast.Record
                 ["tdNam", n; "tdPrm", tpl; "tdPrv", pf; "tdDef", tk;
                  "tdCon", cl; "tdAttributes", attrs] :
               'type_decl)))]];
    (* TODO FIX: this should be a longident+lid, to match ocaml's grammar *)
    Grammar.extension (type_extension : 'type_extension Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (mod_ident_patt :
                                            'mod_ident_patt Grammar.Entry.e)),
                                      (fun (a : 'mod_ident_patt)
                                           (loc : Ploc.t) ->
                                         (Qast.VaVal a : 'e__152)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_tp")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_tp", loc, a) :
                                          'e__152)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "tp")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("tp", loc, a)) :
                                          'e__152)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_list0
                                        (Grammar.s_nterm
                                           (type_parameter :
                                            'type_parameter
                                              Grammar.Entry.e))),
                                   (fun (a : 'type_parameter list)
                                        (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.List a) : 'e__153)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_list")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_list", loc, a) :
                                       'e__153)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "list")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("list", loc, a)) :
                                       'e__153)))])))
                      (Grammar.s_token ("", "+=")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_flag
                                  (Grammar.s_token ("", "private"))),
                             (fun (a : bool) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Bool a) : 'e__154)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_priv")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_priv", loc, a) : 'e__154)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "priv")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) :
                                 'e__154)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (extension_constructor :
                                   'extension_constructor Grammar.Entry.e))
                               (Grammar.s_token ("", "|")) false),
                          (fun (a : 'extension_constructor list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__155)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__155)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__155)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (ecs : 'e__155) (pf : 'e__154) _
                (tpl : 'e__153) (n : 'e__152) (loc : Ploc.t) ->
              (Qast.Record
                 ["teNam", n; "tePrm", tpl; "tePrv", pf; "teECs", ecs;
                  "teAttributes", attrs] :
               'type_extension)))]];
    (* why is this called what it's called? *)
    Grammar.extension (mod_ident_patt : 'mod_ident_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (mod_ident : 'mod_ident Grammar.Entry.e)),
                       (fun (a : 'mod_ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__156)))])),
           (fun (n : 'e__156) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; n] : 'mod_ident_patt)))]];
    Grammar.extension (type_patt : 'type_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__157)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__157)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__157)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__157)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__157)))])),
           (fun (n : 'e__157) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; n] : 'type_patt)))]];
    Grammar.extension (constrain : 'constrain Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "constraint")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Tuple [t1; t2] : 'constrain)))]];
    Grammar.extension (type_parameter : 'type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (simple_type_parameter :
                             'simple_type_parameter Grammar.Entry.e)),
                       (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__160)))])),
           (fun (p : 'e__160) (loc : Ploc.t) ->
              (Qast.Tuple [p; Qast.Option None] : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (simple_type_parameter :
                             'simple_type_parameter Grammar.Entry.e)),
                       (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__159)))])),
           (fun (p : 'e__159) _ (loc : Ploc.t) ->
              (Qast.Tuple [p; Qast.Option (Some (Qast.Bool false))] :
               'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (simple_type_parameter :
                             'simple_type_parameter Grammar.Entry.e)),
                       (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__158)))])),
           (fun (p : 'e__158) _ (loc : Ploc.t) ->
              (Qast.Tuple [p; Qast.Option (Some (Qast.Bool true))] :
               'type_parameter)))]];
    Grammar.extension
      (simple_type_parameter : 'simple_type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Option None : 'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.Option (Some (greek_ascii_equiv i)) :
               'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) ->
              (Qast.Option (Some i) : 'simple_type_parameter)))]];
    Grammar.extension
      (extended_longident : 'extended_longident Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_nterm
                      (check_dot_uid : 'check_dot_uid Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__161)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__161)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__161)))])),
           (fun (i : 'e__161) _ _ (me1 : 'extended_longident)
                (loc : Ploc.t) ->
              (Qast.Node ("LiAcc", [Qast.Loc; me1; i]) :
               'extended_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (me2 : 'extended_longident) _ (me1 : 'extended_longident)
                (loc : Ploc.t) ->
              (Qast.Node ("LiApp", [Qast.Loc; me1; me2]) :
               'extended_longident)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__162)))])),
           (fun (i : 'e__162) (loc : Ploc.t) ->
              (Qast.Node ("LiUid", [Qast.Loc; i]) : 'extended_longident)))]];
    Grammar.extension (ctyp_ident : 'ctyp_ident Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__164)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__164)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__164)))])),
           (fun (i : 'e__164) (loc : Ploc.t) ->
              (Qast.Node ("TyLid", [Qast.Loc; i]) : 'ctyp_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__163)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__163)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__163)))])),
           (fun (i : 'e__163) _ (me1 : 'extended_longident) (loc : Ploc.t) ->
              (Qast.Node ("TyAcc", [Qast.Loc; me1; i]) : 'ctyp_ident)))]];
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e) None
      [Some "top", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "==")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag
                               (Grammar.s_token ("", "private"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__165)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_priv")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_priv", loc, a) : 'e__165)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "priv")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) :
                              'e__165)))])))
             Grammar.s_self,
           (fun (t2 : 'ctyp) (pf : 'e__165) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyMan", [Qast.Loc; t1; pf; t2]) : 'ctyp)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__166)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__166)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__166)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__166) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyAtt", [Qast.Loc; t1; attr]) : 'ctyp)))];
       Some "below_alg_attribute", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop Grammar.s_next,
           (fun (t : 'ctyp) (loc : Ploc.t) -> (t : 'ctyp)))];
       Some "as", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "as")))
             Grammar.s_self,
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyAli", [Qast.Loc; t1; t2]) : 'ctyp)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1
                                  (Grammar.s_token ("LIDENT", ""))),
                             (fun (a : string list) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.List
                                      (List.map (fun a -> Qast.Str a) a)) :
                                 'e__168)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__168)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__168)))])))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (t : 'ctyp) _ (pl : 'e__168) _ (loc : Ploc.t) ->
              (Qast.Node ("TyPot", [Qast.Loc; pl; t]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1
                                  (Grammar.s_nterm
                                     (typevar : 'typevar Grammar.Entry.e))),
                             (fun (a : 'typevar list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__167)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__167)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__167)))])))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (t : 'ctyp) _ (pl : 'e__167) _ (loc : Ploc.t) ->
              (Qast.Node ("TyPol", [Qast.Loc; pl; t]) : 'ctyp)))];
       Some "arrow", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyArr", [Qast.Loc; t1; t2]) : 'ctyp)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (t2 : 'ctyp) (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyApp", [Qast.Loc; t1; t2]) : 'ctyp)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp_ident : 'ctyp_ident Grammar.Entry.e)),
           (fun (t : 'ctyp_ident) (loc : Ploc.t) -> (t : 'ctyp)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_declaration :
                                   'label_declaration Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_declaration list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__172)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__172)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__172)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (ldl : 'e__172) _ (loc : Ploc.t) ->
              (Qast.Node ("TyRec", [Qast.Loc; ldl]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (constructor_declaration :
                                   'constructor_declaration Grammar.Entry.e))
                               (Grammar.s_token ("", "|")) false),
                          (fun (a : 'constructor_declaration list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__171)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__171)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__171)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (cdl : 'e__171) _ (loc : Ploc.t) ->
              (Qast.Node ("TySum", [Qast.Loc; cdl]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ctyp : 'ctyp Grammar.Entry.e))
                               (Grammar.s_token ("", "*")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__170)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__170)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__170)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (tl : 'e__170) _ (loc : Ploc.t) ->
              (Qast.Node ("TyTup", [Qast.Loc; tl]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", "*")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e))
                   (Grammar.s_token ("", "*")) false))
             (Grammar.s_token ("", ")")),
           (fun _ (tl : 'ctyp list) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (mktuptyp Qast.Loc t tl : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (loc : Ploc.t) ->
              (Qast.Node ("TyPck", [Qast.Loc; mt]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("TyExten", [Qast.Loc; e]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("TyAny", [Qast.Loc]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "..")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("TyOpn", [Qast.Loc]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.Node
                 ("TyQuo", [Qast.Loc; Qast.VaVal (greek_ascii_equiv i)]) :
               'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__169)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__169)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__169)))])),
           (fun (i : 'e__169) _ (loc : Ploc.t) ->
              (Qast.Node ("TyQuo", [Qast.Loc; i]) : 'ctyp)))]];
    Grammar.extension (cons_ident : 'cons_ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__173)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__173)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__173)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__173)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__173)))])),
           (fun (ci : 'e__173) (loc : Ploc.t) -> (ci : 'cons_ident)))]];
    Grammar.extension
      (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (Qast.Tuple
                 [Qast.Loc; ci; Qast.VaVal (Qast.List []); Qast.Option None;
                  alg_attrs] :
               'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (cons_ident : 'cons_ident Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (t : 'ctyp) _ (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (let (tl, rt) = generalized_type_of_type t in
               Qast.Tuple
                 [Qast.Loc; ci; Qast.VaVal tl; Qast.Option (Some rt);
                  alg_attrs] :
               'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (cons_ident : 'cons_ident Grammar.Entry.e)))
                   (Grammar.s_token ("", "of")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ctyp : 'ctyp Grammar.Entry.e))
                               (Grammar.s_token ("", "and")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__174)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__174)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__174)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (cal : 'e__174) _
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; ci; cal; Qast.Option None; alg_attrs] :
               'constructor_declaration)))]];
    Grammar.extension
      (constructor_declaration_sans_alg_attrs :
       'constructor_declaration_sans_alg_attrs Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)),
           (fun (ci : 'cons_ident) (loc : Ploc.t) ->
              (Qast.Tuple
                 [Qast.Loc; ci; Qast.VaVal (Qast.List []); Qast.Option None] :
               'constructor_declaration_sans_alg_attrs)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (cons_ident : 'cons_ident Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (ci : 'cons_ident) (loc : Ploc.t) ->
              (let (tl, rt) = generalized_type_of_type t in
               Qast.Tuple
                 [Qast.Loc; ci; Qast.VaVal tl; Qast.Option (Some rt)] :
               'constructor_declaration_sans_alg_attrs)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (cons_ident : 'cons_ident Grammar.Entry.e)))
                (Grammar.s_token ("", "of")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'ctyp list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__175)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__175)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__175)))])),
           (fun (cal : 'e__175) _ (ci : 'cons_ident) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; ci; cal; Qast.Option None] :
               'constructor_declaration_sans_alg_attrs)))]];
    Grammar.extension (label_declaration : 'label_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")))
                      (Grammar.s_token ("", ":")))
                   (Grammar.s_flag (Grammar.s_token ("", "mutable"))))
                (Grammar.s_nterml (ctyp : 'ctyp Grammar.Entry.e)
                   "below_alg_attribute"))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (t : 'ctyp) (mf : bool) _
                (i : string) (loc : Ploc.t) ->
              (mklabdecl Qast.Loc i mf t alg_attrs : 'label_declaration)))]];
    Grammar.extension (ident : 'ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident)))]];
    Grammar.extension (mod_ident : 'mod_ident Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "")))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (j : 'mod_ident) _ (i : string) (loc : Ploc.t) ->
              (Qast.Cons (mkident i, j) : 'mod_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.List [mkident i] : 'mod_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.List [mkident i] : 'mod_ident)))]];
    Grammar.extension (direction_flag : 'direction_flag Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "downto")),
           (fun _ (loc : Ploc.t) -> (Qast.Bool false : 'direction_flag)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "to")),
           (fun _ (loc : Ploc.t) -> (Qast.Bool true : 'direction_flag)))]];
    Grammar.extension (typevar : 'typevar Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) -> (i : 'typevar)))]];
    (* Objects and Classes *)
    Grammar.extension (str_item : 'str_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "class")))
                (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (class_type_declaration :
                                'class_type_declaration Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'class_type_declaration list)
                            (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__177)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__177)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__177)))])),
           (fun (ctd : 'e__177) _ _ (loc : Ploc.t) ->
              (Qast.Node ("StClt", [Qast.Loc; ctd]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "class")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (class_declaration :
                                'class_declaration Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'class_declaration list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__176)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__176)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__176)))])),
           (fun (cd : 'e__176) _ (loc : Ploc.t) ->
              (Qast.Node ("StCls", [Qast.Loc; cd]) : 'str_item)))]];
    Grammar.extension (sig_item : 'sig_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "class")))
                (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (class_type_declaration :
                                'class_type_declaration Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'class_type_declaration list)
                            (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__179)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__179)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__179)))])),
           (fun (ctd : 'e__179) _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgClt", [Qast.Loc; ctd]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "class")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (class_description :
                                'class_description Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'class_description list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__178)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__178)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__178)))])),
           (fun (cd : 'e__178) _ (loc : Ploc.t) ->
              (Qast.Node ("SgCls", [Qast.Loc; cd]) : 'sig_item)))]];
    Grammar.extension (class_declaration : 'class_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "virtual"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__180)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__180)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__180)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__180)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__180)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__181)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__181)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__181)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__181)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__181)))])))
                   (Grammar.s_nterm
                      (class_type_parameters :
                       'class_type_parameters Grammar.Entry.e)))
                (Grammar.s_nterm
                   (class_fun_binding : 'class_fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (cfb : 'class_fun_binding)
                (ctp : 'class_type_parameters) (i : 'e__181) (vf : 'e__180)
                (loc : Ploc.t) ->
              (Qast.Record
                 ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", i;
                  "ciExp", cfb; "ciAttributes", attrs] :
               'class_declaration)))]];
    Grammar.extension (class_fun_binding : 'class_fun_binding Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (cfb : 'class_fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("CeFun", [Qast.Loc; p; cfb]) :
               'class_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm
                      (class_type : 'class_type Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           (fun (ce : 'class_expr) _ (ct : 'class_type) _ (loc : Ploc.t) ->
              (Qast.Node ("CeTyc", [Qast.Loc; ce; ct]) :
               'class_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           (fun (ce : 'class_expr) _ (loc : Ploc.t) ->
              (ce : 'class_fun_binding)))]];
    Grammar.extension
      (class_type_parameters : 'class_type_parameters Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (type_parameter :
                                   'type_parameter Grammar.Entry.e))
                               (Grammar.s_token ("", ",")) false),
                          (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__182)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__182)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__182)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (tpl : 'e__182) _ (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; tpl] : 'class_type_parameters)));
        Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; Qast.VaVal (Qast.List [])] :
               'class_type_parameters)))]];
    Grammar.extension (class_fun_def : 'class_fun_def Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           (fun (ce : 'class_expr) _ (loc : Ploc.t) ->
              (ce : 'class_fun_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (ce : 'class_fun_def) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("CeFun", [Qast.Loc; p; ce]) : 'class_fun_def)))]];
    Grammar.extension (class_expr : 'class_expr Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "rec"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__183)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__183)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__183)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__183)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__183)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__184)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__184)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__184)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (ce : 'class_expr) _ (lb : 'e__184) (rf : 'e__183) _
                (loc : Ploc.t) ->
              (Qast.Node ("CeLet", [Qast.Loc; rf; lb; ce]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm
                (class_fun_def : 'class_fun_def Grammar.Entry.e)),
           (fun (ce : 'class_fun_def) (p : 'ipatt) _ (loc : Ploc.t) ->
              (Qast.Node ("CeFun", [Qast.Loc; p; ce]) : 'class_expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__185)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__185)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__185)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__185) _ (t1 : 'class_expr) (loc : Ploc.t) ->
              (Qast.Node ("CeAtt", [Qast.Loc; t1; attr]) : 'class_expr)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "label"),
           (fun (e : 'expr) (ce : 'class_expr) (loc : Ploc.t) ->
              (Qast.Node ("CeApp", [Qast.Loc; ce; e]) : 'class_expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__186)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__186)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__186)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__186) _ (t1 : 'class_expr) (loc : Ploc.t) ->
              (Qast.Node ("CeAtt", [Qast.Loc; t1; attr]) : 'class_expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("CeExten", [Qast.Loc; e]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (ce : 'class_expr) _ (loc : Ploc.t) -> (ce : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (ct : 'class_type) _ (ce : 'class_expr) _ (loc : Ploc.t) ->
              (Qast.Node ("CeTyc", [Qast.Loc; ce; ct]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (ctyp : 'ctyp Grammar.Entry.e))
                                  (Grammar.s_token ("", ",")) false),
                             (fun (a : 'ctyp list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__189)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__189)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__189)))])))
                (Grammar.s_token ("", "]")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (class_longident :
                             'class_longident Grammar.Entry.e)),
                       (fun (a : 'class_longident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__190)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__190)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__190)))])),
           (fun (ci : 'e__190) _ (ctcl : 'e__189) _ (loc : Ploc.t) ->
              (Qast.Node ("CeCon", [Qast.Loc; ci; ctcl]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "object")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (class_self_patt :
                                      'class_self_patt Grammar.Entry.e))),
                             (fun (a : 'class_self_patt option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__188)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__188)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__188)))])))
                (Grammar.s_nterm
                   (class_structure : 'class_structure Grammar.Entry.e)))
             (Grammar.s_token ("", "end")),
           (fun _ (cf : 'class_structure) (cspo : 'e__188) _ (loc : Ploc.t) ->
              (Qast.Node ("CeStr", [Qast.Loc; cspo; cf]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (class_longident :
                             'class_longident Grammar.Entry.e)),
                       (fun (a : 'class_longident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__187)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__187)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__187)))])),
           (fun (ci : 'e__187) (loc : Ploc.t) ->
              (Qast.Node
                 ("CeCon", [Qast.Loc; ci; Qast.VaVal (Qast.List [])]) :
               'class_expr)))]];
    Grammar.extension (class_structure : 'class_structure Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (class_str_item :
                                            'class_str_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (cf : 'class_str_item)
                                        (loc : Ploc.t) ->
                                      (cf : 'e__191)))])),
                       (fun (a : 'e__191 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__192)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__192)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__192)))])),
           (fun (cf : 'e__192) (loc : Ploc.t) -> (cf : 'class_structure)))]];
    Grammar.extension (class_self_patt : 'class_self_patt Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'class_self_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (p : 'patt) _ (loc : Ploc.t) -> (p : 'class_self_patt)))]];
    Grammar.extension (class_str_item : 'class_str_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (Qast.Node ("CrExten", [Qast.Loc; e]) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (Qast.Node ("CrFlAtt", [Qast.Loc; attr]) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "initializer")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (se : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("CrIni", [Qast.Loc; se; attrs]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t2 : 'ctyp) _ (t1 : 'ctyp) _
                (loc : Ploc.t) ->
              (Qast.Node ("CrCtr", [Qast.Loc; t1; t2; attrs]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "method")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_flag
                                           (Grammar.s_token ("", "!"))),
                                      (fun (a : bool) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Bool a) :
                                          'e__204)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_!")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_!", loc, a) :
                                          'e__204)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "!")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("!", loc, a)) :
                                          'e__204)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "private"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__205)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_priv")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_priv", loc, a) :
                                       'e__205)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "priv")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("priv", loc, a)) :
                                       'e__205)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__206)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__206)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__206)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__206)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__206)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (polyt : 'polyt Grammar.Entry.e))),
                             (fun (a : 'polyt option) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__207)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__207)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__207)))])))
                (Grammar.s_nterm
                   (fun_binding : 'fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (e : 'fun_binding) (topt : 'e__207)
                (l : 'e__206) (pf : 'e__205) (ovf : 'e__204) _
                (loc : Ploc.t) ->
              (Qast.Node ("CrMth", [Qast.Loc; ovf; pf; l; topt; e; attrs]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "method")))
                            (Grammar.s_token ("", "virtual")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "private"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__202)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__202)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__202)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__202)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__202)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__203)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__203)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__203)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__203)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__203)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'e__203)
                (pf : 'e__202) _ _ (loc : Ploc.t) ->
              (Qast.Node ("CrVir", [Qast.Loc; pf; l; t; attrs]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "value")))
                            (Grammar.s_token ("", "virtual")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "mutable"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__200)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__200)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__200)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__200)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__200)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__201)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__201)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__201)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__201)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__201)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (lab : 'e__201)
                (mf : 'e__200) _ _ (loc : Ploc.t) ->
              (Qast.Node ("CrVav", [Qast.Loc; mf; lab; t; attrs]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "value")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "!"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__197)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_!")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_!", loc, a) : 'e__197)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "!")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                       'e__197)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "mutable"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__198)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__198)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__198)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__198)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__198)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (lident : 'lident Grammar.Entry.e)),
                             (fun (a : 'lident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__199)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__199)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__199)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__199)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__199)))])))
                (Grammar.s_nterm
                   (cvalue_binding : 'cvalue_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (e : 'cvalue_binding)
                (lab : 'e__199) (mf : 'e__198) (ovf : 'e__197) _
                (loc : Ploc.t) ->
              (Qast.Node ("CrVal", [Qast.Loc; ovf; mf; lab; e; attrs]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "inherit")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "!"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__195)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_!")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_!", loc, a) : 'e__195)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "!")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                    'e__195)))])))
                   (Grammar.s_nterm
                      (class_expr : 'class_expr Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_nterm
                                  (as_lident : 'as_lident Grammar.Entry.e))),
                          (fun (a : 'as_lident option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__196)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__196)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__196)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (pb : 'e__196) (ce : 'class_expr)
                (ovf : 'e__195) _ (loc : Ploc.t) ->
              (Qast.Node ("CrInh", [Qast.Loc; ovf; ce; pb; attrs]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (class_str_item :
                                               'class_str_item
                                                 Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (s : 'class_str_item)
                                           (loc : Ploc.t) ->
                                         (s : 'e__193)))])),
                          (fun (a : 'e__193 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__194)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__194)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__194)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__194) _ (loc : Ploc.t) ->
              (Qast.Node ("CrDcl", [Qast.Loc; st]) : 'class_str_item)))]];
    Grammar.extension (as_lident : 'as_lident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) _ (loc : Ploc.t) -> (mkident i : 'as_lident)))]];
    Grammar.extension (polyt : 'polyt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'polyt)))]];
    Grammar.extension (cvalue_binding : 'cvalue_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", ":>")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option None; t]) :
               'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", ":")))
                         (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                      (Grammar.s_token ("", ":>")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t2 : 'ctyp) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option (Some t); t2]) :
               'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'cvalue_binding)))]];
    Grammar.extension (lident : 'lident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'lident)))]];
    Grammar.extension (class_type : 'class_type Grammar.Entry.e) None
      [Some "top", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "[")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "]")))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (ct : 'class_type) _ _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("CtFun", [Qast.Loc; t; ct]) : 'class_type)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__208)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__208)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__208)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__208) _ (t1 : 'class_type) (loc : Ploc.t) ->
              (Qast.Node ("CtAtt", [Qast.Loc; t1; attr]) : 'class_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ctyp : 'ctyp Grammar.Entry.e))
                               (Grammar.s_token ("", ",")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__212)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__212)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__212)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (tl : 'e__212) _ (ct : 'class_type) (loc : Ploc.t) ->
              (Qast.Node ("CtCon", [Qast.Loc; ct; tl]) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "object")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (class_self_type :
                                      'class_self_type Grammar.Entry.e))),
                             (fun (a : 'class_self_type option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__209)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__209)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__209)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (class_sig_item :
                                               'class_sig_item
                                                 Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (csf : 'class_sig_item)
                                           (loc : Ploc.t) ->
                                         (csf : 'e__210)))])),
                          (fun (a : 'e__210 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__211)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__211)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__211)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (csf : 'e__211) (cst : 'e__209) _ (loc : Ploc.t) ->
              (Qast.Node ("CtSig", [Qast.Loc; cst; csf]) : 'class_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("CtExten", [Qast.Loc; e]) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (ct : 'class_type) _ (loc : Ploc.t) -> (ct : 'class_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__214)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__214)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__214)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__214)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__214)))])),
           (fun (i : 'e__214) (loc : Ploc.t) ->
              (Qast.Node ("CtLid", [Qast.Loc; i]) : 'class_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (extended_longident : 'extended_longident Grammar.Entry.e)),
           (fun (li : 'extended_longident) (loc : Ploc.t) ->
              (Qast.Node ("CtLong", [Qast.Loc; li]) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__213)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__213)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__213)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__213)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__213)))])),
           (fun (i : 'e__213) _ (li : 'extended_longident) (loc : Ploc.t) ->
              (Qast.Node ("CtLongLid", [Qast.Loc; li; i]) : 'class_type)))]];
    Grammar.extension (class_self_type : 'class_self_type Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'class_self_type)))]];
    Grammar.extension (class_sig_item : 'class_sig_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (Qast.Node ("CgExten", [Qast.Loc; e]) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (Qast.Node ("CgFlAtt", [Qast.Loc; attr]) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t2 : 'ctyp) _ (t1 : 'ctyp) _
                (loc : Ploc.t) ->
              (Qast.Node ("CgCtr", [Qast.Loc; t1; t2; attrs]) :
               'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "method")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "private"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__222)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__222)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__222)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__222)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__222)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__223)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__223)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__223)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__223)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__223)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'e__223)
                (pf : 'e__222) _ (loc : Ploc.t) ->
              (Qast.Node ("CgMth", [Qast.Loc; pf; l; t; attrs]) :
               'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "method")))
                            (Grammar.s_token ("", "virtual")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "private"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__220)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__220)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__220)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__220)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__220)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__221)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__221)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__221)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__221)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__221)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'e__221)
                (pf : 'e__220) _ _ (loc : Ploc.t) ->
              (Qast.Node ("CgVir", [Qast.Loc; pf; l; t; attrs]) :
               'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "value")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_flag
                                           (Grammar.s_token ("", "mutable"))),
                                      (fun (a : bool) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Bool a) :
                                          'e__217)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_opt")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_opt", loc, a) :
                                          'e__217)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "opt")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("opt", loc, a)) :
                                          'e__217)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_flag")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_flag", loc, a) :
                                          'e__217)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "flag")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("flag", loc, a)) :
                                          'e__217)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "virtual"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__218)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__218)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__218)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__218)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__218)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__219)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__219)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__219)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__219)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__219)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'e__219)
                (vf : 'e__218) (mf : 'e__217) _ (loc : Ploc.t) ->
              (Qast.Node ("CgVal", [Qast.Loc; mf; vf; l; t; attrs]) :
               'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "inherit")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (cs : 'class_type) _
                (loc : Ploc.t) ->
              (Qast.Node ("CgInh", [Qast.Loc; cs; attrs]) :
               'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (class_sig_item :
                                               'class_sig_item
                                                 Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (s : 'class_sig_item)
                                           (loc : Ploc.t) ->
                                         (s : 'e__215)))])),
                          (fun (a : 'e__215 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__216)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__216)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__216)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__216) _ (loc : Ploc.t) ->
              (Qast.Node ("CgDcl", [Qast.Loc; st]) : 'class_sig_item)))]];
    Grammar.extension (class_description : 'class_description Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_flag
                                           (Grammar.s_token ("", "virtual"))),
                                      (fun (a : bool) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Bool a) :
                                          'e__224)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_opt")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_opt", loc, a) :
                                          'e__224)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "opt")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("opt", loc, a)) :
                                          'e__224)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_flag")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_flag", loc, a) :
                                          'e__224)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "flag")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("flag", loc, a)) :
                                          'e__224)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("LIDENT", "")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Str a) : 'e__225)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__225)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__225)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_lid")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_lid", loc, a) :
                                       'e__225)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "lid")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("lid", loc, a)) :
                                       'e__225)))])))
                      (Grammar.s_nterm
                         (class_type_parameters :
                          'class_type_parameters Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (ct : 'class_type) _
                (ctp : 'class_type_parameters) (n : 'e__225) (vf : 'e__224)
                (loc : Ploc.t) ->
              (Qast.Record
                 ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", n;
                  "ciExp", ct; "ciAttributes", attrs] :
               'class_description)))]];
    Grammar.extension
      (class_type_declaration : 'class_type_declaration Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_flag
                                           (Grammar.s_token ("", "virtual"))),
                                      (fun (a : bool) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Bool a) :
                                          'e__226)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_opt")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_opt", loc, a) :
                                          'e__226)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "opt")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("opt", loc, a)) :
                                          'e__226)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_flag")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_flag", loc, a) :
                                          'e__226)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "flag")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("flag", loc, a)) :
                                          'e__226)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("LIDENT", "")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Str a) : 'e__227)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__227)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__227)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_lid")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_lid", loc, a) :
                                       'e__227)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "lid")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("lid", loc, a)) :
                                       'e__227)))])))
                      (Grammar.s_nterm
                         (class_type_parameters :
                          'class_type_parameters Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (cs : 'class_type) _
                (ctp : 'class_type_parameters) (n : 'e__227) (vf : 'e__226)
                (loc : Ploc.t) ->
              (Qast.Record
                 ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", n;
                  "ciExp", cs; "ciAttributes", attrs] :
               'class_type_declaration)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "apply"))
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "object")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (class_self_patt :
                                      'class_self_patt Grammar.Entry.e))),
                             (fun (a : 'class_self_patt option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__229)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__229)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__229)))])))
                (Grammar.s_nterm
                   (class_structure : 'class_structure Grammar.Entry.e)))
             (Grammar.s_token ("", "end")),
           (fun _ (cf : 'class_structure) (cspo : 'e__229) _ (loc : Ploc.t) ->
              (Qast.Node ("ExObj", [Qast.Loc; cspo; cf]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "new")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (class_longident :
                             'class_longident Grammar.Entry.e)),
                       (fun (a : 'class_longident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__228)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__228)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__228)))])),
           (fun (i : 'e__228) _ (loc : Ploc.t) ->
              (Qast.Node ("ExNew", [Qast.Loc; i]) : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "."))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "#")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)),
                       (fun (a : 'lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__230)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__230)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__230)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__230)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__230)))])),
           (fun (lab : 'e__230) _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExSnd", [Qast.Loc; e; lab]) : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{<")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (field_expr : 'field_expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'field_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__231)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__231)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__231)))])))
             (Grammar.s_token ("", ">}")),
           (fun _ (fel : 'e__231) _ (loc : Ploc.t) ->
              (Qast.Node ("ExOvr", [Qast.Loc; fel]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ":>")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option None; t]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "(")))
                            Grammar.s_self)
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", ":>")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t2 : 'ctyp) _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option (Some t); t2]) :
               'expr)))]];
    Grammar.extension (field_expr : 'field_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (l : 'lident) (loc : Ploc.t) ->
              (Qast.Tuple [l; e] : 'field_expr)))]];
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "<")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list0sep
                                  (Grammar.s_nterm
                                     (field : 'field Grammar.Entry.e))
                                  (Grammar.s_token ("", ";")) false),
                             (fun (a : 'field list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__233)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__233)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__233)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", ".."))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__234)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__234)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__234)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__234)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__234)))])))
             (Grammar.s_token ("", ">")),
           (fun _ (v : 'e__234) (ml : 'e__233) _ (loc : Ploc.t) ->
              (Qast.Node ("TyObj", [Qast.Loc; ml; v]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (class_longident :
                             'class_longident Grammar.Entry.e)),
                       (fun (a : 'class_longident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__232)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__232)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__232)))])),
           (fun (id : 'e__232) _ (loc : Ploc.t) ->
              (Qast.Node ("TyCls", [Qast.Loc; id]) : 'ctyp)))]];
    Grammar.extension (field : 'field Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("LIDENT", "")))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (lab : string) (loc : Ploc.t) ->
              (Qast.Tuple [mkident lab; t] : 'field)))]];
    Grammar.extension (class_longident : 'class_longident Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.List [mkident i] : 'class_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "")))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (l : 'class_longident) _ (m : string) (loc : Ploc.t) ->
              (Qast.Cons (mkident m, l) : 'class_longident)))]];
    (* Labels *)
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.After "arrow"))
      [None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_qic : 'a_qic Grammar.Entry.e)),
                          (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__236)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("QUESTIONIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__236)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("?_:", loc, a) : 'e__236)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                              'e__236)))])))
             Grammar.s_self,
           (fun (t : 'ctyp) (i : 'e__236) (loc : Ploc.t) ->
              (Qast.Node ("TyOlb", [Qast.Loc; i; t]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__235)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__235)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__235)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__235)))])))
             Grammar.s_self,
           (fun (t : 'ctyp) (i : 'e__235) (loc : Ploc.t) ->
              (Qast.Node ("TyLab", [Qast.Loc; i; t]) : 'ctyp)))]];
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "[")))
                         (Grammar.s_token ("", "<")))
                      (Grammar.s_nterm
                         (poly_variant_list :
                          'poly_variant_list Grammar.Entry.e)))
                   (Grammar.s_token ("", ">")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_nterm
                                  (name_tag : 'name_tag Grammar.Entry.e))),
                          (fun (a : 'name_tag list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__237)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__237)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__237)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (ntl : 'e__237) _ (rfl : 'poly_variant_list) _ _
                (loc : Ploc.t) ->
              (Qast.Node
                 ("TyVrn",
                  [Qast.Loc; rfl;
                   Qast.Option (Some (Qast.Option (Some ntl)))]) :
               'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_token ("", "<")))
                (Grammar.s_nterm
                   (poly_variant_list : 'poly_variant_list Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("TyVrn",
                  [Qast.Loc; rfl;
                   Qast.Option
                     (Some
                        (Qast.Option (Some (Qast.VaVal (Qast.List [])))))]) :
               'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_token ("", ">")))
                (Grammar.s_nterm
                   (poly_variant_list : 'poly_variant_list Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("TyVrn",
                  [Qast.Loc; rfl; Qast.Option (Some (Qast.Option None))]) :
               'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (poly_variant_list : 'poly_variant_list Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
              (Qast.Node ("TyVrn", [Qast.Loc; rfl; Qast.Option None]) :
               'ctyp)))]];
    Grammar.extension (poly_variant_list : 'poly_variant_list Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0sep
                            (Grammar.s_nterm
                               (poly_variant : 'poly_variant Grammar.Entry.e))
                            (Grammar.s_token ("", "|")) false),
                       (fun (a : 'poly_variant list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__238)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__238)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__238)))])),
           (fun (rfl : 'e__238) (loc : Ploc.t) ->
              (rfl : 'poly_variant_list)))]];
    Grammar.extension (poly_variant : 'poly_variant Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("PvInh", [Qast.Loc; t]) : 'poly_variant)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "`")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (ident : 'ident Grammar.Entry.e)),
                                   (fun (a : 'ident) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__240)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__240)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__240)))])))
                      (Grammar.s_token ("", "of")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_flag (Grammar.s_token ("", "&"))),
                             (fun (a : bool) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Bool a) : 'e__241)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__241)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__241)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_flag")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_flag", loc, a) : 'e__241)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "flag")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                 'e__241)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterml
                                  (ctyp : 'ctyp Grammar.Entry.e)
                                  "below_alg_attribute")
                               (Grammar.s_token ("", "&")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__242)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__242)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__242)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (l : 'e__242) (ao : 'e__241) _
                (i : 'e__240) _ (loc : Ploc.t) ->
              (Qast.Node ("PvTag", [Qast.Loc; i; ao; l; alg_attrs]) :
               'poly_variant)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (ident : 'ident Grammar.Entry.e)),
                          (fun (a : 'ident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__239)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__239)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__239)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (i : 'e__239) _
                (loc : Ploc.t) ->
              (Qast.Node
                 ("PvTag",
                  [Qast.Loc; i; Qast.VaVal (Qast.Bool true);
                   Qast.VaVal (Qast.List []); alg_attrs]) :
               'poly_variant)))]];
    Grammar.extension (name_tag : 'name_tag Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) -> (i : 'name_tag)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (patt_option_label : 'patt_option_label Grammar.Entry.e)),
           (fun (p : 'patt_option_label) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in p : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_ti : 'a_ti Grammar.Entry.e)),
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__249)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__249)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__249)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__249)))])),
           (fun (i : 'e__249) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option None)]])]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__248)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__248)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__248)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__248)))])))
             Grammar.s_self,
           (fun (p : 'patt) (i : 'e__248) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option (Some p))]])]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "?")))
                      (Grammar.s_token ("", "{")))
                   (Grammar.s_nterm (patt_tcon : 'patt_tcon Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("", "=")))
                                        (Grammar.s_nterm
                                           (expr : 'expr Grammar.Entry.e)),
                                      (fun (e : 'expr) _ (loc : Ploc.t) ->
                                         (e : 'e__246)))])),
                          (fun (a : 'e__246 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__247)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__247)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__247)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'e__247) (p : 'patt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaOlb", [Qast.Loc; p; eo]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (patt_tcon_opt_eq_patt :
                                   'patt_tcon_opt_eq_patt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'patt_tcon_opt_eq_patt list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__245)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__245)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__245)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lppo : 'e__245) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaLab", [Qast.Loc; lppo]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (mod_ident : 'mod_ident Grammar.Entry.e)),
                       (fun (a : 'mod_ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__244)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__244)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__244)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__244)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__244)))])),
           (fun (sl : 'e__244) _ (loc : Ploc.t) ->
              (Qast.Node ("PaTyp", [Qast.Loc; sl]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__243)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__243)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__243)))])),
           (fun (s : 'e__243) _ (loc : Ploc.t) ->
              (Qast.Node ("PaVrn", [Qast.Loc; s]) : 'patt)))]];
    Grammar.extension
      (patt_tcon_opt_eq_patt : 'patt_tcon_opt_eq_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (patt_tcon : 'patt_tcon Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("", "=")))
                                     (Grammar.s_nterm
                                        (patt : 'patt Grammar.Entry.e)),
                                   (fun (p : 'patt) _ (loc : Ploc.t) ->
                                      (p : 'e__250)))])),
                       (fun (a : 'e__250 option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__251)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__251)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__251)))])),
           (fun (po : 'e__251) (p : 'patt_tcon) (loc : Ploc.t) ->
              (Qast.Tuple [p; po] : 'patt_tcon_opt_eq_patt)))]];
    Grammar.extension (patt_tcon : 'patt_tcon Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'patt_tcon)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) (loc : Ploc.t) -> (p : 'patt_tcon)))]];
    Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (patt_option_label : 'patt_option_label Grammar.Entry.e)),
           (fun (p : 'patt_option_label) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in p : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_ti : 'a_ti Grammar.Entry.e)),
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__256)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__256)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__256)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__256)))])),
           (fun (i : 'e__256) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option None)]])]) :
               'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__255)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__255)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__255)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__255)))])))
             Grammar.s_self,
           (fun (p : 'ipatt) (i : 'e__255) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option (Some p))]])]) :
               'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "?")))
                      (Grammar.s_token ("", "{")))
                   (Grammar.s_nterm
                      (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("", "=")))
                                        (Grammar.s_nterm
                                           (expr : 'expr Grammar.Entry.e)),
                                      (fun (e : 'expr) _ (loc : Ploc.t) ->
                                         (e : 'e__253)))])),
                          (fun (a : 'e__253 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__254)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__254)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__254)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'e__254) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaOlb", [Qast.Loc; p; eo]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ipatt_tcon_opt_eq_patt :
                                   'ipatt_tcon_opt_eq_patt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'ipatt_tcon_opt_eq_patt list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__252)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__252)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__252)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lppo : 'e__252) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaLab", [Qast.Loc; lppo]) : 'ipatt)))]];
    Grammar.extension
      (ipatt_tcon_opt_eq_patt : 'ipatt_tcon_opt_eq_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("", "=")))
                                     (Grammar.s_nterm
                                        (patt : 'patt Grammar.Entry.e)),
                                   (fun (p : 'patt) _ (loc : Ploc.t) ->
                                      (p : 'e__257)))])),
                       (fun (a : 'e__257 option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__258)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__258)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__258)))])),
           (fun (po : 'e__258) (p : 'ipatt_tcon) (loc : Ploc.t) ->
              (Qast.Tuple [p; po] : 'ipatt_tcon_opt_eq_patt)))]];
    Grammar.extension (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'ipatt_tcon)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p : 'ipatt) (loc : Ploc.t) -> (p : 'ipatt_tcon)))]];
    Grammar.extension (patt_option_label : 'patt_option_label Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "?")))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__271)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__271)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__271)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__271)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__271)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (i : 'e__271) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option None)]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "?")))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__270)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__270)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__270)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__270)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__270)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (i : 'e__270) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option (Some e))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "?")))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__269)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__269)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__269)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__269)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__269)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (i : 'e__269) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc;
                   Qast.Node
                     ("PaTyc",
                      [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                   Qast.VaVal (Qast.Option None)]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "?")))
                               (Grammar.s_token ("", "(")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__268)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__268)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__268)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__268)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__268)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (i : 'e__268) _ _
                (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc;
                   Qast.Node
                     ("PaTyc",
                      [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                   Qast.VaVal (Qast.Option (Some e))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_qi : 'a_qi Grammar.Entry.e)),
                       (fun (a : 'a_qi) (loc : Ploc.t) -> (a : 'e__267)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("QUESTIONIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__267)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("?_", loc, a) : 'e__267)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("?", loc, a)) :
                           'e__267)))])),
           (fun (i : 'e__267) (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option None)]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (a_qic : 'a_qic Grammar.Entry.e)),
                                (fun (a : 'a_qic) (loc : Ploc.t) ->
                                   (a : 'e__265)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token
                                     ("QUESTIONIDENTCOLON", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__265)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "?_:")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("?_:", loc, a) : 'e__265)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "?:")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                                    'e__265)))])))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__266)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__266)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__266)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__266)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__266)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (j : 'e__266) _ (i : 'e__265) (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal
                     (Qast.Option
                        (Some (Qast.Node ("ExLid", [Qast.Loc; j]))))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (a_qic : 'a_qic Grammar.Entry.e)),
                                      (fun (a : 'a_qic) (loc : Ploc.t) ->
                                         (a : 'e__263)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("QUESTIONIDENTCOLON", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__263)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?_:")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("?_:", loc, a) :
                                          'e__263)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?:")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("?:", loc, a)) :
                                          'e__263)))])))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__264)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__264)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__264)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__264)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__264)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (j : 'e__264) _ (i : 'e__263)
                (loc : Ploc.t) ->
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
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (a_qic : 'a_qic Grammar.Entry.e)),
                                      (fun (a : 'a_qic) (loc : Ploc.t) ->
                                         (a : 'e__261)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("QUESTIONIDENTCOLON", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__261)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?_:")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("?_:", loc, a) :
                                          'e__261)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?:")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("?:", loc, a)) :
                                          'e__261)))])))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__262)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__262)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__262)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__262)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__262)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (j : 'e__262) _ (i : 'e__261)
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
                                Qast.VaVal (Qast.Option None)]))))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_facto
                                     (Grammar.s_rules
                                        [Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_nterm
                                                 (a_qic :
                                                  'a_qic Grammar.Entry.e)),
                                            (fun (a : 'a_qic)
                                                 (loc : Ploc.t) ->
                                               (a : 'e__259)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("QUESTIONIDENTCOLON", "")),
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaVal (Qast.Str a) :
                                                'e__259)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("ANTIQUOT", "?_:")),
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaAnt ("?_:", loc, a) :
                                                'e__259)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("ANTIQUOT", "?:")),
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaVal
                                                  (Qast.VaAnt
                                                     ("?:", loc, a)) :
                                                'e__259)))])))
                               (Grammar.s_token ("", "(")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__260)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__260)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__260)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__260)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__260)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (j : 'e__260) _ (i : 'e__259)
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
               'patt_option_label)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.After "apply"))
      [Some "label", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_qi : 'a_qi Grammar.Entry.e)),
                       (fun (a : 'a_qi) (loc : Ploc.t) -> (a : 'e__277)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("QUESTIONIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__277)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("?_", loc, a) : 'e__277)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("?", loc, a)) :
                           'e__277)))])),
           (fun (i : 'e__277) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option None)]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_qic : 'a_qic Grammar.Entry.e)),
                          (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__276)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("QUESTIONIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__276)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("?_:", loc, a) : 'e__276)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                              'e__276)))])))
             Grammar.s_self,
           (fun (e : 'expr) (i : 'e__276) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option (Some e))]) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_ti : 'a_ti Grammar.Entry.e)),
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__275)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__275)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__275)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__275)))])),
           (fun (i : 'e__275) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option None)]])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__274)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__274)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__274)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__274)))])))
             Grammar.s_self,
           (fun (e : 'expr) (i : 'e__274) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option (Some e))]])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "?")))
                      (Grammar.s_token ("", "{")))
                   (Grammar.s_nterm
                      (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_nterm
                                  (fun_binding :
                                   'fun_binding Grammar.Entry.e))),
                          (fun (a : 'fun_binding option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__273)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__273)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__273)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'e__273) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExOlb", [Qast.Loc; p; eo]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ipatt_tcon_fun_binding :
                                   'ipatt_tcon_fun_binding Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'ipatt_tcon_fun_binding list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__272)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__272)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__272)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lpeo : 'e__272) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExLab", [Qast.Loc; lpeo]) : 'expr)))]];
    Grammar.extension
      (ipatt_tcon_fun_binding : 'ipatt_tcon_fun_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm
                               (fun_binding : 'fun_binding Grammar.Entry.e))),
                       (fun (a : 'fun_binding option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__278)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__278)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__278)))])),
           (fun (eo : 'e__278) (p : 'ipatt_tcon) (loc : Ploc.t) ->
              (Qast.Tuple [p; eo] : 'ipatt_tcon_fun_binding)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__279)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__279)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__279)))])),
           (fun (s : 'e__279) _ (loc : Ploc.t) ->
              (Qast.Node ("ExVrn", [Qast.Loc; s]) : 'expr)))]];
    (* -- end copy from pa_r to q_MLast -- *)
    Grammar.extension (a_ti : 'a_ti Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
             (Grammar.s_token ("ANTIQUOT", "")),
           (fun (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("~", loc, a) : 'a_ti)))]];
    Grammar.extension (a_tic : 'a_tic Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                (Grammar.s_token ("ANTIQUOT", "")))
             (Grammar.s_token ("", ":")),
           (fun _ (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("~", loc, a) : 'a_tic)))]];
    Grammar.extension (a_qi : 'a_qi Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "?")))
             (Grammar.s_token ("ANTIQUOT", "")),
           (fun (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("?", loc, a) : 'a_qi)))]];
    Grammar.extension (a_qic : 'a_qic Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "?")))
                (Grammar.s_token ("ANTIQUOT", "")))
             (Grammar.s_token ("", ":")),
           (fun _ (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("?", loc, a) : 'a_qic)))]]]);;

(* Antiquotations *)

let antiquot_xtr loc n a =
  if !(Pcaml.strict_mode) then
    Qast.Node (n, [Qast.Loc; Qast.VaAnt ("xtr", loc, a); Qast.Option None])
  else Qast.Apply ("failwith", [Qast.Str "antiquotation not authorized"])
;;

Grammar.safe_extend
  [Grammar.extension (module_expr : 'module_expr Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'module_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "MeXtr" a : 'module_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "mexp")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("mexp", loc, a) : 'module_expr)))]];
   Grammar.extension
     (extended_longident : 'extended_longident Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "longid")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("longid", loc, a) : 'extended_longident)))]];
   Grammar.extension (str_item : 'str_item Grammar.Entry.e)
     (Some (Gramext.Level "top"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'str_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "StXtr" a : 'str_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "stri")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("stri", loc, a) : 'str_item)))]];
   Grammar.extension (module_type : 'module_type Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'module_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "MtXtr" a : 'module_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "mtyp")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("mtyp", loc, a) : 'module_type)))]];
   Grammar.extension (sig_item : 'sig_item Grammar.Entry.e)
     (Some (Gramext.Level "top"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'sig_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "SgXtr" a : 'sig_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "sigi")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("sigi", loc, a) : 'sig_item)))]];
   Grammar.extension (expr : 'expr Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("ExAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "ExXtr" a : 'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "exp")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("exp", loc, a) : 'expr)))]];
   Grammar.extension (patt : 'patt Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("PaAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "PaXtr" a : 'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "pat")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("pat", loc, a) : 'patt)))]];
   Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("PaAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "PaXtr" a : 'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "pat")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("pat", loc, a) : 'ipatt)))]];
   Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'ctyp)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "TyXtr" a : 'ctyp)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "typ")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("typ", loc, a) : 'ctyp)))]];
   Grammar.extension (class_expr : 'class_expr Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "CeXtr" a : 'class_expr)))]];
   Grammar.extension (class_str_item : 'class_str_item Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_str_item)))]];
   Grammar.extension (class_sig_item : 'class_sig_item Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_sig_item)))]];
   Grammar.extension (class_type : 'class_type Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "CtXtr" a : 'class_type)))]]];;

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

let attribute_body_eoi = Grammar.Entry.create gram "attribute_body_eoi" in
let sig_item_eoi = Grammar.Entry.create gram "sig_item_eoi" in
let str_item_eoi = Grammar.Entry.create gram "str_item_eoi" in
let ctyp_eoi = Grammar.Entry.create gram "ctyp_eoi" in
let patt_eoi = Grammar.Entry.create gram "patt_eoi" in
let expr_eoi = Grammar.Entry.create gram "expr_eoi" in
let module_type_eoi = Grammar.Entry.create gram "module_type_eoi" in
let extended_longident_eoi =
  Grammar.Entry.create gram "extended_longident_eoi"
in
let module_expr_eoi = Grammar.Entry.create gram "module_expr_eoi" in
let class_type_eoi = Grammar.Entry.create gram "class_type_eoi" in
let class_expr_eoi = Grammar.Entry.create gram "class_expr_eoi" in
let class_sig_item_eoi = Grammar.Entry.create gram "class_sig_item_eoi" in
let class_str_item_eoi = Grammar.Entry.create gram "class_str_item_eoi" in
let with_constr_eoi = Grammar.Entry.create gram "with_constr_eoi" in
let poly_variant_eoi = Grammar.Entry.create gram "poly_variant_eoi" in
let type_decl_eoi = Grammar.Entry.create gram "type_decl_eoi" in
let type_extension_eoi = Grammar.Entry.create gram "type_extension_eoi" in
let extension_constructor_eoi =
  Grammar.Entry.create gram "extension_constructor_eoi"
in
Grammar.safe_extend
  [Grammar.extension
     (attribute_body_eoi : 'attribute_body_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (attribute_body : 'attribute_body Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'attribute_body) (loc : Ploc.t) ->
             (x : 'attribute_body_eoi)))]];
   Grammar.extension (sig_item_eoi : 'sig_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (sig_item : 'sig_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'sig_item) (loc : Ploc.t) -> (x : 'sig_item_eoi)))]];
   Grammar.extension (str_item_eoi : 'str_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'str_item) (loc : Ploc.t) -> (x : 'str_item_eoi)))]];
   Grammar.extension (ctyp_eoi : 'ctyp_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'ctyp) (loc : Ploc.t) -> (x : 'ctyp_eoi)))]];
   Grammar.extension (patt_eoi : 'patt_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'patt) (loc : Ploc.t) -> (x : 'patt_eoi)))]];
   Grammar.extension (expr_eoi : 'expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'expr) (loc : Ploc.t) -> (x : 'expr_eoi)))]];
   Grammar.extension (module_type_eoi : 'module_type_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'module_type) (loc : Ploc.t) ->
             (x : 'module_type_eoi)))]];
   Grammar.extension (module_expr_eoi : 'module_expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'module_expr) (loc : Ploc.t) ->
             (x : 'module_expr_eoi)))]];
   Grammar.extension
     (extended_longident_eoi : 'extended_longident_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (extended_longident : 'extended_longident Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'extended_longident) (loc : Ploc.t) ->
             (x : 'extended_longident_eoi)))]];
   Grammar.extension (class_type_eoi : 'class_type_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'class_type) (loc : Ploc.t) ->
             (x : 'class_type_eoi)))]];
   Grammar.extension (class_expr_eoi : 'class_expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'class_expr) (loc : Ploc.t) ->
             (x : 'class_expr_eoi)))]];
   Grammar.extension
     (class_sig_item_eoi : 'class_sig_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (class_sig_item : 'class_sig_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'class_sig_item) (loc : Ploc.t) ->
             (x : 'class_sig_item_eoi)))]];
   Grammar.extension
     (class_str_item_eoi : 'class_str_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (class_str_item : 'class_str_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'class_str_item) (loc : Ploc.t) ->
             (x : 'class_str_item_eoi)))]];
   Grammar.extension (with_constr_eoi : 'with_constr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (with_constr : 'with_constr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'with_constr) (loc : Ploc.t) ->
             (x : 'with_constr_eoi)))]];
   Grammar.extension (poly_variant_eoi : 'poly_variant_eoi Grammar.Entry.e)
     None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (poly_variant : 'poly_variant Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'poly_variant) (loc : Ploc.t) ->
             (x : 'poly_variant_eoi)))]];
   Grammar.extension (type_decl_eoi : 'type_decl_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (type_decl : 'type_decl Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'type_decl) (loc : Ploc.t) -> (x : 'type_decl_eoi)))]];
   Grammar.extension
     (type_extension_eoi : 'type_extension_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (type_extension : 'type_extension Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'type_extension) (loc : Ploc.t) ->
             (x : 'type_extension_eoi)))]];
   Grammar.extension
     (extension_constructor_eoi : 'extension_constructor_eoi Grammar.Entry.e)
     None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (extension_constructor :
                   'extension_constructor Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'extension_constructor) (loc : Ploc.t) ->
             (x : 'extension_constructor_eoi)))]]];
List.iter (fun (q, f) -> Quotation.add q (f q))
  ["attribute_body", apply_entry attribute_body_eoi;
   "sig_item", apply_entry sig_item_eoi; "str_item", apply_entry str_item_eoi;
   "ctyp", apply_entry ctyp_eoi; "patt", apply_entry patt_eoi;
   "expr", apply_entry expr_eoi; "module_type", apply_entry module_type_eoi;
   "module_expr", apply_entry module_expr_eoi;
   "extended_longident", apply_entry extended_longident_eoi;
   "class_type", apply_entry class_type_eoi;
   "class_expr", apply_entry class_expr_eoi;
   "class_sig_item", apply_entry class_sig_item_eoi;
   "class_str_item", apply_entry class_str_item_eoi;
   "with_constr", apply_entry with_constr_eoi;
   "poly_variant", apply_entry poly_variant_eoi;
   "type_decl", apply_entry type_decl_eoi;
   "type_extension", apply_entry type_extension_eoi;
   "extension_constructor", apply_entry extension_constructor_eoi];;

let expr_eoi = Grammar.Entry.create Pcaml.gram "expr_eoi" in
Grammar.safe_extend
  [Grammar.extension (expr_eoi : 'expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_token ("ANTIQUOT_LOC", "")))
            (Grammar.s_token ("EOI", "")),
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
              'expr_eoi)));
       Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (Pcaml.expr : 'Pcaml__expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
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
              'expr_eoi)))]]];
let expr s =
  Ploc.call_with Plexer.force_antiquot_loc true (Grammar.Entry.parse expr_eoi)
    (Stream.of_string s)
in
let patt_eoi = Grammar.Entry.create Pcaml.gram "patt_eoi" in
Grammar.safe_extend
  [Grammar.extension (patt_eoi : 'patt_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_token ("ANTIQUOT_LOC", "")))
            (Grammar.s_token ("EOI", "")),
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
              'patt_eoi)));
       Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (Pcaml.patt : 'Pcaml__patt Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
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
              'patt_eoi)))]]];
let patt s =
  Ploc.call_with Plexer.force_antiquot_loc true (Grammar.Entry.parse patt_eoi)
    (Stream.of_string s)
in
Quotation.add "vala" (Quotation.ExAst (expr, patt));;
