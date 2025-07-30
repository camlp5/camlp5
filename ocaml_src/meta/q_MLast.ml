(* camlp5r *)
(* q_MLast.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "pa_extend_m.cmo" *)
(* #load "q_MLast.cmo" *)
(* #load "pa_macro.cmo" *)

open Asttools;;
open Mlsyntax.Original;;

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
      let l = Versdep.split_on_char '.' n in
      let li =
        match m, l with
          "", [n] -> MLast.LiUid (loc, n)
        | m, [n] -> MLast.LiAcc (loc, MLast.LiUid (loc, m), n)
        | _, _ :: _ -> longident_of_string_list loc l
        | _, [] -> assert false
      in
      MLast.ExLong (loc, li)
    ;;
    let patt_node m n =
      let l = Versdep.split_on_char '.' n in
      let li =
        match m, l with
          "", [n] -> MLast.LiUid (loc, n)
        | m, [n] -> MLast.LiAcc (loc, MLast.LiUid (loc, m), n)
        | _, _ :: _ -> longident_of_string_list loc l
        | _, [] -> assert false
      in
      MLast.PaLong (loc, li, [])
    ;;
    let patt_label m n =
      if m = "" then MLast.PaLid (loc, n)
      else MLast.PaPfx (loc, MLast.LiUid (loc, m), MLast.PaLid (loc, n))
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
                  MLast.ExApp
                    (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")),
                     to_expr m a),
                  e))
            al (MLast.ExLong (loc, MLast.LiUid (loc, "[]")))
      | Tuple al -> MLast.ExTup (loc, List.map (to_expr m) al)
      | Option None -> MLast.ExLong (loc, MLast.LiUid (loc, "None"))
      | Option (Some a) ->
          MLast.ExApp
            (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")), to_expr m a)
      | Int s -> MLast.ExInt (loc, s, "")
      | Str s -> MLast.ExStr (loc, (loc, s))
      | Bool true -> MLast.ExLong (loc, MLast.LiUid (loc, "True"))
      | Bool false -> MLast.ExLong (loc, MLast.LiUid (loc, "False"))
      | Cons (a1, a2) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")),
                to_expr m a1),
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
                     MLast.ExLong
                       (loc,
                        MLast.LiAcc
                          (loc, MLast.LiUid (loc, "Ploc"), "VaVal")),
                     ee)
                in
                let loc = MLast.loc_of_expr e in MLast.ExAnt (loc, ee)
            | _ ->
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaVal")),
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
                  MLast.PaApp
                    (loc, MLast.PaLong (loc, MLast.LiUid (loc, "::"), []),
                     to_patt m a),
                  p))
            al (MLast.PaLong (loc, MLast.LiUid (loc, "[]"), []))
      | Tuple al -> MLast.PaTup (loc, List.map (to_patt m) al, true)
      | Option None -> MLast.PaLong (loc, MLast.LiUid (loc, "None"), [])
      | Option (Some a) ->
          MLast.PaApp
            (loc, MLast.PaLong (loc, MLast.LiUid (loc, "Some"), []),
             to_patt m a)
      | Int s -> MLast.PaInt (loc, s, "")
      | Str s -> MLast.PaStr (loc, s)
      | Bool true -> MLast.PaLong (loc, MLast.LiUid (loc, "True"), [])
      | Bool false -> MLast.PaLong (loc, MLast.LiUid (loc, "False"), [])
      | Cons (a1, a2) ->
          MLast.PaApp
            (loc,
             MLast.PaApp
               (loc, MLast.PaLong (loc, MLast.LiUid (loc, "::"), []),
                to_patt m a1),
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
                     MLast.PaLong
                       (loc,
                        MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaVal"),
                        []),
                     pp)
                in
                let loc = MLast.loc_of_patt p in MLast.PaAnt (loc, pp)
            | _ ->
                MLast.PaApp
                  (loc,
                   MLast.PaLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaVal"),
                      []),
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
let longident = Grammar.Entry.create gram "longident";;
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
            Qast.Node
              ("ExLong",
               [Qast.Loc;
                Qast.Node ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")])])
        | a -> a
        end
    | e1 :: el ->
        Qast.Node
          ("ExApp",
           [Qast.Loc;
            Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node
                  ("ExLong",
                   [Qast.Loc;
                    Qast.Node
                      ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "::")])]);
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
            Qast.Node
              ("PaLong",
               [Qast.Loc;
                Qast.Node ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")]);
                Qast.VaVal (Qast.List [])])
        | a -> a
        end
    | p1 :: pl ->
        Qast.Node
          ("PaApp",
           [Qast.Loc;
            Qast.Node
              ("PaApp",
               [Qast.Loc;
                Qast.Node
                  ("PaLong",
                   [Qast.Loc;
                    Qast.Node
                      ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "::")]);
                    Qast.VaVal (Qast.List [])]);
                p1]);
            loop false pl])
  in
  loop true
;;

let mktupexp _ e el =
  Qast.Node ("ExTup", [Qast.Loc; Qast.VaVal (Qast.Cons (e, Qast.List el))])
;;

let mktuppat _ p pl clflag =
  Qast.Node
    ("PaTup",
     [Qast.Loc; Qast.VaVal (Qast.Cons (p, Qast.List pl));
      Qast.VaVal (Qast.Bool clflag)])
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
    | Some ("", "=" | "", ":=" | "", ";" | "", ";;") -> true
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

let check_uident_coloneq_f strm =
  match stream_npeek 2 strm with
    ["UIDENT", _; "", ":="] -> ()
  | ["ANTIQUOT", qs; "", ":="]
    when prefix_eq "uid:" qs || prefix_eq "_uid:" qs ->
      ()
  | _ -> raise Stream.Failure
;;

let check_uident_coloneq =
  Grammar.Entry.of_parser gram "check_uident_coloneq" check_uident_coloneq_f
;;

let dotop =
  Grammar.Entry.of_parser gram "dotop"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_dotop x -> Stream.junk strm__; Qast.Str x
       | _ -> raise Stream.Failure)
;;

let is_lparen_f strm =
  match Stream.npeek 1 strm with
    ["", "("] -> true
  | _ -> false
;;

let is_lparen_type_f strm =
  is_lparen_f strm &&
  (match Stream.npeek 2 strm with
     ["", "("; "", "type"] -> true
   | _ -> false)
;;

let check_lparen_type_f strm =
  if is_lparen_type_f strm then () else raise Stream.Failure
;;

let check_lparen_type =
  Grammar.Entry.of_parser gram "check_lparen_type" check_lparen_type_f
;;

let is_type_binder_f strm = check_fsm type_binder_fsm strm;;

let check_type_binder_f strm =
  if is_type_binder_f strm then () else raise Stream.Failure
;;

let check_type_binder =
  Grammar.Entry.of_parser gram "check_type_binder" check_type_binder_f
;;

let is_lident_colon_f strm =
  match Stream.npeek 2 strm with
    ("LIDENT", _) :: ("", ":") :: _ -> true
  | _ -> false
;;

let check_lident_colon_f strm =
  if is_lident_colon_f strm then () else raise Stream.Failure
;;

let check_lident_colon =
  Grammar.Entry.of_parser gram "check_lident_colon" check_lident_colon_f
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
   and _ = (longident : 'longident Grammar.Entry.e)
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
   and _ = (ctyp_ident : 'ctyp_ident Grammar.Entry.e)
   and _ = (check_type_binder : 'check_type_binder Grammar.Entry.e) in
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
   and type_binder_opt : 'type_binder_opt Grammar.Entry.e =
     grammar_entry_create "type_binder_opt"
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
   and patt_ident : 'patt_ident Grammar.Entry.e =
     grammar_entry_create "patt_ident"
   and tuple_patt_body1 : 'tuple_patt_body1 Grammar.Entry.e =
     grammar_entry_create "tuple_patt_body1"
   and tuple_patt_body : 'tuple_patt_body Grammar.Entry.e =
     grammar_entry_create "tuple_patt_body"
   and paren_patt : 'paren_patt Grammar.Entry.e =
     grammar_entry_create "paren_patt"
   and cons_patt_opt : 'cons_patt_opt Grammar.Entry.e =
     grammar_entry_create "cons_patt_opt"
   and label_patt : 'label_patt Grammar.Entry.e =
     grammar_entry_create "label_patt"
   and patt_label_ident : 'patt_label_ident Grammar.Entry.e =
     grammar_entry_create "patt_label_ident"
   and tuple_ipatt_body1 : 'tuple_ipatt_body1 Grammar.Entry.e =
     grammar_entry_create "tuple_ipatt_body1"
   and tuple_ipatt_body : 'tuple_ipatt_body Grammar.Entry.e =
     grammar_entry_create "tuple_ipatt_body"
   and paren_ipatt : 'paren_ipatt Grammar.Entry.e =
     grammar_entry_create "paren_ipatt"
   and label_ipatt : 'label_ipatt Grammar.Entry.e =
     grammar_entry_create "label_ipatt"
   and type_patt : 'type_patt Grammar.Entry.e =
     grammar_entry_create "type_patt"
   and constrain : 'constrain Grammar.Entry.e =
     grammar_entry_create "constrain"
   and type_variance : 'type_variance Grammar.Entry.e =
     grammar_entry_create "type_variance"
   and type_parameter : 'type_parameter Grammar.Entry.e =
     grammar_entry_create "type_parameter"
   and simple_type_parameter : 'simple_type_parameter Grammar.Entry.e =
     grammar_entry_create "simple_type_parameter"
   and maybe_labeled_ctyp : 'maybe_labeled_ctyp Grammar.Entry.e =
     grammar_entry_create "maybe_labeled_ctyp"
   and cons_ident : 'cons_ident Grammar.Entry.e =
     grammar_entry_create "cons_ident"
   and rest_constructor_declaration : 'rest_constructor_declaration Grammar.Entry.e =
     grammar_entry_create "rest_constructor_declaration"
   and ident : 'ident Grammar.Entry.e = grammar_entry_create "ident"
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
   and longident_lident : 'longident_lident Grammar.Entry.e =
     grammar_entry_create "longident_lident"
   and extended_longident_lident : 'extended_longident_lident Grammar.Entry.e =
     grammar_entry_create "extended_longident_lident"
   and poly_variant_list : 'poly_variant_list Grammar.Entry.e =
     grammar_entry_create "poly_variant_list"
   and name_tag : 'name_tag Grammar.Entry.e = grammar_entry_create "name_tag"
   and patt_tcon : 'patt_tcon Grammar.Entry.e =
     grammar_entry_create "patt_tcon"
   and ipatt_tcon : 'ipatt_tcon Grammar.Entry.e =
     grammar_entry_create "ipatt_tcon"
   and patt_option_label : 'patt_option_label Grammar.Entry.e =
     grammar_entry_create "patt_option_label"
   and a_ti : 'a_ti Grammar.Entry.e =
     (* -- end copy from pa_r to q_MLast -- *)
     grammar_entry_create "a_ti"
   and a_tic : 'a_tic Grammar.Entry.e = grammar_entry_create "a_tic"
   and a_qi : 'a_qi Grammar.Entry.e = grammar_entry_create "a_qi"
   and a_qic : 'a_qic Grammar.Entry.e = grammar_entry_create "a_qic" in
   [Grammar.extension (attribute_id : 'attribute_id Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("STRING", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; Qast.Str s] : 'attribute_id)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       "194fe98d",
                       (fun (i : string) (loc : Ploc.t) -> (i : 'e__1)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (i : string) (loc : Ploc.t) -> (i : 'e__1)))])
                (Grammar.s_token ("", ".")) false),
           "194fe98d",
           (fun (l : 'e__1 list) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; Qast.Str (String.concat "." l)] :
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
                                   "194fe98d",
                                   (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                      (s : 'e__2)))])),
                       "194fe98d",
                       (fun (a : 'e__2 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__3)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_structure")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_structure", loc, a) : 'e__3)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "structure")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("structure", loc, a)) :
                           'e__3)))])),
           "194fe98d",
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
                                   "194fe98d",
                                   (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                      (s : 'e__4)))])),
                       "194fe98d",
                       (fun (a : 'e__4 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__5)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_signature")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_signature", loc, a) : 'e__5)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "signature")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("signature", loc, a)) :
                           'e__5)))])),
           "194fe98d",
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
                                   "194fe98d",
                                   (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__13)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token
                                        ("ANTIQUOT", "_attrid")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_attrid", loc, a) :
                                       'e__13)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "attrid")),
                                   "194fe98d",
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
                             "194fe98d",
                             (fun (a : 'patt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__14)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_patt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_patt", loc, a) : 'e__14)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "patt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("patt", loc, a)) :
                                 'e__14)))])))
                (Grammar.s_token ("", "when")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'expr) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__15)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_expr")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_expr", loc, a) : 'e__15)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "expr")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("expr", loc, a)) :
                           'e__15)))])),
           "194fe98d",
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
                             "194fe98d",
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__11)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__11)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__11)))])))
                (Grammar.s_token ("", "?")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'patt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__12)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_patt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_patt", loc, a) : 'e__12)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "patt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("patt", loc, a)) :
                           'e__12)))])),
           "194fe98d",
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
                             "194fe98d",
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__9)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__9)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__9)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'ctyp) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__10)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_type")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_type", loc, a) : 'e__10)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "type")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("type", loc, a)) :
                           'e__10)))])),
           "194fe98d",
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
                             "194fe98d",
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__8)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__8)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__8)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm
                (attribute_signature : 'attribute_signature Grammar.Entry.e)),
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : 'attribute_id) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__7)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_attrid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_attrid", loc, a) : 'e__7)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "attrid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                           'e__7)))])),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_id) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__6)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attrid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attrid", loc, a) : 'e__6)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attrid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                              'e__6)))])))
             (Grammar.s_nterm
                (attribute_structure : 'attribute_structure Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__16)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__16)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__16)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__17)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__17)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__17)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__18)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__18)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__18)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__19)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_itemattrs")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_itemattrs", loc, a) : 'e__19)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "itemattrs")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("itemattrs", loc, a)) :
                           'e__19)))])),
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__20)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_algattrs")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_algattrs", loc, a) : 'e__20)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "algattrs")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("algattrs", loc, a)) :
                           'e__20)))])),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__21)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_extension")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_extension", loc, a) : 'e__21)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "extension")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("extension", loc, a)) :
                              'e__21)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__22)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_extension")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_extension", loc, a) : 'e__22)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "extension")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("extension", loc, a)) :
                              'e__22)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (e : 'e__22) _ (loc : Ploc.t) -> (e : 'alg_extension)))]];
    Grammar.extension (functor_parameter : 'functor_parameter Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
                                "194fe98d",
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__23)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__23)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__23)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
                             "194fe98d",
                             (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__24)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_fp")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_fp", loc, a) : 'e__24)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "fp")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                                 'e__24)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "_functor_parameter")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_functor_parameter", loc, a) :
                                 'e__24)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "functor_parameter")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.VaAnt
                                      ("functor_parameter", loc, a)) :
                                 'e__24)))])))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__25)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__25)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__25)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
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
           "194fe98d",
           (fun _ (st : 'structure) _ (loc : Ploc.t) ->
              (Qast.Node ("MeStr", [Qast.Loc; st]) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           "194fe98d",
           (fun (me2 : 'module_expr) (me1 : 'module_expr) (loc : Ploc.t) ->
              (Qast.Node ("MeApp", [Qast.Loc; me1; me2]) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           "194fe98d",
           (fun (me2 : 'module_expr) _ (me1 : 'module_expr) (loc : Ploc.t) ->
              (Qast.Node ("MeAcc", [Qast.Loc; me1; me2]) : 'module_expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("MeExten", [Qast.Loc; e]) : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__26)))])),
           "194fe98d",
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
                                   "194fe98d",
                                   (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                      (s : 'e__27)))])),
                       "194fe98d",
                       (fun (a : 'e__27 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__28)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__28)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__28)))])),
           "194fe98d",
           (fun (st : 'e__28) (loc : Ploc.t) -> (st : 'structure)))]];
    Grammar.extension (type_binder_opt : 'type_binder_opt Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) ->
              (Qast.VaVal (Qast.List []) : 'type_binder_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (check_type_binder :
                       'check_type_binder Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_nterm
                                  (typevar : 'typevar Grammar.Entry.e))),
                          "194fe98d",
                          (fun (a : 'typevar list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__29)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__29)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__29)))])))
             (Grammar.s_token ("", ".")),
           "194fe98d",
           (fun _ (ls : 'e__29) _ (loc : Ploc.t) ->
              (ls : 'type_binder_opt)))]];
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__30)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__30)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__30)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__30) _ (si : 'str_item) (loc : Ploc.t) ->
              (Qast.Node ("StAtt", [Qast.Loc; si; attr]) : 'str_item)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (item_extension : 'item_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (e : 'item_extension)
                (loc : Ploc.t) ->
              (Qast.Node ("StExten", [Qast.Loc; e; attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           "194fe98d",
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (Qast.Node ("StFlAtt", [Qast.Loc; attr]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__46)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_str")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_str", loc, a) : 'e__46)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "str")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                              'e__46)))])))
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
                                   "194fe98d",
                                   (fun (si : 'str_item) (loc : Ploc.t) ->
                                      (Qast.Tuple [si; Qast.Loc] :
                                       'e__47)))])),
                       "194fe98d",
                       (fun (a : 'e__47 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__48)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__48)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__48)))])),
           "194fe98d",
           (fun (sil : 'e__48) (s : 'e__46) _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__44)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__44)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__44)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__44)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__44)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
                       "194fe98d",
                       (fun (a : 'expr option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__45)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__45)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__45)))])),
           "194fe98d",
           (fun (dp : 'e__45) (n : 'e__44) _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__42)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__42)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__42)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__42)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__42)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (let_binding : 'let_binding Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       "194fe98d",
                       (fun (a : 'let_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__43)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__43)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__43)))])),
           "194fe98d",
           (fun (l : 'e__43) (r : 'e__42) _ (loc : Ploc.t) ->
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
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__40)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__40)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__40)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__40)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__40)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (type_decl : 'type_decl Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       "194fe98d",
                       (fun (a : 'type_decl list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__41)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__41)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__41)))])),
           "194fe98d",
           (fun (tdl : 'e__41) (nrfl : 'e__40) _ _ (loc : Ploc.t) ->
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
                             "194fe98d",
                             (fun (a : bool) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Bool a) : 'e__39)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_!")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_!", loc, a) : 'e__39)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "!")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                 'e__39)))])))
                (Grammar.s_nterm
                   (module_expr : 'module_expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (me : 'module_expr) (ovf : 'e__39)
                _ (loc : Ploc.t) ->
              (Qast.Node ("StOpn", [Qast.Loc; ovf; me; attrs]) : 'str_item)));
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
                                "194fe98d",
                                (fun (a : 'ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__38)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__38)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__38)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__36)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__36)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__36)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__36)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          "194fe98d",
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
                       "194fe98d",
                       (fun (a : 'mod_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__37)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__37)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__37)))])),
           "194fe98d",
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
           "194fe98d",
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
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "external")))
                               (Grammar.s_facto
                                  (Grammar.s_rules
                                     [Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("LIDENT", "")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal (Qast.Str a) :
                                             'e__34)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "_")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaAnt ("_", loc, a) :
                                             'e__34)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("ANTIQUOT", "")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal
                                               (Qast.VaAnt ("", loc, a)) :
                                             'e__34)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "_lid")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaAnt ("_lid", loc, a) :
                                             'e__34)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "lid")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal
                                               (Qast.VaAnt ("lid", loc, a)) :
                                             'e__34)))])))
                            (Grammar.s_token ("", ":")))
                         (Grammar.s_nterm
                            (type_binder_opt :
                             'type_binder_opt Grammar.Entry.e)))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_token ("STRING", ""))),
                          "194fe98d",
                          (fun (a : string list) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.List
                                   (List.map (fun a -> Qast.Str a) a)) :
                              'e__35)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__35)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__35)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (pd : 'e__35) _ (t : 'ctyp)
                (ls : 'type_binder_opt) _ (i : 'e__34) _ (loc : Ploc.t) ->
              (Qast.Node ("StExt", [Qast.Loc; i; ls; t; pd; attrs]) :
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
                          "194fe98d",
                          (fun (a : 'extension_constructor) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__33)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_excon")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_excon", loc, a) : 'e__33)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "excon")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("excon", loc, a)) :
                              'e__33)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
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
                                      "194fe98d",
                                      (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                         (s : 'e__31)))])),
                          "194fe98d",
                          (fun (a : 'e__31 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__32)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__32)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__32)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (st : 'e__32) _ (loc : Ploc.t) ->
              (Qast.Node ("StDcl", [Qast.Loc; st]) : 'str_item)))]];
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
                             "194fe98d",
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__49)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__49)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__49)))])))
                (Grammar.s_nterm
                   (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (me : 'mod_fun_binding)
                (i : 'e__49) (loc : Ploc.t) ->
              (Qast.Tuple [i; me; attrs] : 'mod_binding)))]];
    Grammar.extension (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)
      None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__50)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_fp")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_fp", loc, a) : 'e__50)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "fp")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                              'e__50)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "_functor_parameter")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_functor_parameter", loc, a) :
                              'e__50)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "functor_parameter")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.VaAnt ("functor_parameter", loc, a)) :
                              'e__50)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (mb : 'mod_fun_binding) (arg : 'e__50) (loc : Ploc.t) ->
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
                             "194fe98d",
                             (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__51)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_fp")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_fp", loc, a) : 'e__51)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "fp")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                                 'e__51)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "_functor_parameter")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_functor_parameter", loc, a) :
                                 'e__51)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "functor_parameter")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.VaAnt
                                      ("functor_parameter", loc, a)) :
                                 'e__51)))])))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           "194fe98d",
           (fun (mt : 'module_type) _ (arg : 'e__51) _ (loc : Ploc.t) ->
              (Qast.Node ("MtFun", [Qast.Loc; arg; mt]) : 'module_type)))];
       Some "->", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__52)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__52)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__52)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__52) _ (e : 'module_type) (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : 'with_constr list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__53)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__53)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__53)))])),
           "194fe98d",
           (fun (wcl : 'e__53) _ (mt : 'module_type) (loc : Ploc.t) ->
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (sg : 'signature) _ (loc : Ploc.t) ->
              (Qast.Node ("MtSig", [Qast.Loc; sg]) : 'module_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__56)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__56)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__56)))])),
           "194fe98d",
           (fun (i : 'e__56) _ (loc : Ploc.t) ->
              (Qast.Node ("MtQuo", [Qast.Loc; i]) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("MtExten", [Qast.Loc; e]) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__55)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__55)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__55)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__55)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__55)))])),
           "194fe98d",
           (fun (i : 'e__55) (loc : Ploc.t) ->
              (Qast.Node ("MtLid", [Qast.Loc; i]) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (extended_longident : 'extended_longident Grammar.Entry.e)),
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__54)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__54)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__54)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__54)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__54)))])),
           "194fe98d",
           (fun (i : 'e__54) _ (li : 'extended_longident) (loc : Ploc.t) ->
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
                                   "194fe98d",
                                   (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                      (s : 'e__57)))])),
                       "194fe98d",
                       (fun (a : 'e__57 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__58)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__58)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__58)))])),
           "194fe98d",
           (fun (st : 'e__58) (loc : Ploc.t) -> (st : 'signature)))]];
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__59)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__59)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__59)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__59) _ (si : 'sig_item) (loc : Ploc.t) ->
              (Qast.Node ("SgAtt", [Qast.Loc; si; attr]) : 'sig_item)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (item_extension : 'item_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (e : 'item_extension)
                (loc : Ploc.t) ->
              (Qast.Node ("SgExten", [Qast.Loc; e; attrs]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__76)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_str")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_str", loc, a) : 'e__76)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "str")),
                          "194fe98d",
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
                                   "194fe98d",
                                   (fun (si : 'sig_item) (loc : Ploc.t) ->
                                      (Qast.Tuple [si; Qast.Loc] :
                                       'e__77)))])),
                       "194fe98d",
                       (fun (a : 'e__77 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__78)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__78)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__78)))])),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__74)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__74)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__74)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__74)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__74)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
                       "194fe98d",
                       (fun (a : 'expr option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__75)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__75)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__75)))])),
           "194fe98d",
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
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__73)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__73)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__73)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__73)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__73)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (te : 'type_extension) _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgTypExten", [Qast.Loc; te]) : 'sig_item)));
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
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__71)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__71)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__71)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__71)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__71)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (type_decl : 'type_decl Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       "194fe98d",
                       (fun (a : 'type_decl list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__72)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__72)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__72)))])),
           "194fe98d",
           (fun (tdl : 'e__72) (nrfl : 'e__71) _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgTyp", [Qast.Loc; nrfl; tdl]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "open")))
                (Grammar.s_nterm
                   (extended_longident :
                    'extended_longident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (i : 'extended_longident) _
                (loc : Ploc.t) ->
              (Qast.Node ("SgOpn", [Qast.Loc; i; attrs]) : 'sig_item)));
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
                                "194fe98d",
                                (fun (a : 'ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__70)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__70)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__70)))])))
                   (Grammar.s_token ("", ":=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (mt : 'module_type) _ (i : 'e__70)
                _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgMtySubst", [Qast.Loc; i; mt; attrs]) :
               'sig_item)));
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
                                "194fe98d",
                                (fun (a : 'ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__69)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__69)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__69)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (mt : 'module_type) _ (i : 'e__69)
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
                         (Grammar.s_nterm
                            (check_uident_coloneq :
                             'check_uident_coloneq Grammar.Entry.e)))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("UIDENT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__68)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uid", loc, a) : 'e__68)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                    'e__68)))])))
                   (Grammar.s_token ("", ":=")))
                (Grammar.s_nterm
                   (extended_longident :
                    'extended_longident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (li : 'extended_longident) _
                (i : 'e__68) _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgModSubst", [Qast.Loc; i; li; attrs]) :
               'sig_item)));
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
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__66)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uid", loc, a) : 'e__66)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                    'e__66)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (longident : 'longident Grammar.Entry.e)),
                          "194fe98d",
                          (fun (a : 'longident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__67)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_longid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_longid", loc, a) : 'e__67)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "longid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("longid", loc, a)) :
                              'e__67)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (li : 'e__67) _ (i : 'e__66) _ _
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
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__64)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__64)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__64)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__64)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__64)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (mod_decl_binding :
                                'mod_decl_binding Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       "194fe98d",
                       (fun (a : 'mod_decl_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__65)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__65)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__65)))])),
           "194fe98d",
           (fun (l : 'e__65) (rf : 'e__64) _ (loc : Ploc.t) ->
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
           "194fe98d",
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
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "external")))
                               (Grammar.s_facto
                                  (Grammar.s_rules
                                     [Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("LIDENT", "")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal (Qast.Str a) :
                                             'e__62)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "_")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaAnt ("_", loc, a) :
                                             'e__62)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("ANTIQUOT", "")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal
                                               (Qast.VaAnt ("", loc, a)) :
                                             'e__62)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "_lid")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaAnt ("_lid", loc, a) :
                                             'e__62)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "lid")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal
                                               (Qast.VaAnt ("lid", loc, a)) :
                                             'e__62)))])))
                            (Grammar.s_token ("", ":")))
                         (Grammar.s_nterm
                            (type_binder_opt :
                             'type_binder_opt Grammar.Entry.e)))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_token ("STRING", ""))),
                          "194fe98d",
                          (fun (a : string list) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.List
                                   (List.map (fun a -> Qast.Str a) a)) :
                              'e__63)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__63)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__63)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (pd : 'e__63) _ (t : 'ctyp)
                (ls : 'type_binder_opt) _ (i : 'e__62) _ (loc : Ploc.t) ->
              (Qast.Node ("SgExt", [Qast.Loc; i; ls; t; pd; attrs]) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "exception")))
                (Grammar.s_nterm
                   (constructor_declaration :
                    'constructor_declaration Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (item_attrs : 'item_attributes)
                (ctl : 'constructor_declaration) _ (loc : Ploc.t) ->
              (Qast.Node ("SgExc", [Qast.Loc; ctl; item_attrs]) :
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
                                      "194fe98d",
                                      (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                         (s : 'e__60)))])),
                          "194fe98d",
                          (fun (a : 'e__60 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__61)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__61)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__61)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (st : 'e__61) _ (loc : Ploc.t) ->
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
                             "194fe98d",
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__79)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__79)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__79)))])))
                (Grammar.s_nterm
                   (module_declaration :
                    'module_declaration Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_fp")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_fp", loc, a) : 'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "fp")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                              'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "_functor_parameter")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_functor_parameter", loc, a) :
                              'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "functor_parameter")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.VaAnt ("functor_parameter", loc, a)) :
                              'e__80)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (mt : 'module_declaration) (arg : 'e__80) (loc : Ploc.t) ->
              (Qast.Node ("MtFun", [Qast.Loc; arg; mt]) :
               'module_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           "194fe98d",
           (fun (mt : 'module_type) _ (loc : Ploc.t) ->
              (mt : 'module_declaration)))]];
    Grammar.extension (with_constr : 'with_constr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
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
                                  (longident : 'longident Grammar.Entry.e)),
                             "194fe98d",
                             (fun (a : 'longident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__89)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_longid", loc, a) : 'e__89)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("longid", loc, a)) :
                                 'e__89)))])))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           "194fe98d",
           (fun (mt : 'module_type) _ (i : 'e__89) _ _ (loc : Ploc.t) ->
              (Qast.Node ("WcMts", [Qast.Loc; i; mt]) : 'with_constr)));
        Grammar.production
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
                                  (longident : 'longident Grammar.Entry.e)),
                             "194fe98d",
                             (fun (a : 'longident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__88)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_longid", loc, a) : 'e__88)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("longid", loc, a)) :
                                 'e__88)))])))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           "194fe98d",
           (fun (mt : 'module_type) _ (i : 'e__88) _ _ (loc : Ploc.t) ->
              (Qast.Node ("WcMty", [Qast.Loc; i; mt]) : 'with_constr)));
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
                                  (longident : 'longident Grammar.Entry.e)),
                             "194fe98d",
                             (fun (a : 'longident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_longid", loc, a) : 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("longid", loc, a)) :
                                 'e__87)))])))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           "194fe98d",
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
                                  (longident : 'longident Grammar.Entry.e)),
                             "194fe98d",
                             (fun (a : 'longident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_longid", loc, a) : 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("longid", loc, a)) :
                                 'e__86)))])))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           "194fe98d",
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
                                     (longident_lident :
                                      'longident_lident Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'longident_lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lilongid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lilongid", loc, a) :
                                    'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lilongid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("lilongid", loc, a)) :
                                    'e__84)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list0
                                  (Grammar.s_nterm
                                     (type_parameter :
                                      'type_parameter Grammar.Entry.e))),
                             "194fe98d",
                             (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__85)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__85)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__85)))])))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp) _ (tpl : 'e__85) (lili : 'e__84) _
                (loc : Ploc.t) ->
              (Qast.Node ("WcTys", [Qast.Loc; lili; tpl; t]) :
               'with_constr)));
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
                                        (longident_lident :
                                         'longident_lident Grammar.Entry.e)),
                                   "194fe98d",
                                   (fun (a : 'longident_lident)
                                        (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token
                                        ("ANTIQUOT", "_lilongid")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_lilongid", loc, a) :
                                       'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token
                                        ("ANTIQUOT", "lilongid")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("lilongid", loc, a)) :
                                       'e__81)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_list0
                                     (Grammar.s_nterm
                                        (type_parameter :
                                         'type_parameter Grammar.Entry.e))),
                                "194fe98d",
                                (fun (a : 'type_parameter list)
                                     (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.List a) : 'e__82)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_list")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_list", loc, a) : 'e__82)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "list")),
                                "194fe98d",
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
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__83)))])))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp) (pf : 'e__83) _ (tpl : 'e__82) (lili : 'e__81) _
                (loc : Ploc.t) ->
              (Qast.Node ("WcTyp", [Qast.Loc; lili; tpl; pf; t]) :
               'with_constr)))]];
    Grammar.extension (uidopt : 'uidopt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Option None : 'uidopt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__90)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__90)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__90)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__90)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__90)))])),
           "194fe98d",
           (fun (m : 'e__90) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__101)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__101)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__101)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (seq : 'e__101) _ _ (e : 'expr) _ (loc : Ploc.t) ->
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
                                      "194fe98d",
                                      (fun (a : 'direction_flag)
                                           (loc : Ploc.t) ->
                                         (Qast.VaVal a : 'e__99)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_to")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_to", loc, a) :
                                          'e__99)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "to")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("to", loc, a)) :
                                          'e__99)))])))
                         Grammar.s_self)
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sequence : 'sequence Grammar.Entry.e)),
                          "194fe98d",
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__100)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__100)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__100)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (seq : 'e__100) _ _ (e2 : 'expr) (df : 'e__99) (e1 : 'expr)
                _ (i : 'patt) _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__98)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__98)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__98)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (seq : 'e__98) _ _ (loc : Ploc.t) ->
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (l : 'closed_case_list) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExMat", [Qast.Loc; e; l]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm (fun_def : 'fun_def Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (l : 'closed_case_list) _ (loc : Ploc.t) ->
              (Qast.Node ("ExFun", [Qast.Loc; l]) : 'expr)));
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
                         (Grammar.s_token ("", "open")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "!"))),
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__97)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_!", loc, a) : 'e__97)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                    'e__97)))])))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) _ (m : 'module_expr) (ovf : 'e__97) _ _ _
                (loc : Ploc.t) ->
              (Qast.Node ("ExLop", [Qast.Loc; ovf; m; e]) : 'expr)));
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
                                "194fe98d",
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__96)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__96)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__96)))])))
                   (Grammar.s_nterm
                      (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) _ (mb : 'mod_fun_binding) (m : 'e__96) _ _ _
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
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__94)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__94)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__94)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__94)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__94)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             "194fe98d",
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__95)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__95)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__95)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (x : 'expr) _ (l : 'e__95) (r : 'e__94) _ _ (loc : Ploc.t) ->
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
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__93)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uid", loc, a) : 'e__93)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                    'e__93)))])))
                   (Grammar.s_nterm
                      (alg_attributes : 'alg_attributes Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (x : 'expr) _ (alg_attrs : 'alg_attributes) (id : 'e__93) _ _
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
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) : 'e__91)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_uid")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_uid", loc, a) :
                                          'e__91)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "uid")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("uid", loc, a)) :
                                          'e__91)))])))
                         (Grammar.s_token ("", "of")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_list1
                                     (Grammar.s_nterml
                                        (ctyp : 'ctyp Grammar.Entry.e)
                                        "below_alg_attribute")),
                                "194fe98d",
                                (fun (a : 'ctyp list) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.List a) : 'e__92)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_list")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_list", loc, a) : 'e__92)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "list")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                    'e__92)))])))
                   (Grammar.s_nterm
                      (alg_attributes : 'alg_attributes Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (x : 'expr) _ (alg_attrs : 'alg_attributes) (tyl : 'e__92) _
                (id : 'e__91) _ _ _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__102)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__102)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__102)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__102)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__102)))])))
             (Grammar.s_nterm (let_binding : 'let_binding Grammar.Entry.e)),
           "194fe98d",
           (fun (lb : 'let_binding) (rf : 'e__102) _ (e : 'expr)
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
           "194fe98d",
           (fun _ (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAss", [Qast.Loc; e1; e2]) : 'expr)))];
       Some "||", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "||")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__103)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__103)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__103)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__103) _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAtt", [Qast.Loc; e; attr]) : 'expr)))];
       Some "+", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-.")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExLaz", [Qast.Loc; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "assert")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExAsr", [Qast.Loc; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExApp", [Qast.Loc; e1; e2]) : 'expr)))];
       Some ".", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (dotop : 'dotop Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'dotop) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__110)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_dotop")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_dotop", loc, a) :
                                    'e__110)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "dotop")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("dotop", loc, a)) :
                                    'e__110)))])))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          "194fe98d",
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__111)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__111)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__111)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (el : 'e__111) _ (op : 'e__110) (e : 'expr)
                (loc : Ploc.t) ->
              (Qast.Node ("ExBae", [Qast.Loc; op; e; el]) : 'expr)));
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
                          "194fe98d",
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__109)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__109)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__109)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (el : 'e__109) _ _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExBae", [Qast.Loc; Qast.VaVal (Qast.Str "."); e; el]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (dotop : 'dotop Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'dotop) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__107)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_dotop")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_dotop", loc, a) :
                                    'e__107)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "dotop")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("dotop", loc, a)) :
                                    'e__107)))])))
                   (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          "194fe98d",
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__108)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__108)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__108)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (el : 'e__108) _ (op : 'e__107) (e1 : 'expr)
                (loc : Ploc.t) ->
              (Qast.Node ("ExSte", [Qast.Loc; op; e1; el]) : 'expr)));
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
           "194fe98d",
           (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExSte",
                  [Qast.Loc; Qast.VaVal (Qast.Str "."); e1;
                   Qast.VaVal (Qast.List [e2])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (dotop : 'dotop Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'dotop) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__105)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_dotop")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_dotop", loc, a) :
                                    'e__105)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "dotop")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("dotop", loc, a)) :
                                    'e__105)))])))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          "194fe98d",
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__106)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__106)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__106)))])))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (el : 'e__106) _ (op : 'e__105) (e1 : 'expr)
                (loc : Ploc.t) ->
              (Qast.Node ("ExAre", [Qast.Loc; op; e1; el]) : 'expr)));
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
           "194fe98d",
           (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExAre",
                  [Qast.Loc; Qast.VaVal (Qast.Str "."); e1;
                   Qast.VaVal (Qast.List [e2])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (longident_lident :
                             'longident_lident Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'longident_lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__104)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lilongid", loc, a) : 'e__104)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lilongid", loc, a)) :
                           'e__104)))])),
           "194fe98d",
           (fun (lili : 'e__104) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExFle", [Qast.Loc; e1; lili]) : 'expr)))];
       Some "~-", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-.")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__125)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__125)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__125)))])))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (el : 'e__125) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTup", [Qast.Loc; el]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d", (fun _ (e : 'expr) _ (loc : Ploc.t) -> (e : 'expr)));
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (mt : 'module_type) _ (me : 'module_expr) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("ExPck", [Qast.Loc; me; Qast.Option (Some mt)]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExLong",
                  [Qast.Loc;
                   Qast.Node
                     ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")])]) :
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
                          "194fe98d",
                          (fun (a : 'label_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__124)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__124)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__124)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (lel : 'e__124) _ _ (e : 'expr) _ _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'label_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__123)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__123)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__123)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (lel : 'e__123) _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__122)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__122)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__122)))])))
             (Grammar.s_token ("", "|]")),
           "194fe98d",
           (fun _ (el : 'e__122) _ (loc : Ploc.t) ->
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
           "194fe98d",
           (fun _ (last : 'cons_expr_opt) (el : 'expr list) _
                (loc : Ploc.t) ->
              (mklistexp Qast.Loc last el : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExLong",
                  [Qast.Loc;
                   Qast.Node
                     ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ".")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("ExUnr", [Qast.Loc]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (longident : 'longident Grammar.Entry.e)))
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (e : 'expr) _ _ (i : 'longident) (loc : Ploc.t) ->
              (Qast.Node ("ExOpen", [Qast.Loc; i; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)),
           "194fe98d",
           (fun (i : 'longident) (loc : Ploc.t) ->
              (Qast.Node ("ExLong", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__121)))])),
           "194fe98d",
           (fun (i : 'e__121) (loc : Ploc.t) ->
              (Qast.Node ("ExLid", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__120)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__120)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__120)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__120)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__120)))])),
           "194fe98d",
           (fun (i : 'e__120) (loc : Ploc.t) ->
              (Qast.Node ("ExLid", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("ExExten", [Qast.Loc; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("CHAR", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__119)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_chr")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_chr", loc, a) : 'e__119)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "chr")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("chr", loc, a)) :
                           'e__119)))])),
           "194fe98d",
           (fun (s : 'e__119) (loc : Ploc.t) ->
              (Qast.Node ("ExChr", [Qast.Loc; s]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("RAWSTRING", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__118)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_locstr")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_locstr", loc, a) : 'e__118)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "locstr")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("locstr", loc, a)) :
                           'e__118)))])),
           "194fe98d",
           (fun (s : 'e__118) (loc : Ploc.t) ->
              (match s with
                 Qast.VaVal (Str s) ->
                   let (_, s) = Asttools.split_rawstring s in
                   Qast.Node
                     ("ExStr",
                      [Qast.Loc;
                       Qast.VaVal
                         (Qast.Tuple [Qast.Loc; Qast.VaVal (Qast.Str s)])])
               | VaVal (VaAnt (_, _, _)) -> Qast.Node ("ExStr", [Qast.Loc; s])
               | VaAnt (_, _, _) -> Qast.Node ("ExStr", [Qast.Loc; s])
               | _ ->
                   Ploc.raise loc
                     (Failure
                        "Internal error: a locstr should have been either a raw string or an antiquotation") :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("STRING", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__117)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_str")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_str", loc, a) : 'e__117)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "str")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                           'e__117)))])),
           "194fe98d",
           (fun (s : 'e__117) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExStr",
                  [Qast.Loc; Qast.VaVal (Qast.Tuple [Qast.Loc; s])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("FLOAT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__116)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_flo")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_flo", loc, a) : 'e__116)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "flo")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("flo", loc, a)) :
                           'e__116)))])),
           "194fe98d",
           (fun (s : 'e__116) (loc : Ploc.t) ->
              (Qast.Node ("ExFlo", [Qast.Loc; s]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_n", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__115)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_nativeint")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_nativeint", loc, a) : 'e__115)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "nativeint")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("nativeint", loc, a)) :
                           'e__115)))])),
           "194fe98d",
           (fun (s : 'e__115) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "n"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_L", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__114)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int64")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int64", loc, a) : 'e__114)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int64")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int64", loc, a)) :
                           'e__114)))])),
           "194fe98d",
           (fun (s : 'e__114) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "L"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_l", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__113)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int32")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int32", loc, a) : 'e__113)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int32")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int32", loc, a)) :
                           'e__113)))])),
           "194fe98d",
           (fun (s : 'e__113) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "l"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__112)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int", loc, a) : 'e__112)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int", loc, a)) :
                           'e__112)))])),
           "194fe98d",
           (fun (s : 'e__112) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'match_case list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__127)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__127)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__127)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (l : 'e__127) _ (loc : Ploc.t) -> (l : 'closed_case_list)));
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
                          "194fe98d",
                          (fun (a : 'match_case list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__126)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__126)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__126)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (l : 'e__126) _ (loc : Ploc.t) ->
              (l : 'closed_case_list)))]];
    Grammar.extension (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (Qast.Option None : 'cons_expr_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Option (Some e) : 'cons_expr_opt)))]];
    Grammar.extension (dummy : 'dummy Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (() : 'dummy)))]];
    Grammar.extension (sequence : 'sequence Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) (loc : Ploc.t) -> (Qast.List [e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           "194fe98d",
           (fun _ (e : 'expr) (loc : Ploc.t) -> (Qast.List [e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             Grammar.s_self,
           "194fe98d",
           (fun (el : 'sequence) _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Cons (e, el) : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "open")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "!"))),
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__131)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_!", loc, a) : 'e__131)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                    'e__131)))])))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (el : 'sequence) _ (m : 'module_expr) (ovf : 'e__131) _ _
                (loc : Ploc.t) ->
              (Qast.List
                 [Qast.Node
                    ("ExLop", [Qast.Loc; ovf; m; mksequence Qast.Loc el])] :
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
                                "194fe98d",
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__130)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__130)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__130)))])))
                   (Grammar.s_nterm
                      (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (el : 'sequence) _ (mb : 'mod_fun_binding) (m : 'e__130) _ _
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
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__128)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__128)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__128)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__128)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__128)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             "194fe98d",
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__129)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__129)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__129)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (el : 'sequence) _ (l : 'e__129) (rf : 'e__128) _
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
           "194fe98d",
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
           "194fe98d",
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
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
                             "194fe98d",
                             (fun (a : 'when_expr option) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__132)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__132)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__132)))])))
                (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (w : 'e__132) (aso : 'as_patt_opt) (p : 'patt)
                (loc : Ploc.t) ->
              (mkmatchcase Qast.Loc p aso w e : 'match_case)))]];
    Grammar.extension (as_patt_opt : 'as_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (Qast.Option None : 'as_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Option (Some p) : 'as_patt_opt)))]];
    Grammar.extension (when_expr : 'when_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "when")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'when_expr)))]];
    Grammar.extension (label_expr : 'label_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (patt_label_ident : 'patt_label_ident Grammar.Entry.e)))
             (Grammar.s_nterm (fun_binding : 'fun_binding Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'fun_binding) (i : 'patt_label_ident) (loc : Ploc.t) ->
              (Qast.Tuple [i; e] : 'label_expr)))]];
    Grammar.extension (fun_def : 'fun_def Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d", (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'fun_def) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p; Qast.VaVal (Qast.Option None); e]])]) :
               'fun_def)))]];
    Grammar.extension (patt_ident : 'patt_ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)),
           "194fe98d",
           (fun (li : 'longident) (loc : Ploc.t) ->
              (Qast.Node
                 ("PaLong", [Qast.Loc; li; Qast.VaVal (Qast.List [])]) :
               'patt_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (longident : 'longident Grammar.Entry.e)))
                         (Grammar.s_nterm
                            (check_lparen_type :
                             'check_lparen_type Grammar.Entry.e)))
                      (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "type")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      "194fe98d",
                                      (fun (s : string) (loc : Ploc.t) ->
                                         (Qast.Tuple [Qast.Loc; Qast.Str s] :
                                          'e__135)))])),
                          "194fe98d",
                          (fun (a : 'e__135 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__136)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__136)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__136)))])))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (loc_ids : 'e__136) _ _ _ (li : 'longident)
                (loc : Ploc.t) ->
              (Qast.Node ("PaLong", [Qast.Loc; li; loc_ids]) : 'patt_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_nterml (patt : 'patt Grammar.Entry.e) "simple"),
           "194fe98d",
           (fun (p : 'patt) _ (li : 'longident) (loc : Ploc.t) ->
              (Qast.Node ("PaPfx", [Qast.Loc; li; p]) : 'patt_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__134)))])),
           "194fe98d",
           (fun (s : 'e__134) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'patt_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__133)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__133)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__133)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__133)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__133)))])),
           "194fe98d",
           (fun (s : 'e__133) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'patt_ident)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "|")))
             Grammar.s_self,
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__137)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__137)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__137)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__137) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaAtt", [Qast.Loc; p1; attr]) : 'patt)))];
       None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "effect")))
                   Grammar.s_self)
                (Grammar.s_token ("", ",")))
             (Grammar.s_nterml (patt : 'patt Grammar.Entry.e) "simple"),
           "194fe98d",
           (fun (p2 : 'patt) _ (p1 : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaEff", [Qast.Loc; p1; p2]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("", "exception")))
             Grammar.s_self,
           "194fe98d",
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaExc", [Qast.Loc; p]) : 'patt)))];
       None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "..")))
             Grammar.s_self,
           "194fe98d",
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaRng", [Qast.Loc; p1; p2]) : 'patt)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "lazy")))
             Grammar.s_self,
           "194fe98d",
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaLaz", [Qast.Loc; p]) : 'patt)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           "194fe98d",
           (fun (p2 : 'patt) (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaApp", [Qast.Loc; p1; p2]) : 'patt)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (paren_patt : 'paren_patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'label_patt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__146)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__146)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__146)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (lpl : 'e__146) _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'patt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__145)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__145)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__145)))])))
             (Grammar.s_token ("", "|]")),
           "194fe98d",
           (fun _ (pl : 'e__145) _ (loc : Ploc.t) ->
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
           "194fe98d",
           (fun _ (last : 'cons_patt_opt) (pl : 'patt list) _
                (loc : Ploc.t) ->
              (mklistpat Qast.Loc last pl : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaLong",
                  [Qast.Loc;
                   Qast.Node
                     ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")]);
                   Qast.VaVal (Qast.List [])]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("FLOAT", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node ("PaFlo", [Qast.Loc; Qast.VaVal (neg_string s)]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_n", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "n"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_L", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "L"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_l", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "l"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT", "")),
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__144)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_chr")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_chr", loc, a) : 'e__144)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "chr")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("chr", loc, a)) :
                           'e__144)))])),
           "194fe98d",
           (fun (s : 'e__144) (loc : Ploc.t) ->
              (Qast.Node ("PaChr", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("STRING", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__143)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_str")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_str", loc, a) : 'e__143)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "str")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                           'e__143)))])),
           "194fe98d",
           (fun (s : 'e__143) (loc : Ploc.t) ->
              (Qast.Node ("PaStr", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("FLOAT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__142)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_flo")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_flo", loc, a) : 'e__142)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "flo")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("flo", loc, a)) :
                           'e__142)))])),
           "194fe98d",
           (fun (s : 'e__142) (loc : Ploc.t) ->
              (Qast.Node ("PaFlo", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_n", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__141)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_nativeint")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_nativeint", loc, a) : 'e__141)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "nativeint")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("nativeint", loc, a)) :
                           'e__141)))])),
           "194fe98d",
           (fun (s : 'e__141) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "n"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_L", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int64")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int64", loc, a) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int64")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int64", loc, a)) :
                           'e__140)))])),
           "194fe98d",
           (fun (s : 'e__140) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "L"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_l", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__139)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int32")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int32", loc, a) : 'e__139)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int32")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int32", loc, a)) :
                           'e__139)))])),
           "194fe98d",
           (fun (s : 'e__139) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "l"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__138)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int", loc, a) : 'e__138)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int", loc, a)) :
                           'e__138)))])),
           "194fe98d",
           (fun (s : 'e__138) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str ""]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt_ident : 'patt_ident Grammar.Entry.e)),
           "194fe98d", (fun (p : 'patt_ident) (loc : Ploc.t) -> (p : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("PaExten", [Qast.Loc; e]) : 'patt)))]];
    Grammar.extension (tuple_patt_body1 : 'tuple_patt_body1 Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> ([], true : 'tuple_patt_body1)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ",")))
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (pl, clflag : 'tuple_patt_body1) (p : 'patt) _
                (loc : Ploc.t) ->
              (p :: pl, clflag : 'tuple_patt_body1)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ",")))
             (Grammar.s_token ("", "..")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) -> ([], false : 'tuple_patt_body1)))]];
    Grammar.extension (tuple_patt_body : 'tuple_patt_body Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             (Grammar.s_nterm
                (tuple_patt_body1 : 'tuple_patt_body1 Grammar.Entry.e)),
           "194fe98d",
           (fun (pl, clflag : 'tuple_patt_body1) (p : 'patt) (loc : Ploc.t) ->
              (p :: pl, clflag : 'tuple_patt_body)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "..")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> ([], false : 'tuple_patt_body)))]];
    Grammar.extension (paren_patt : 'paren_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) ->
              (Qast.Node
                 ("PaLong",
                  [Qast.Loc;
                   Qast.Node
                     ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]);
                   Qast.VaVal (Qast.List [])]) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'uidopt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__153)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uidopt", loc, a) : 'e__153)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uidopt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                           'e__153)))])),
           "194fe98d",
           (fun (s : 'e__153) _ (loc : Ploc.t) ->
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
                             "194fe98d",
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__152)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__152)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__152)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           "194fe98d",
           (fun (mt : 'module_type) _ (s : 'e__152) _ (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__151)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__151)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__151)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__151)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__151)))])),
           "194fe98d",
           (fun (s : 'e__151) _ (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : 'patt list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__150)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__150)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__150)))])),
           "194fe98d",
           (fun (pl : 'e__150) (loc : Ploc.t) ->
              (Qast.Node
                 ("PaTup", [Qast.Loc; pl; Qast.VaVal (Qast.Bool true)]) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (patt : 'patt Grammar.Entry.e))
                                  (Grammar.s_token ("", ",")) false),
                             "194fe98d",
                             (fun (a : 'patt list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__147)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__147)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__147)))])))
                (Grammar.s_token ("", ",")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_stop, "194fe98d",
                                (fun (loc : Ploc.t) ->
                                   (Qast.Bool true : 'e__148)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "..")),
                                "194fe98d",
                                (fun _ (loc : Ploc.t) ->
                                   (Qast.Bool false : 'e__148)))]),
                       "194fe98d",
                       (fun (a : 'e__148) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__149)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_closed")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_closed", loc, a) : 'e__149)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "closed")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("closed", loc, a)) :
                           'e__149)))])),
           "194fe98d",
           (fun (clflag : 'e__149) _ (pl : 'e__147) (loc : Ploc.t) ->
              (Qast.Node ("PaTup", [Qast.Loc; pl; clflag]) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d", (fun (p : 'patt) (loc : Ploc.t) -> (p : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ",")))
             (Grammar.s_nterm
                (tuple_patt_body : 'tuple_patt_body Grammar.Entry.e)),
           "194fe98d",
           (fun (pl, clflag : 'tuple_patt_body) _ (p : 'patt)
                (loc : Ploc.t) ->
              (mktuppat Qast.Loc p pl clflag : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d",
           (fun (p2 : 'patt) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaAli", [Qast.Loc; p; p2]) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'paren_patt)))]];
    Grammar.extension (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (Qast.Option None : 'cons_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (p : 'patt) _ (i : 'patt_label_ident) (loc : Ploc.t) ->
              (Qast.Tuple [i; p] : 'label_patt)))]];
    Grammar.extension (patt_label_ident : 'patt_label_ident Grammar.Entry.e)
      None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__154)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__154)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__154)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__154)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__154)))])),
           "194fe98d",
           (fun (i : 'e__154) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; i]) : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)),
           "194fe98d",
           (fun (p1 : 'longident) (loc : Ploc.t) ->
              (Qast.Node
                 ("PaLong", [Qast.Loc; p1; Qast.VaVal (Qast.List [])]) :
               'patt_label_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           "194fe98d",
           (fun (p2 : 'patt_label_ident) _ (p1 : 'longident) (loc : Ploc.t) ->
              (Qast.Node ("PaPfx", [Qast.Loc; p1; p2]) :
               'patt_label_ident)))]];
    Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__157)))])),
           "194fe98d",
           (fun (s : 'e__157) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__156)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__156)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__156)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__156)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__156)))])),
           "194fe98d",
           (fun (s : 'e__156) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("PaExten", [Qast.Loc; e]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm
                   (paren_ipatt : 'paren_ipatt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'label_ipatt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__155)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__155)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__155)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (lpl : 'e__155) _ (loc : Ploc.t) ->
              (Qast.Node ("PaRec", [Qast.Loc; lpl]) : 'ipatt)))]];
    Grammar.extension (tuple_ipatt_body1 : 'tuple_ipatt_body1 Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> ([], true : 'tuple_ipatt_body1)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ",")))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (pl, clflag : 'tuple_ipatt_body1) (p : 'ipatt) _
                (loc : Ploc.t) ->
              (p :: pl, clflag : 'tuple_ipatt_body1)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ",")))
             (Grammar.s_token ("", "..")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) -> ([], false : 'tuple_ipatt_body1)))]];
    Grammar.extension (tuple_ipatt_body : 'tuple_ipatt_body Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm
                (tuple_ipatt_body1 : 'tuple_ipatt_body1 Grammar.Entry.e)),
           "194fe98d",
           (fun (pl, clflag : 'tuple_ipatt_body1) (p : 'ipatt)
                (loc : Ploc.t) ->
              (p :: pl, clflag : 'tuple_ipatt_body)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "..")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> ([], false : 'tuple_ipatt_body)))]];
    Grammar.extension (paren_ipatt : 'paren_ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) ->
              (Qast.Node
                 ("PaLong",
                  [Qast.Loc;
                   Qast.Node
                     ("LiUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]);
                   Qast.VaVal (Qast.List [])]) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'uidopt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__164)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uidopt", loc, a) : 'e__164)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uidopt")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                           'e__164)))])),
           "194fe98d",
           (fun (s : 'e__164) _ (loc : Ploc.t) ->
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
                             "194fe98d",
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__163)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__163)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__163)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           "194fe98d",
           (fun (mt : 'module_type) _ (s : 'e__163) _ (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__162)))])),
           "194fe98d",
           (fun (s : 'e__162) _ (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : 'ipatt list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__161)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__161)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__161)))])),
           "194fe98d",
           (fun (pl : 'e__161) (loc : Ploc.t) ->
              (Qast.Node
                 ("PaTup", [Qast.Loc; pl; Qast.VaVal (Qast.Bool true)]) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (ipatt : 'ipatt Grammar.Entry.e))
                                  (Grammar.s_token ("", ",")) false),
                             "194fe98d",
                             (fun (a : 'ipatt list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__158)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__158)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__158)))])))
                (Grammar.s_token ("", ",")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_stop, "194fe98d",
                                (fun (loc : Ploc.t) ->
                                   (Qast.Bool true : 'e__159)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "..")),
                                "194fe98d",
                                (fun _ (loc : Ploc.t) ->
                                   (Qast.Bool false : 'e__159)))]),
                       "194fe98d",
                       (fun (a : 'e__159) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__160)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_closed")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_closed", loc, a) : 'e__160)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "closed")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("closed", loc, a)) :
                           'e__160)))])),
           "194fe98d",
           (fun (clflag : 'e__160) _ (pl : 'e__158) (loc : Ploc.t) ->
              (Qast.Node ("PaTup", [Qast.Loc; pl; clflag]) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'ipatt) (loc : Ploc.t) -> (p : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ",")))
             (Grammar.s_nterm
                (tuple_ipatt_body : 'tuple_ipatt_body Grammar.Entry.e)),
           "194fe98d",
           (fun (pl, clflag : 'tuple_ipatt_body) _ (p : 'ipatt)
                (loc : Ploc.t) ->
              (mktuppat Qast.Loc p pl clflag : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           "194fe98d",
           (fun (p2 : 'ipatt) _ (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("PaAli", [Qast.Loc; p; p2]) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
                                         "194fe98d",
                                         (fun (a : 'type_patt)
                                              (loc : Ploc.t) ->
                                            (Qast.VaVal a : 'e__165)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "_tp")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaAnt ("_tp", loc, a) :
                                             'e__165)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "tp")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal
                                               (Qast.VaAnt ("tp", loc, a)) :
                                             'e__165)))])))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_list0
                                           (Grammar.s_nterm
                                              (type_parameter :
                                               'type_parameter
                                                 Grammar.Entry.e))),
                                      "194fe98d",
                                      (fun (a : 'type_parameter list)
                                           (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.List a) :
                                          'e__166)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_list")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_list", loc, a) :
                                          'e__166)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "list")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("list", loc, a)) :
                                          'e__166)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_rules
                                        [Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token ("", ":=")),
                                            "194fe98d",
                                            (fun _ (loc : Ploc.t) ->
                                               (Qast.Bool false : 'e__167)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token ("", "=")),
                                            "194fe98d",
                                            (fun _ (loc : Ploc.t) ->
                                               (Qast.Bool true : 'e__167)))]),
                                   "194fe98d",
                                   (fun (a : 'e__167) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__168)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token
                                        ("ANTIQUOT", "_isdecl")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_isdecl", loc, a) :
                                       'e__168)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "isdecl")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("isdecl", loc, a)) :
                                       'e__168)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "private"))),
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__169)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_priv")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_priv", loc, a) : 'e__169)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "priv")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) :
                                    'e__169)))])))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_nterm
                                  (constrain : 'constrain Grammar.Entry.e))),
                          "194fe98d",
                          (fun (a : 'constrain list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__170)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__170)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__170)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (cl : 'e__170) (tk : 'ctyp)
                (pf : 'e__169) (isDecl : 'e__168) (tpl : 'e__166)
                (n : 'e__165) (loc : Ploc.t) ->
              (Qast.Record
                 ["tdIsDecl", isDecl; "tdNam", n; "tdPrm", tpl; "tdPrv", pf;
                  "tdDef", tk; "tdCon", cl; "tdAttributes", attrs] :
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
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_facto
                                     (Grammar.s_rules
                                        [Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_nterm
                                                 (longident_lident :
                                                  'longident_lident
                                                    Grammar.Entry.e)),
                                            "194fe98d",
                                            (fun (a : 'longident_lident)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaVal a : 'e__171)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("ANTIQUOT", "_lilongid")),
                                            "194fe98d",
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaAnt
                                                  ("_lilongid", loc, a) :
                                                'e__171)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("ANTIQUOT", "lilongid")),
                                            "194fe98d",
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaVal
                                                  (Qast.VaAnt
                                                     ("lilongid", loc, a)) :
                                                'e__171)))])))
                               (Grammar.s_facto
                                  (Grammar.s_rules
                                     [Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_list0
                                              (Grammar.s_nterm
                                                 (type_parameter :
                                                  'type_parameter
                                                    Grammar.Entry.e))),
                                         "194fe98d",
                                         (fun (a : 'type_parameter list)
                                              (loc : Ploc.t) ->
                                            (Qast.VaVal (Qast.List a) :
                                             'e__172)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "_list")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaAnt ("_list", loc, a) :
                                             'e__172)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "list")),
                                         "194fe98d",
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal
                                               (Qast.VaAnt ("list", loc, a)) :
                                             'e__172)))])))
                            (Grammar.s_token ("", "+=")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "private"))),
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__173)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_priv")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_priv", loc, a) :
                                       'e__173)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "priv")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("priv", loc, a)) :
                                       'e__173)))])))
                      (Grammar.s_token ("", "[")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (extension_constructor :
                                      'extension_constructor Grammar.Entry.e))
                                  (Grammar.s_token ("", "|")) false),
                             "194fe98d",
                             (fun (a : 'extension_constructor list)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__174)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__174)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__174)))])))
                (Grammar.s_token ("", "]")))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) _ (ecs : 'e__174) _ (pf : 'e__173)
                _ (tpl : 'e__172) (n : 'e__171) (loc : Ploc.t) ->
              (Qast.Record
                 ["teNam", n; "tePrm", tpl; "tePrv", pf; "teECs", ecs;
                  "teAttributes", attrs] :
               'type_extension)))]];
    Grammar.extension (type_patt : 'type_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__175)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__175)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__175)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__175)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__175)))])),
           "194fe98d",
           (fun (n : 'e__175) (loc : Ploc.t) ->
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
           "194fe98d",
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Tuple [t1; t2] : 'constrain)))]];
    Grammar.extension (type_variance : 'type_variance Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (Qast.Str "" : 'type_variance)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-!")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Str "-!" : 'type_variance)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!-")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Str "!-" : 'type_variance)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+!")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Str "+!" : 'type_variance)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!+")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Str "!+" : 'type_variance)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")))
             (Grammar.s_token ("", "-")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) -> (Qast.Str "!-" : 'type_variance)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")))
             (Grammar.s_token ("", "+")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) -> (Qast.Str "!+" : 'type_variance)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Str "!" : 'type_variance)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("", "!")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) -> (Qast.Str "-!" : 'type_variance)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Str "-" : 'type_variance)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_token ("", "!")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) -> (Qast.Str "+!" : 'type_variance)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Str "+" : 'type_variance)))]];
    Grammar.extension (type_parameter : 'type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (type_variance :
                                'type_variance Grammar.Entry.e)),
                          "194fe98d",
                          (fun (a : 'type_variance) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__176)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_variance")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_variance", loc, a) : 'e__176)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "variance")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("variance", loc, a)) :
                              'e__176)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (simple_type_parameter :
                             'simple_type_parameter Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__177)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_var")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_var", loc, a) : 'e__177)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "var")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("var", loc, a)) :
                           'e__177)))])),
           "194fe98d",
           (fun (p : 'e__177) (tv : 'e__176) (loc : Ploc.t) ->
              (Qast.Tuple [p; tv] : 'type_parameter)))]];
    Grammar.extension
      (simple_type_parameter : 'simple_type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (Qast.Option None : 'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.Option (Some (greek_ascii_equiv i)) :
               'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
           (fun (i : 'ident) _ (loc : Ploc.t) ->
              (Qast.Option (Some i) : 'simple_type_parameter)))]];
    Grammar.extension (longident : 'longident Grammar.Entry.e) None
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__178)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__178)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__178)))])),
           "194fe98d",
           (fun (i : 'e__178) _ _ (me1 : 'longident) (loc : Ploc.t) ->
              (Qast.Node ("LiAcc", [Qast.Loc; me1; i]) : 'longident)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__179)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__179)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__179)))])),
           "194fe98d",
           (fun (i : 'e__179) (loc : Ploc.t) ->
              (Qast.Node ("LiUid", [Qast.Loc; i]) : 'longident)))]];
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__180)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__180)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__180)))])),
           "194fe98d",
           (fun (i : 'e__180) _ _ (me1 : 'extended_longident)
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
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__181)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__181)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__181)))])),
           "194fe98d",
           (fun (i : 'e__181) (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__183)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__183)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__183)))])),
           "194fe98d",
           (fun (i : 'e__183) (loc : Ploc.t) ->
              (Qast.Node ("TyLid", [Qast.Loc; i]) : 'ctyp_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (extended_longident :
                             'extended_longident Grammar.Entry.e)))
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (t : 'ctyp) _ _ (me1 : 'extended_longident)
                (loc : Ploc.t) ->
              (Qast.Node ("TyOpen", [Qast.Loc; me1; t]) : 'ctyp_ident)));
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__182)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__182)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__182)))])),
           "194fe98d",
           (fun (i : 'e__182) _ (me1 : 'extended_longident) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__184)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_priv")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_priv", loc, a) : 'e__184)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "priv")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) :
                              'e__184)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (t2 : 'ctyp) (pf : 'e__184) _ (t1 : 'ctyp) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__185)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__185)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__185)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__185) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyAtt", [Qast.Loc; t1; attr]) : 'ctyp)))];
       Some "below_alg_attribute", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop Grammar.s_next, "194fe98d",
           (fun (t : 'ctyp) (loc : Ploc.t) -> (t : 'ctyp)))];
       Some "as", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "as")))
             Grammar.s_self,
           "194fe98d",
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
                             "194fe98d",
                             (fun (a : string list) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.List
                                      (List.map (fun a -> Qast.Str a) a)) :
                                 'e__187)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__187)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__187)))])))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           "194fe98d",
           (fun (t : 'ctyp) _ (pl : 'e__187) _ (loc : Ploc.t) ->
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
                             "194fe98d",
                             (fun (a : 'typevar list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__186)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__186)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__186)))])))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           "194fe98d",
           (fun (t : 'ctyp) _ (pl : 'e__186) _ (loc : Ploc.t) ->
              (Qast.Node ("TyPol", [Qast.Loc; pl; t]) : 'ctyp)))];
       Some "arrow", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           "194fe98d",
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyArr", [Qast.Loc; t1; t2]) : 'ctyp)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           "194fe98d",
           (fun (t2 : 'ctyp) (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyApp", [Qast.Loc; t1; t2]) : 'ctyp)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp_ident : 'ctyp_ident Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'label_declaration list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__191)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__191)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__191)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (ldl : 'e__191) _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'constructor_declaration list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__190)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__190)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__190)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (cdl : 'e__190) _ (loc : Ploc.t) ->
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
                                  (maybe_labeled_ctyp :
                                   'maybe_labeled_ctyp Grammar.Entry.e))
                               (Grammar.s_token ("", "*")) false),
                          "194fe98d",
                          (fun (a : 'maybe_labeled_ctyp list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__189)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__189)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__189)))])))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (tl : 'e__189) _ (loc : Ploc.t) ->
              (Qast.Node ("TyTup", [Qast.Loc; tl]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d", (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'ctyp)));
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
           "194fe98d",
           (fun _ (tl : 'ctyp list) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (mktuptyp Qast.Loc t tl : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "module")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (mt : 'module_type) _ _ (loc : Ploc.t) ->
              (Qast.Node ("TyPck", [Qast.Loc; mt]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("TyExten", [Qast.Loc; e]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("TyAny", [Qast.Loc]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "..")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("TyOpn", [Qast.Loc]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__188)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__188)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__188)))])),
           "194fe98d",
           (fun (i : 'e__188) _ (loc : Ploc.t) ->
              (Qast.Node ("TyQuo", [Qast.Loc; i]) : 'ctyp)))]];
    Grammar.extension
      (maybe_labeled_ctyp : 'maybe_labeled_ctyp Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.VaVal (Qast.Option None); t] :
               'maybe_labeled_ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (check_lident_colon :
                          'check_lident_colon Grammar.Entry.e)))
                   (Grammar.s_token ("LIDENT", "")))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp) _ (li : string) _ (loc : Ploc.t) ->
              (Qast.Tuple
                 [Qast.VaVal (Qast.Option (Some (Qast.VaVal (Qast.Str li))));
                  t] :
               'maybe_labeled_ctyp)))]];
    Grammar.extension (cons_ident : 'cons_ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__192)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__192)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__192)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__192)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__192)))])),
           "194fe98d",
           (fun (ci : 'e__192) (loc : Ploc.t) -> (ci : 'cons_ident)))]];
    Grammar.extension
      (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (rest_constructor_declaration :
                 'rest_constructor_declaration Grammar.Entry.e)),
           "194fe98d",
           (fun (l : 'rest_constructor_declaration) (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (Qast.Tuple (Qast.Loc :: ci :: l) :
               'constructor_declaration)))]];
    Grammar.extension
      (rest_constructor_declaration :
       'rest_constructor_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("", ":")))
                                        (Grammar.s_nterm
                                           (ctyp : 'ctyp Grammar.Entry.e)),
                                      "194fe98d",
                                      (fun (t : 'ctyp) _ (loc : Ploc.t) ->
                                         (t : 'e__196)))])),
                          "194fe98d",
                          (fun (a : 'e__196 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__197)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_rto")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_rto", loc, a) : 'e__197)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "rto")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("rto", loc, a)) :
                              'e__197)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (rto : 'e__197)
                (loc : Ploc.t) ->
              ([Qast.VaVal (Qast.List []); Qast.VaVal (Qast.List []); rto;
                alg_attrs] :
               'rest_constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "of")))
                      (Grammar.s_nterm
                         (type_binder_opt :
                          'type_binder_opt Grammar.Entry.e)))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (ctyp : 'ctyp Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             "194fe98d",
                             (fun (a : 'ctyp list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__193)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__193)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__193)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("", ":")))
                                        (Grammar.s_nterm
                                           (ctyp : 'ctyp Grammar.Entry.e)),
                                      "194fe98d",
                                      (fun (t : 'ctyp) _ (loc : Ploc.t) ->
                                         (t : 'e__194)))])),
                          "194fe98d",
                          (fun (a : 'e__194 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__195)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_rto")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_rto", loc, a) : 'e__195)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "rto")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("rto", loc, a)) :
                              'e__195)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (rto : 'e__195) (cal : 'e__193)
                (ls : 'type_binder_opt) _ (loc : Ploc.t) ->
              ([ls; cal; rto; alg_attrs] : 'rest_constructor_declaration)))]];
    Grammar.extension
      (extension_constructor : 'extension_constructor Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (rest_constructor_declaration :
                 'rest_constructor_declaration Grammar.Entry.e)),
           "194fe98d",
           (fun (l : 'rest_constructor_declaration) (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (Qast.Node
                 ("EcTuple", [Qast.Loc; Qast.Tuple (Qast.Loc :: ci :: l)]) :
               'extension_constructor)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (cons_ident : 'cons_ident Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (longident : 'longident Grammar.Entry.e)),
                          "194fe98d",
                          (fun (a : 'longident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__198)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_longid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_longid", loc, a) : 'e__198)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "longid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("longid", loc, a)) :
                              'e__198)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (b : 'e__198) _
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (Qast.Node ("EcRebind", [Qast.Loc; ci; b; alg_attrs]) :
               'extension_constructor)))]];
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
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (t : 'ctyp) (mf : bool) _
                (i : string) (loc : Ploc.t) ->
              (mklabdecl Qast.Loc i mf t alg_attrs : 'label_declaration)))]];
    Grammar.extension (ident : 'ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident)))]];
    Grammar.extension (direction_flag : 'direction_flag Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "downto")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Bool false : 'direction_flag)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "to")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (Qast.Bool true : 'direction_flag)))]];
    Grammar.extension (typevar : 'typevar Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : 'class_type_declaration list)
                            (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__200)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__200)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__200)))])),
           "194fe98d",
           (fun (ctd : 'e__200) _ _ (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : 'class_declaration list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__199)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__199)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__199)))])),
           "194fe98d",
           (fun (cd : 'e__199) _ (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : 'class_type_declaration list)
                            (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__202)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__202)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__202)))])),
           "194fe98d",
           (fun (ctd : 'e__202) _ _ (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : 'class_description list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__201)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__201)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__201)))])),
           "194fe98d",
           (fun (cd : 'e__201) _ (loc : Ploc.t) ->
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
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__203)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__203)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__203)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__203)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__203)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__204)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__204)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__204)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__204)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__204)))])))
                   (Grammar.s_nterm
                      (class_type_parameters :
                       'class_type_parameters Grammar.Entry.e)))
                (Grammar.s_nterm
                   (class_fun_binding : 'class_fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (cfb : 'class_fun_binding)
                (ctp : 'class_type_parameters) (i : 'e__204) (vf : 'e__203)
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
           "194fe98d",
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
           "194fe98d",
           (fun (ce : 'class_expr) _ (ct : 'class_type) _ (loc : Ploc.t) ->
              (Qast.Node ("CeTyc", [Qast.Loc; ce; ct]) :
               'class_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__205)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__205)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__205)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (tpl : 'e__205) _ (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; tpl] : 'class_type_parameters)));
        Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; Qast.VaVal (Qast.List [])] :
               'class_type_parameters)))]];
    Grammar.extension (class_fun_def : 'class_fun_def Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           "194fe98d",
           (fun (ce : 'class_expr) _ (loc : Ploc.t) ->
              (ce : 'class_fun_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (ce : 'class_fun_def) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("CeFun", [Qast.Loc; p; ce]) : 'class_fun_def)))]];
    Grammar.extension (class_expr : 'class_expr Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "open")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "!"))),
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__208)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_!", loc, a) : 'e__208)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                    'e__208)))])))
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (ce : 'class_expr) _ (i : 'extended_longident) (ovf : 'e__208)
                _ _ (loc : Ploc.t) ->
              (Qast.Node ("CeLop", [Qast.Loc; ovf; i; ce]) : 'class_expr)));
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
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__206)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__206)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__206)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__206)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__206)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             "194fe98d",
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__207)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__207)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__207)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (ce : 'class_expr) _ (lb : 'e__207) (rf : 'e__206) _
                (loc : Ploc.t) ->
              (Qast.Node ("CeLet", [Qast.Loc; rf; lb; ce]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm
                (class_fun_def : 'class_fun_def Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__209)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__209)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__209)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__209) _ (t1 : 'class_expr) (loc : Ploc.t) ->
              (Qast.Node ("CeAtt", [Qast.Loc; t1; attr]) : 'class_expr)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "label"),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__210)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__210)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__210)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__210) _ (t1 : 'class_expr) (loc : Ploc.t) ->
              (Qast.Node ("CeAtt", [Qast.Loc; t1; attr]) : 'class_expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("CeExten", [Qast.Loc; e]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
           "194fe98d",
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
                             "194fe98d",
                             (fun (a : 'ctyp list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__213)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__213)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__213)))])))
                (Grammar.s_token ("", "]")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (longident_lident :
                             'longident_lident Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'longident_lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__214)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lilongid", loc, a) : 'e__214)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lilongid", loc, a)) :
                           'e__214)))])),
           "194fe98d",
           (fun (cli : 'e__214) _ (ctcl : 'e__213) _ (loc : Ploc.t) ->
              (Qast.Node ("CeCon", [Qast.Loc; cli; ctcl]) : 'class_expr)));
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
                             "194fe98d",
                             (fun (a : 'class_self_patt option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__212)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__212)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__212)))])))
                (Grammar.s_nterm
                   (class_structure : 'class_structure Grammar.Entry.e)))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (cf : 'class_structure) (cspo : 'e__212) _ (loc : Ploc.t) ->
              (Qast.Node ("CeStr", [Qast.Loc; cspo; cf]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (longident_lident :
                             'longident_lident Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'longident_lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__211)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lilongid", loc, a) : 'e__211)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lilongid", loc, a)) :
                           'e__211)))])),
           "194fe98d",
           (fun (cli : 'e__211) (loc : Ploc.t) ->
              (Qast.Node
                 ("CeCon", [Qast.Loc; cli; Qast.VaVal (Qast.List [])]) :
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
                                   "194fe98d",
                                   (fun _ (cf : 'class_str_item)
                                        (loc : Ploc.t) ->
                                      (cf : 'e__215)))])),
                       "194fe98d",
                       (fun (a : 'e__215 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__216)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__216)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__216)))])),
           "194fe98d",
           (fun (cf : 'e__216) (loc : Ploc.t) -> (cf : 'class_structure)))]];
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
           "194fe98d",
           (fun _ (t : 'ctyp) _ (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'class_self_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (p : 'patt) _ (loc : Ploc.t) -> (p : 'class_self_patt)))]];
    Grammar.extension (class_str_item : 'class_str_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (Qast.Node ("CrExten", [Qast.Loc; e]) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                                      "194fe98d",
                                      (fun (a : bool) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Bool a) :
                                          'e__228)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_!")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_!", loc, a) :
                                          'e__228)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "!")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("!", loc, a)) :
                                          'e__228)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "private"))),
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__229)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_priv")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_priv", loc, a) :
                                       'e__229)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "priv")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("priv", loc, a)) :
                                       'e__229)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__230)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__230)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__230)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__230)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__230)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (polyt : 'polyt Grammar.Entry.e))),
                             "194fe98d",
                             (fun (a : 'polyt option) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__231)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__231)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__231)))])))
                (Grammar.s_nterm
                   (fun_binding : 'fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (e : 'fun_binding) (topt : 'e__231)
                (l : 'e__230) (pf : 'e__229) (ovf : 'e__228) _
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
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__226)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__226)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__226)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__226)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__226)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__227)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__227)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__227)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__227)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__227)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'e__227)
                (pf : 'e__226) _ _ (loc : Ploc.t) ->
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
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__224)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__224)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__224)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__224)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__224)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__225)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__225)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__225)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__225)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__225)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (lab : 'e__225)
                (mf : 'e__224) _ _ (loc : Ploc.t) ->
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
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__221)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_!")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_!", loc, a) : 'e__221)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "!")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                       'e__221)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "mutable"))),
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__222)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__222)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__222)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__222)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__222)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (lident : 'lident Grammar.Entry.e)),
                             "194fe98d",
                             (fun (a : 'lident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__223)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__223)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__223)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__223)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__223)))])))
                (Grammar.s_nterm
                   (cvalue_binding : 'cvalue_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (e : 'cvalue_binding)
                (lab : 'e__223) (mf : 'e__222) (ovf : 'e__221) _
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
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__219)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_!", loc, a) : 'e__219)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                    'e__219)))])))
                   (Grammar.s_nterm
                      (class_expr : 'class_expr Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_nterm
                                  (as_lident : 'as_lident Grammar.Entry.e))),
                          "194fe98d",
                          (fun (a : 'as_lident option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__220)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__220)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__220)))])))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (pb : 'e__220) (ce : 'class_expr)
                (ovf : 'e__219) _ (loc : Ploc.t) ->
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
                                      "194fe98d",
                                      (fun _ (s : 'class_str_item)
                                           (loc : Ploc.t) ->
                                         (s : 'e__217)))])),
                          "194fe98d",
                          (fun (a : 'e__217 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__218)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__218)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__218)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (st : 'e__218) _ (loc : Ploc.t) ->
              (Qast.Node ("CrDcl", [Qast.Loc; st]) : 'class_str_item)))]];
    Grammar.extension (as_lident : 'as_lident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) _ (loc : Ploc.t) -> (mkident i : 'as_lident)))]];
    Grammar.extension (polyt : 'polyt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d", (fun (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'polyt)))]];
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'cvalue_binding)))]];
    Grammar.extension (lident : 'lident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'lident)))]];
    Grammar.extension (class_type : 'class_type Grammar.Entry.e) None
      [Some "top", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "open")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "!"))),
                                "194fe98d",
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__232)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_!", loc, a) : 'e__232)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "!")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                    'e__232)))])))
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (ce : 'class_type) _ (i : 'extended_longident) (ovf : 'e__232)
                _ _ (loc : Ploc.t) ->
              (Qast.Node ("CtLop", [Qast.Loc; ovf; i; ce]) : 'class_type)));
        Grammar.production
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
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__233)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__233)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__233)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (attr : 'e__233) _ (t1 : 'class_type) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__237)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__237)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__237)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (tl : 'e__237) _ (ct : 'class_type) (loc : Ploc.t) ->
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
                             "194fe98d",
                             (fun (a : 'class_self_type option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__234)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__234)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__234)))])))
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
                                      "194fe98d",
                                      (fun _ (csf : 'class_sig_item)
                                           (loc : Ploc.t) ->
                                         (csf : 'e__235)))])),
                          "194fe98d",
                          (fun (a : 'e__235 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__236)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__236)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__236)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (csf : 'e__236) (cst : 'e__234) _ (loc : Ploc.t) ->
              (Qast.Node ("CtSig", [Qast.Loc; cst; csf]) : 'class_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (Qast.Node ("CtExten", [Qast.Loc; e]) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (ct : 'class_type) _ (loc : Ploc.t) -> (ct : 'class_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__239)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__239)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__239)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__239)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__239)))])),
           "194fe98d",
           (fun (i : 'e__239) (loc : Ploc.t) ->
              (Qast.Node ("CtLid", [Qast.Loc; i]) : 'class_type)));
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
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__238)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__238)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__238)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__238)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__238)))])),
           "194fe98d",
           (fun (i : 'e__238) _ (li : 'extended_longident) (loc : Ploc.t) ->
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
           "194fe98d",
           (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'class_self_type)))]];
    Grammar.extension (class_sig_item : 'class_sig_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (Qast.Node ("CgExten", [Qast.Loc; e]) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__247)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__247)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__247)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__247)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__247)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__248)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__248)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__248)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__248)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__248)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'e__248)
                (pf : 'e__247) _ (loc : Ploc.t) ->
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
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__245)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__245)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__245)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__245)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__245)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__246)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__246)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__246)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__246)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__246)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'e__246)
                (pf : 'e__245) _ _ (loc : Ploc.t) ->
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
                                      "194fe98d",
                                      (fun (a : bool) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Bool a) :
                                          'e__242)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_opt")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_opt", loc, a) :
                                          'e__242)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "opt")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("opt", loc, a)) :
                                          'e__242)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_flag")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_flag", loc, a) :
                                          'e__242)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "flag")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("flag", loc, a)) :
                                          'e__242)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "virtual"))),
                                   "194fe98d",
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__243)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__243)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__243)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__243)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__243)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (lident : 'lident Grammar.Entry.e)),
                                "194fe98d",
                                (fun (a : 'lident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__244)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__244)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__244)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__244)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__244)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'e__244)
                (vf : 'e__243) (mf : 'e__242) _ (loc : Ploc.t) ->
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
           "194fe98d",
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
                                      "194fe98d",
                                      (fun _ (s : 'class_sig_item)
                                           (loc : Ploc.t) ->
                                         (s : 'e__240)))])),
                          "194fe98d",
                          (fun (a : 'e__240 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__241)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__241)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__241)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (st : 'e__241) _ (loc : Ploc.t) ->
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
                                      "194fe98d",
                                      (fun (a : bool) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Bool a) :
                                          'e__249)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_opt")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_opt", loc, a) :
                                          'e__249)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "opt")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("opt", loc, a)) :
                                          'e__249)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_flag")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_flag", loc, a) :
                                          'e__249)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "flag")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("flag", loc, a)) :
                                          'e__249)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("LIDENT", "")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Str a) : 'e__250)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__250)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__250)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_lid")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_lid", loc, a) :
                                       'e__250)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "lid")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("lid", loc, a)) :
                                       'e__250)))])))
                      (Grammar.s_nterm
                         (class_type_parameters :
                          'class_type_parameters Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (ct : 'class_type) _
                (ctp : 'class_type_parameters) (n : 'e__250) (vf : 'e__249)
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
                                      "194fe98d",
                                      (fun (a : bool) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Bool a) :
                                          'e__251)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_opt")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_opt", loc, a) :
                                          'e__251)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "opt")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("opt", loc, a)) :
                                          'e__251)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_flag")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_flag", loc, a) :
                                          'e__251)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "flag")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("flag", loc, a)) :
                                          'e__251)))])))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("LIDENT", "")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Str a) : 'e__252)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__252)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__252)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_lid")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_lid", loc, a) :
                                       'e__252)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "lid")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("lid", loc, a)) :
                                       'e__252)))])))
                      (Grammar.s_nterm
                         (class_type_parameters :
                          'class_type_parameters Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (cs : 'class_type) _
                (ctp : 'class_type_parameters) (n : 'e__252) (vf : 'e__251)
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
                             "194fe98d",
                             (fun (a : 'class_self_patt option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__254)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__254)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__254)))])))
                (Grammar.s_nterm
                   (class_structure : 'class_structure Grammar.Entry.e)))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (cf : 'class_structure) (cspo : 'e__254) _ (loc : Ploc.t) ->
              (Qast.Node ("ExObj", [Qast.Loc; cspo; cf]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "new")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (longident_lident :
                             'longident_lident Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'longident_lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__253)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lilongid", loc, a) : 'e__253)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lilongid", loc, a)) :
                           'e__253)))])),
           "194fe98d",
           (fun (cli : 'e__253) _ (loc : Ploc.t) ->
              (Qast.Node ("ExNew", [Qast.Loc; cli]) : 'expr)))]];
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
                       "194fe98d",
                       (fun (a : 'lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__255)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__255)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__255)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__255)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__255)))])),
           "194fe98d",
           (fun (lab : 'e__255) _ (e : 'expr) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'field_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__256)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__256)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__256)))])))
             (Grammar.s_token ("", ">}")),
           "194fe98d",
           (fun _ (fel : 'e__256) _ (loc : Ploc.t) ->
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                             "194fe98d",
                             (fun (a : 'field list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__258)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__258)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__258)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", ".."))),
                          "194fe98d",
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__259)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__259)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__259)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__259)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__259)))])))
             (Grammar.s_token ("", ">")),
           "194fe98d",
           (fun _ (v : 'e__259) (ml : 'e__258) _ (loc : Ploc.t) ->
              (Qast.Node ("TyObj", [Qast.Loc; ml; v]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (extended_longident_lident :
                             'extended_longident_lident Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'extended_longident_lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__257)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lilongid", loc, a) : 'e__257)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lilongid", loc, a)) :
                           'e__257)))])),
           "194fe98d",
           (fun (cli : 'e__257) _ (loc : Ploc.t) ->
              (Qast.Node ("TyCls", [Qast.Loc; cli]) : 'ctyp)))]];
    Grammar.extension (field : 'field Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("LIDENT", "")))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (t : 'ctyp) _ (lab : string)
                (loc : Ploc.t) ->
              (Qast.Tuple [mkident lab; t; alg_attrs] : 'field)))]];
    Grammar.extension (longident_lident : 'longident_lident Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__262)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__262)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__262)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__262)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__262)))])),
           "194fe98d",
           (fun (i : 'e__262) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Option None; i] : 'longident_lident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (longident : 'longident Grammar.Entry.e)),
                             "194fe98d",
                             (fun (a : 'longident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__260)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_longid", loc, a) : 'e__260)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("longid", loc, a)) :
                                 'e__260)))])))
                (Grammar.s_token ("", ".")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__261)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__261)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__261)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__261)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__261)))])),
           "194fe98d",
           (fun (i : 'e__261) _ (li : 'e__260) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Option (Some li); i] : 'longident_lident)))]];
    Grammar.extension
      (extended_longident_lident : 'extended_longident_lident Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__265)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__265)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__265)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__265)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__265)))])),
           "194fe98d",
           (fun (i : 'e__265) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Option None; i] :
               'extended_longident_lident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (extended_longident :
                                   'extended_longident Grammar.Entry.e)),
                             "194fe98d",
                             (fun (a : 'extended_longident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__263)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_longid", loc, a) : 'e__263)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "longid")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("longid", loc, a)) :
                                 'e__263)))])))
                (Grammar.s_token ("", ".")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__264)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__264)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__264)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__264)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__264)))])),
           "194fe98d",
           (fun (i : 'e__264) _ (li : 'e__263) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Option (Some li); i] :
               'extended_longident_lident)))]];
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
                          "194fe98d",
                          (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__267)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("QUESTIONIDENTCOLON", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__267)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?_:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("?_:", loc, a) : 'e__267)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                              'e__267)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (t : 'ctyp) (i : 'e__267) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__266)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__266)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__266)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__266)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (t : 'ctyp) (i : 'e__266) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'name_tag list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__268)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__268)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__268)))])))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (ntl : 'e__268) _ (rfl : 'poly_variant_list) _ _
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                       "194fe98d",
                       (fun (a : 'poly_variant list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__269)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__269)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__269)))])),
           "194fe98d",
           (fun (rfl : 'e__269) (loc : Ploc.t) ->
              (rfl : 'poly_variant_list)))]];
    Grammar.extension (poly_variant : 'poly_variant Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
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
                                   "194fe98d",
                                   (fun (a : 'ident) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__271)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__271)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   "194fe98d",
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__271)))])))
                      (Grammar.s_token ("", "of")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_flag (Grammar.s_token ("", "&"))),
                             "194fe98d",
                             (fun (a : bool) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Bool a) : 'e__272)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__272)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__272)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_flag")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_flag", loc, a) : 'e__272)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "flag")),
                             "194fe98d",
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                 'e__272)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterml
                                  (ctyp : 'ctyp Grammar.Entry.e)
                                  "below_alg_attribute")
                               (Grammar.s_token ("", "&")) false),
                          "194fe98d",
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__273)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__273)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__273)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (l : 'e__273) (ao : 'e__272) _
                (i : 'e__271) _ (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'ident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__270)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__270)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__270)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (i : 'e__270) _
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
           "194fe98d",
           (fun (i : 'ident) _ (loc : Ploc.t) -> (i : 'name_tag)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (patt_option_label : 'patt_option_label Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt_option_label) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in p : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_ti : 'a_ti Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__281)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__281)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__281)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__281)))])),
           "194fe98d",
           (fun (i : 'e__281) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option None)]) :
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
                          "194fe98d",
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__280)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__280)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__280)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__280)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (p : 'patt) (i : 'e__280) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option (Some p))]) :
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
                                      "194fe98d",
                                      (fun (e : 'expr) _ (loc : Ploc.t) ->
                                         (e : 'e__278)))])),
                          "194fe98d",
                          (fun (a : 'e__278 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__279)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__279)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__279)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (eo : 'e__279) (p : 'patt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaOlb", [Qast.Loc; p; eo]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "~")))
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
                                           (patt : 'patt Grammar.Entry.e)),
                                      "194fe98d",
                                      (fun (p : 'patt) _ (loc : Ploc.t) ->
                                         (p : 'e__276)))])),
                          "194fe98d",
                          (fun (a : 'e__276 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__277)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__277)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__277)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (po : 'e__277) (p : 'patt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaLab", [Qast.Loc; p; po]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (extended_longident_lident :
                             'extended_longident_lident Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'extended_longident_lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__275)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lilongid", loc, a) : 'e__275)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lilongid")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lilongid", loc, a)) :
                           'e__275)))])),
           "194fe98d",
           (fun (lili : 'e__275) _ (loc : Ploc.t) ->
              (Qast.Node ("PaTyp", [Qast.Loc; lili]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__274)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__274)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__274)))])),
           "194fe98d",
           (fun (s : 'e__274) _ (loc : Ploc.t) ->
              (Qast.Node ("PaVrn", [Qast.Loc; s]) : 'patt)))]];
    Grammar.extension (patt_tcon : 'patt_tcon Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'patt_tcon)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt) (loc : Ploc.t) -> (p : 'patt_tcon)))]];
    Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (patt_option_label : 'patt_option_label Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt_option_label) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in p : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_ti : 'a_ti Grammar.Entry.e)),
                       "194fe98d",
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__287)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__287)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__287)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__287)))])),
           "194fe98d",
           (fun (i : 'e__287) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option None)]) :
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
                          "194fe98d",
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__286)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__286)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__286)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__286)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (p : 'ipatt) (i : 'e__286) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option (Some p))]) :
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
                                      "194fe98d",
                                      (fun (e : 'expr) _ (loc : Ploc.t) ->
                                         (e : 'e__284)))])),
                          "194fe98d",
                          (fun (a : 'e__284 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__285)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__285)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__285)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (eo : 'e__285) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaOlb", [Qast.Loc; p; eo]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "~")))
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
                                           (patt : 'patt Grammar.Entry.e)),
                                      "194fe98d",
                                      (fun (p : 'patt) _ (loc : Ploc.t) ->
                                         (p : 'e__282)))])),
                          "194fe98d",
                          (fun (a : 'e__282 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__283)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__283)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__283)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (po : 'e__283) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaLab", [Qast.Loc; p; po]) : 'ipatt)))]];
    Grammar.extension (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'ipatt_tcon)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           "194fe98d",
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
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__300)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__300)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__300)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__300)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__300)))])))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (i : 'e__300) _ _ (loc : Ploc.t) ->
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
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__299)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__299)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__299)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__299)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__299)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (e : 'expr) _ (i : 'e__299) _ _ (loc : Ploc.t) ->
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
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__298)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__298)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__298)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__298)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__298)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (t : 'ctyp) _ (i : 'e__298) _ _ (loc : Ploc.t) ->
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
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__297)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__297)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__297)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__297)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__297)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (i : 'e__297) _ _
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
                       "194fe98d",
                       (fun (a : 'a_qi) (loc : Ploc.t) -> (a : 'e__296)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("QUESTIONIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__296)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("?_", loc, a) : 'e__296)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("?", loc, a)) :
                           'e__296)))])),
           "194fe98d",
           (fun (i : 'e__296) (loc : Ploc.t) ->
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
                                "194fe98d",
                                (fun (a : 'a_qic) (loc : Ploc.t) ->
                                   (a : 'e__294)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token
                                     ("QUESTIONIDENTCOLON", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__294)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "?_:")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("?_:", loc, a) : 'e__294)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "?:")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                                    'e__294)))])))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__295)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__295)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__295)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__295)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__295)))])))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (j : 'e__295) _ (i : 'e__294) (loc : Ploc.t) ->
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
                                      "194fe98d",
                                      (fun (a : 'a_qic) (loc : Ploc.t) ->
                                         (a : 'e__292)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("QUESTIONIDENTCOLON", "")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__292)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?_:")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("?_:", loc, a) :
                                          'e__292)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?:")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("?:", loc, a)) :
                                          'e__292)))])))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__293)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__293)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__293)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__293)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__293)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (e : 'expr) _ (j : 'e__293) _ (i : 'e__292)
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
                                      "194fe98d",
                                      (fun (a : 'a_qic) (loc : Ploc.t) ->
                                         (a : 'e__290)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("QUESTIONIDENTCOLON", "")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__290)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?_:")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("?_:", loc, a) :
                                          'e__290)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?:")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("?:", loc, a)) :
                                          'e__290)))])))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__291)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__291)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__291)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__291)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                "194fe98d",
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__291)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (t : 'ctyp) _ (j : 'e__291) _ (i : 'e__290)
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
                                            "194fe98d",
                                            (fun (a : 'a_qic)
                                                 (loc : Ploc.t) ->
                                               (a : 'e__288)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("QUESTIONIDENTCOLON", "")),
                                            "194fe98d",
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaVal (Qast.Str a) :
                                                'e__288)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("ANTIQUOT", "?_:")),
                                            "194fe98d",
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaAnt ("?_:", loc, a) :
                                                'e__288)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("ANTIQUOT", "?:")),
                                            "194fe98d",
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaVal
                                                  (Qast.VaAnt
                                                     ("?:", loc, a)) :
                                                'e__288)))])))
                               (Grammar.s_token ("", "(")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__289)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__289)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__289)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__289)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      "194fe98d",
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__289)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (j : 'e__289) _ (i : 'e__288)
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
                       "194fe98d",
                       (fun (a : 'a_qi) (loc : Ploc.t) -> (a : 'e__306)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("QUESTIONIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__306)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("?_", loc, a) : 'e__306)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("?", loc, a)) :
                           'e__306)))])),
           "194fe98d",
           (fun (i : 'e__306) (loc : Ploc.t) ->
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
                          "194fe98d",
                          (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__305)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("QUESTIONIDENTCOLON", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__305)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?_:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("?_:", loc, a) : 'e__305)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                              'e__305)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) (i : 'e__305) (loc : Ploc.t) ->
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
                       "194fe98d",
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__304)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__304)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__304)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__304)))])),
           "194fe98d",
           (fun (i : 'e__304) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExLab",
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
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          "194fe98d",
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__303)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__303)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__303)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__303)))])))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) (i : 'e__303) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExLab",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option (Some e))]) :
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
                          "194fe98d",
                          (fun (a : 'fun_binding option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__302)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__302)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__302)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (eo : 'e__302) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExOlb", [Qast.Loc; p; eo]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "~")))
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
                          "194fe98d",
                          (fun (a : 'fun_binding option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__301)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__301)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          "194fe98d",
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__301)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (eo : 'e__301) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExLab", [Qast.Loc; p; eo]) : 'expr)))]];
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
                       "194fe98d",
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__307)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__307)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       "194fe98d",
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__307)))])),
           "194fe98d",
           (fun (s : 'e__307) _ (loc : Ploc.t) ->
              (Qast.Node ("ExVrn", [Qast.Loc; s]) : 'expr)))]];
    (* -- end copy from pa_r to q_MLast -- *)
    Grammar.extension (a_ti : 'a_ti Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
             (Grammar.s_token ("ANTIQUOT", "")),
           "194fe98d",
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
           "194fe98d",
           (fun _ (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("~", loc, a) : 'a_tic)))]];
    Grammar.extension (a_qi : 'a_qi Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "?")))
             (Grammar.s_token ("ANTIQUOT", "")),
           "194fe98d",
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
           "194fe98d",
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
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'module_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "MeXtr" a : 'module_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "mexp")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("mexp", loc, a) : 'module_expr)))]];
   Grammar.extension (longident : 'longident Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "longid")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("longid", loc, a) : 'longident)))]];
   Grammar.extension
     (extended_longident : 'extended_longident Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "longid")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("longid", loc, a) : 'extended_longident)))]];
   Grammar.extension (str_item : 'str_item Grammar.Entry.e)
     (Some (Gramext.Level "top"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'str_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "StXtr" a : 'str_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "stri")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("stri", loc, a) : 'str_item)))]];
   Grammar.extension (module_type : 'module_type Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'module_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "MtXtr" a : 'module_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "mtyp")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("mtyp", loc, a) : 'module_type)))]];
   Grammar.extension (sig_item : 'sig_item Grammar.Entry.e)
     (Some (Gramext.Level "top"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'sig_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "SgXtr" a : 'sig_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "sigi")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("sigi", loc, a) : 'sig_item)))]];
   Grammar.extension (expr : 'expr Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("ExAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "ExXtr" a : 'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "exp")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("exp", loc, a) : 'expr)))]];
   Grammar.extension (patt : 'patt Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("PaAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "PaXtr" a : 'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "pat")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("pat", loc, a) : 'patt)))]];
   Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("PaAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "PaXtr" a : 'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "pat")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("pat", loc, a) : 'ipatt)))]];
   Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'ctyp)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "TyXtr" a : 'ctyp)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "typ")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("typ", loc, a) : 'ctyp)))]];
   Grammar.extension (class_expr : 'class_expr Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "CeXtr" a : 'class_expr)))]];
   Grammar.extension (class_str_item : 'class_str_item Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_str_item)))]];
   Grammar.extension (class_sig_item : 'class_sig_item Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_sig_item)))]];
   Grammar.extension (class_type : 'class_type Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          "194fe98d",
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          "194fe98d",
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
     Some (MLast.ExStr (_, (_, s))) -> set_qmod s
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
        | Qast.Tuple (Qast.Loc :: nl) -> Qast.Tuple (Qast.TrueLoc :: nl)
        | x -> x
      else qast
    in
    Qast.to_patt (m ()) qast
  in
  Quotation.ExAst (expr, patt)
;;

let attribute_body_eoi = Grammar.Entry.create gram "attribute_body_eoi" in
let class_expr_eoi = Grammar.Entry.create gram "class_expr_eoi" in
let class_sig_item_eoi = Grammar.Entry.create gram "class_sig_item_eoi" in
let class_str_item_eoi = Grammar.Entry.create gram "class_str_item_eoi" in
let class_type_eoi = Grammar.Entry.create gram "class_type_eoi" in
let ctyp_eoi = Grammar.Entry.create gram "ctyp_eoi" in
let expr_eoi = Grammar.Entry.create gram "expr_eoi" in
let extended_longident_eoi =
  Grammar.Entry.create gram "extended_longident_eoi"
in
let extension_constructor_eoi =
  Grammar.Entry.create gram "extension_constructor_eoi"
in
let constructor_eoi = Grammar.Entry.create gram "constructor_eoi" in
let longident_eoi = Grammar.Entry.create gram "longident_eoi" in
let module_expr_eoi = Grammar.Entry.create gram "module_expr_eoi" in
let module_type_eoi = Grammar.Entry.create gram "module_type_eoi" in
let patt_eoi = Grammar.Entry.create gram "patt_eoi" in
let poly_variant_eoi = Grammar.Entry.create gram "poly_variant_eoi" in
let sig_item_eoi = Grammar.Entry.create gram "sig_item_eoi" in
let str_item_eoi = Grammar.Entry.create gram "str_item_eoi" in
let type_decl_eoi = Grammar.Entry.create gram "type_decl_eoi" in
let type_extension_eoi = Grammar.Entry.create gram "type_extension_eoi" in
let with_constr_eoi = Grammar.Entry.create gram "with_constr_eoi" in
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
          "194fe98d",
          (fun _ (x : 'attribute_body) (loc : Ploc.t) ->
             (x : 'attribute_body_eoi)))]];
   Grammar.extension (class_expr_eoi : 'class_expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
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
          "194fe98d",
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
          "194fe98d",
          (fun _ (x : 'class_str_item) (loc : Ploc.t) ->
             (x : 'class_str_item_eoi)))]];
   Grammar.extension (class_type_eoi : 'class_type_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'class_type) (loc : Ploc.t) ->
             (x : 'class_type_eoi)))]];
   Grammar.extension (ctyp_eoi : 'ctyp_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'ctyp) (loc : Ploc.t) -> (x : 'ctyp_eoi)))]];
   Grammar.extension (expr_eoi : 'expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'expr) (loc : Ploc.t) -> (x : 'expr_eoi)))]];
   Grammar.extension
     (extended_longident_eoi : 'extended_longident_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (extended_longident : 'extended_longident Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'extended_longident) (loc : Ploc.t) ->
             (x : 'extended_longident_eoi)))]];
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
          "194fe98d",
          (fun _ (x : 'extension_constructor) (loc : Ploc.t) ->
             (x : 'extension_constructor_eoi)))]];
   Grammar.extension (constructor_eoi : 'constructor_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (constructor_declaration :
                   'constructor_declaration Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'constructor_declaration) (loc : Ploc.t) ->
             (x : 'constructor_eoi)))]];
   Grammar.extension (longident_eoi : 'longident_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'longident) (loc : Ploc.t) -> (x : 'longident_eoi)))]];
   Grammar.extension (module_expr_eoi : 'module_expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'module_expr) (loc : Ploc.t) ->
             (x : 'module_expr_eoi)))]];
   Grammar.extension (module_type_eoi : 'module_type_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'module_type) (loc : Ploc.t) ->
             (x : 'module_type_eoi)))]];
   Grammar.extension (patt_eoi : 'patt_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'patt) (loc : Ploc.t) -> (x : 'patt_eoi)))]];
   Grammar.extension (poly_variant_eoi : 'poly_variant_eoi Grammar.Entry.e)
     None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (poly_variant : 'poly_variant Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'poly_variant) (loc : Ploc.t) ->
             (x : 'poly_variant_eoi)))]];
   Grammar.extension (sig_item_eoi : 'sig_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (sig_item : 'sig_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'sig_item) (loc : Ploc.t) -> (x : 'sig_item_eoi)))]];
   Grammar.extension (str_item_eoi : 'str_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'str_item) (loc : Ploc.t) -> (x : 'str_item_eoi)))]];
   Grammar.extension (type_decl_eoi : 'type_decl_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (type_decl : 'type_decl Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
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
          "194fe98d",
          (fun _ (x : 'type_extension) (loc : Ploc.t) ->
             (x : 'type_extension_eoi)))]];
   Grammar.extension (with_constr_eoi : 'with_constr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (with_constr : 'with_constr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (x : 'with_constr) (loc : Ploc.t) ->
             (x : 'with_constr_eoi)))]]];
List.iter (fun (q, f) -> Quotation.add q (f q))
  ["attribute_body", apply_entry attribute_body_eoi;
   "class_expr", apply_entry class_expr_eoi;
   "class_sig_item", apply_entry class_sig_item_eoi;
   "class_str_item", apply_entry class_str_item_eoi;
   "class_type", apply_entry class_type_eoi; "ctyp", apply_entry ctyp_eoi;
   "expr", apply_entry expr_eoi;
   "extended_longident", apply_entry extended_longident_eoi;
   "extension_constructor", apply_entry extension_constructor_eoi;
   "constructor", apply_entry constructor_eoi;
   "longident", apply_entry longident_eoi;
   "module_expr", apply_entry module_expr_eoi;
   "module_type", apply_entry module_type_eoi; "patt", apply_entry patt_eoi;
   "poly_variant", apply_entry poly_variant_eoi;
   "sig_item", apply_entry sig_item_eoi; "str_item", apply_entry str_item_eoi;
   "type_decl", apply_entry type_decl_eoi;
   "type_extension", apply_entry type_extension_eoi;
   "with_constr", apply_entry with_constr_eoi];;

let expr_eoi = Grammar.Entry.create Pcaml.gram "expr_eoi" in
Grammar.safe_extend
  [Grammar.extension (expr_eoi : 'expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_token ("ANTIQUOT_LOC", "")))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
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
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaAnt")),
                   MLast.ExAnt (loc, a))
              else
                MLast.ExApp
                  (loc, MLast.ExLid (loc, "failwith"),
                   MLast.ExStr (loc, (loc, "antiquot"))) :
              'expr_eoi)));
       Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (Pcaml.expr : 'Pcaml__expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (e : 'Pcaml__expr) (loc : Ploc.t) ->
             (let loc = Ploc.make_unlined (0, 0) in
              if !(Pcaml.strict_mode) then
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaVal")),
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
          "194fe98d",
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
                   MLast.PaLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaAnt"),
                      []),
                   MLast.PaAnt (loc, a))
              else MLast.PaAny loc :
              'patt_eoi)));
       Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (Pcaml.patt : 'Pcaml__patt Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          "194fe98d",
          (fun _ (p : 'Pcaml__patt) (loc : Ploc.t) ->
             (let loc = Ploc.make_unlined (0, 0) in
              if !(Pcaml.strict_mode) then
                MLast.PaApp
                  (loc,
                   MLast.PaLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaVal"),
                      []),
                   MLast.PaAnt (loc, p))
              else MLast.PaAnt (loc, p) :
              'patt_eoi)))]]];
let patt s =
  Ploc.call_with Plexer.force_antiquot_loc true (Grammar.Entry.parse patt_eoi)
    (Stream.of_string s)
in
Quotation.add "vala" (Quotation.ExAst (expr, patt));;
