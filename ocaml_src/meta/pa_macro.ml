(* camlp5r *)
(* pa_macro.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "q_MLast.cmo" *)

(*
Added statements:

  In structure items:

     DEFINE <uident>
     DEFINE <uident> = <expression>
     DEFINE <uident> <parameters> = <expression>
     IFDEF <dexpr> THEN <structure> <else> END
     IFNDEF <dexpr> THEN <structure> <else> END

     where <else> is either:
        ELSIFDEF <dexpr> THEN <structure> <else>
        ELSIFNDEF <dexpr> THEN <structure> <else>
        ELSE <structure>
        <nothing>

  In signature items:

     DEFINE <uident>
     DEFINE <uident> = <type>
     DEFINE <uident> <parameters> = <type>
     IFDEF <dexpr> THEN <signature> <else> END
     IFNDEF <dexpr> THEN <signature> <else> END

     where <else> is either:
        ELSIFDEF <dexpr> THEN <signature> <else>
        ELSIFNDEF <dexpr> THEN <signature> <else>
        ELSE <signature>
        <nothing>

  In expressions:

     IFDEF <dexpr> THEN <expression> <else> END
     IFNDEF <dexpr> THEN <expression> <else> END
     __FILE__
     __LOCATION__

     where <else> is either:
        ELSIFDEF <dexpr> THEN <expression> <else>
        ELSIFNDEF <dexpr> THEN <expression> <else>
        ELSE <expression>

  In patterns:

     IFDEF <dexpr> THEN <pattern> ELSE <pattern> END
     IFNDEF <dexpr> THEN <pattern> ELSE <pattern> END

  In types:

     IFDEF <dexpr> THEN <type> ELSE <type> END
     IFNDEF <dexpr> THEN <type> ELSE <type> END

  In constructors declarations, record label declarations and in match cases:

     IFDEF <dexpr> THEN <item> ELSE <item> END
     IFNDEF <dexpr> THEN <item> ELSE <item> END
     IFDEF <dexpr> THEN <item> END
     IFNDEF <dexpr> THEN <item> END

  A <dexpr> is either:

     <dexpr> OR <dexpr>
     <dexpr> AND <dexpr>
     NOT <dexpr>
     ( <dexpr> )
     <uident>
     OCAML_VERSION <op> <version>

  An <op> is among: < <= = > >=
  A <version> is a version of OCaml whose dots are replaced by underscores
  and the possible subpart starting with 'plus' are removed, and prefixed
  with 'OCAML_'. E.g.:
      OCAML_3_08 for ocaml version 3.08
      OCAML_3_13_0 for ocaml version 3.13.0+dev1

  As Camlp5 options:

     -D<uident>
     -U<uident>

  After having used a DEFINE <uident> followed by "= <expression>", you
  can use it in expressions *and* in patterns. If the expression defining
  the macro cannot be used as a pattern, there is an error message if
  it is used in a pattern.

  If the expression body of a DEFINE contains the identifier EVAL, the
  expression is evaluated at compile time. Only some kinds of expressions
  are interpreted (Char.chr, Char.code, binary + and -, characters,
  integers).

  The expression __FILE__ returns the current compiled file name.
  The expression __LOCATION__ returns the current location of itself.

*)

open Pcaml;;
open Printf;;
open Versdep;;

type macro_value =
    MvExpr of string list * MLast.expr
  | MvType of string list * MLast.ctyp
  | MvNone
;;

type 'a item_or_def =
    SdStr of 'a
  | SdDef of string * macro_value
  | SdUnd of string
  | SdNop
;;

let rec list_remove x =
  function
    (y, _) :: l when y = x -> l
  | d :: l -> d :: list_remove x l
  | [] -> []
;;

let oversion =
  let v = string_copy (bytes_of_string Pcaml.ocaml_version) in
  for i = 0 to string_length v - 1 do
    match string_get v i with
      '0'..'9' | 'a'..'z' | 'A'..'Z' -> ()
    | _ -> string_set v i '_'
  done;
  bytes_to_string v
;;

let oname =
  if ocaml_name = "ocaml" then [] else [string_uppercase ocaml_name, MvNone]
;;

let defined =
  ref
    (("CAMLP5", MvNone) :: ("CAMLP5_4_02", MvNone) ::
     ("CAMLP5_5_00", MvNone) :: ("CAMLP5_6_00", MvNone) ::
     ("CAMLP5_6_02_1", MvNone) :: ("CAMLP5_6_09", MvNone) ::
     ("OCAML_" ^ oversion, MvNone) :: oname)
;;

let defined_version loc =
  let s = "OCAML_" in
  let rec loop =
    function
      (d, _) :: l ->
        if String.length d > String.length s &&
           String.sub d 0 (String.length s) = s
        then
          d
        else loop l
    | [] -> Ploc.raise loc (Failure "no defined version")
  in
  loop (List.rev !defined)
;;

let is_defined i =
  i = "STRICT" && !(Pcaml.strict_mode) ||
  i = "COMPATIBLE_WITH_OLD_OCAML" &&
  !(Pcaml.flag_compatible_old_versions_of_ocaml) ||
  List.mem_assoc i !defined
;;

let print_defined () =
  let deflist =
    if !(Pcaml.strict_mode) then ("STRICT", MvNone) :: !defined else !defined
  in
  List.iter
    (fun (d, v) ->
       print_string d;
       begin match v with
         MvExpr (_, _) -> print_string " = <expr>"
       | MvType (_, _) -> print_string " = <type>"
       | MvNone -> ()
       end;
       print_newline ())
    deflist;
  if !(Sys.interactive) then () else exit 0
;;

let loc = Ploc.dummy;;

let subst mloc env =
  let rec loop =
    function
      MLast.ExLet (_, rf, pel, e) ->
        let pel = List.map (fun (p, e) -> p, loop e) pel in
        MLast.ExLet (loc, rf, pel, loop e)
    | MLast.ExIfe (_, e1, e2, e3) ->
        MLast.ExIfe (loc, loop e1, loop e2, loop e3)
    | MLast.ExApp (_, e1, e2) -> MLast.ExApp (loc, loop e1, loop e2)
    | MLast.ExLid (_, x) as e ->
        (try MLast.ExAnt (loc, List.assoc x env) with Not_found -> e)
    | MLast.ExUid (_, x) as e ->
        (try MLast.ExAnt (loc, List.assoc x env) with Not_found -> e)
    | MLast.ExTup (_, x) -> MLast.ExTup (loc, List.map loop x)
    | MLast.ExRec (_, pel, None) ->
        let pel = List.map (fun (p, e) -> p, loop e) pel in
        MLast.ExRec (loc, pel, None)
    | e -> e
  in
  loop
;;

let substp mloc env =
  let rec loop =
    function
      MLast.ExAcc (_, e1, e2) -> MLast.PaAcc (loc, loop e1, loop e2)
    | MLast.ExApp (_, e1, e2) -> MLast.PaApp (loc, loop e1, loop e2)
    | MLast.ExLid (_, x) ->
        begin try MLast.PaAnt (loc, List.assoc x env) with
          Not_found -> MLast.PaLid (loc, x)
        end
    | MLast.ExUid (_, x) ->
        begin try MLast.PaAnt (loc, List.assoc x env) with
          Not_found -> MLast.PaUid (loc, x)
        end
    | MLast.ExInt (_, x, "") -> MLast.PaInt (loc, x, "")
    | MLast.ExChr (_, x) -> MLast.PaChr (loc, x)
    | MLast.ExStr (_, x) -> MLast.PaStr (loc, x)
    | MLast.ExTup (_, x) -> MLast.PaTup (loc, List.map loop x)
    | MLast.ExRec (_, pel, None) ->
        let ppl = List.map (fun (p, e) -> p, loop e) pel in
        MLast.PaRec (loc, ppl)
    | x ->
        Ploc.raise mloc
          (Failure
             "this macro cannot be used in a pattern (see its definition)")
  in
  loop
;;

let substt mloc env =
  let rec loop =
    function
      MLast.TyArr (_, t1, t2) -> MLast.TyArr (loc, loop t1, loop t2)
    | MLast.TyApp (_, t1, t2) -> MLast.TyApp (loc, loop t1, loop t2)
    | MLast.TyTup (_, tl) -> MLast.TyTup (loc, List.map loop tl)
    | MLast.TyLid (_, x) as t -> (try List.assoc x env with Not_found -> t)
    | MLast.TyUid (_, x) as t -> (try List.assoc x env with Not_found -> t)
    | t -> t
  in
  loop
;;

let cannot_eval e =
  let loc = MLast.loc_of_expr e in Ploc.raise loc (Stream.Error "can't eval")
;;

let rec eval =
  function
    MLast.ExApp
      (_, MLast.ExAcc (_, MLast.ExUid (_, "Char"), MLast.ExLid (_, "chr")),
       e) ->
      begin match eval e with
        MLast.ExInt (_, i, "") ->
          let c = Char.escaped (Char.chr (int_of_string i)) in
          MLast.ExChr (loc, c)
      | e -> cannot_eval e
      end
  | MLast.ExApp
      (_, MLast.ExAcc (_, MLast.ExUid (_, "Char"), MLast.ExLid (_, "code")),
       e) ->
      begin match eval e with
        MLast.ExChr (_, c) ->
          let i = string_of_int (Char.code (Plexing.eval_char c)) in
          MLast.ExInt (loc, i, "")
      | e -> cannot_eval e
      end
  | MLast.ExApp (_, MLast.ExApp (_, op, x), y) ->
      let f = eval op in
      let x = eval x in
      let y = eval y in
      begin match x, y with
        MLast.ExInt (_, x, ""), MLast.ExInt (_, y, "") ->
          let x = int_of_string x in
          let y = int_of_string y in
          begin match f with
            MLast.ExLid (_, "+") ->
              MLast.ExInt (loc, string_of_int (x + y), "")
          | MLast.ExLid (_, "-") ->
              MLast.ExInt (loc, string_of_int (x - y), "")
          | MLast.ExLid (_, "lor") ->
              let s = sprintf "0o%o" (x lor y) in MLast.ExInt (loc, s, "")
          | _ -> cannot_eval op
          end
      | _ -> cannot_eval op
      end
  | MLast.ExUid (_, x) as e ->
      (try (match List.assoc x !defined with _ -> e) with Not_found -> e)
  | MLast.ExChr (_, _) | MLast.ExInt (_, _, "") | MLast.ExLid (_, _) as e -> e
  | e -> cannot_eval e
;;

let may_eval =
  function
    MLast.ExApp (_, MLast.ExUid (_, "EVAL"), e) -> eval e
  | e -> e
;;

let incorrect_number loc l1 l2 =
  Ploc.raise loc
    (Failure
       (sprintf "expected %d parameters; found %d" (List.length l2)
          (List.length l1)))
;;

let define eo x =
  begin match eo with
    MvExpr ([], e) ->
      Grammar.safe_extend
        [Grammar.extension (expr : 'expr Grammar.Entry.e)
           (Some (Gramext.Level "simple"))
           [None, None,
            [Grammar.production
               (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)),
                (fun _ (loc : Ploc.t) ->
                   (may_eval (Reloc.expr (fun _ -> loc) 0 e) : 'expr)))]];
         Grammar.extension (patt : 'patt Grammar.Entry.e)
           (Some (Gramext.Level "simple"))
           [None, None,
            [Grammar.production
               (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)),
                (fun _ (loc : Ploc.t) ->
                   (let p = substp loc [] e in Reloc.patt (fun _ -> loc) 0 p :
                    'patt)))]]]
  | MvExpr (sl, e) ->
      Grammar.safe_extend
        [Grammar.extension (expr : 'expr Grammar.Entry.e)
           (Some (Gramext.Level "apply"))
           [None, None,
            [Grammar.production
               (Grammar.r_next
                  (Grammar.r_next Grammar.r_stop
                     (Grammar.s_token ("UIDENT", x)))
                  Grammar.s_self,
                (fun (param : 'expr) _ (loc : Ploc.t) ->
                   (let el =
                      match param with
                        MLast.ExTup (_, el) -> el
                      | e -> [e]
                    in
                    if List.length el = List.length sl then
                      let env = List.combine sl el in
                      let e = subst loc env e in
                      may_eval (Reloc.expr (fun _ -> loc) 0 e)
                    else incorrect_number loc el sl :
                    'expr)))]];
         Grammar.extension (patt : 'patt Grammar.Entry.e)
           (Some (Gramext.Level "simple"))
           [None, None,
            [Grammar.production
               (Grammar.r_next
                  (Grammar.r_next Grammar.r_stop
                     (Grammar.s_token ("UIDENT", x)))
                  Grammar.s_self,
                (fun (param : 'patt) _ (loc : Ploc.t) ->
                   (let pl =
                      match param with
                        MLast.PaTup (_, pl) -> pl
                      | p -> [p]
                    in
                    if List.length pl = List.length sl then
                      let e = may_eval (Reloc.expr (fun _ -> loc) 0 e) in
                      let env = List.combine sl pl in
                      let p = substp loc env e in
                      Reloc.patt (fun _ -> loc) 0 p
                    else incorrect_number loc pl sl :
                    'patt)))]]]
  | MvType ([], t) ->
      Grammar.safe_extend
        [Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
           (Some (Gramext.Level "simple"))
           [None, None,
            [Grammar.production
               (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)),
                (fun _ (loc : Ploc.t) -> (t : 'ctyp)))]]]
  | MvType (sl, t) ->
      Grammar.safe_extend
        [Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
           (Some (Gramext.Level "apply"))
           [None, None,
            [Grammar.production
               (Grammar.r_next
                  (Grammar.r_next Grammar.r_stop
                     (Grammar.s_token ("UIDENT", x)))
                  Grammar.s_self,
                (fun (param : 'ctyp) _ (loc : Ploc.t) ->
                   (let tl = [param] in
                    if List.length tl = List.length sl then
                      let env = List.combine sl tl in
                      let t = substt loc env t in t
                    else incorrect_number loc tl sl :
                    'ctyp)))]]]
  | MvNone -> ()
  end;
  defined := (x, eo) :: !defined
;;

let undef x =
  try
    let eo = List.assoc x !defined in
    begin match eo with
      MvExpr ([], _) ->
        Grammar.safe_delete_rule expr
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)));
        Grammar.safe_delete_rule patt
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)))
    | MvExpr (_, _) ->
        Grammar.safe_delete_rule expr
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)))
             Grammar.s_self);
        Grammar.safe_delete_rule patt
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)))
             Grammar.s_self)
    | MvType ([], _) ->
        Grammar.safe_delete_rule ctyp
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)))
    | MvType (_, _) ->
        Grammar.safe_delete_rule ctyp
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", x)))
             Grammar.s_self)
    | MvNone -> ()
    end;
    defined := list_remove x !defined
  with Not_found -> ()
;;

let apply_directive loc n dp =
  let n = Pcaml.unvala n in
  match try Some (Pcaml.find_directive n) with Not_found -> None with
    Some f -> f (Pcaml.unvala dp)
  | None ->
      let msg = sprintf "unknown directive #%s" n in
      Ploc.raise loc (Stream.Error msg)
;;

Grammar.safe_extend
  (let _ = (expr : 'expr Grammar.Entry.e)
   and _ = (patt : 'patt Grammar.Entry.e)
   and _ = (str_item : 'str_item Grammar.Entry.e)
   and _ = (sig_item : 'sig_item Grammar.Entry.e)
   and _ =
     (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
   and _ = (match_case : 'match_case Grammar.Entry.e)
   and _ = (label_declaration : 'label_declaration Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry expr) s
   in
   let str_macro_def : 'str_macro_def Grammar.Entry.e =
     grammar_entry_create "str_macro_def"
   and else_str : 'else_str Grammar.Entry.e = grammar_entry_create "else_str"
   and sig_macro_def : 'sig_macro_def Grammar.Entry.e =
     grammar_entry_create "sig_macro_def"
   and else_sig : 'else_sig Grammar.Entry.e = grammar_entry_create "else_sig"
   and structure_or_macro : 'structure_or_macro Grammar.Entry.e =
     grammar_entry_create "structure_or_macro"
   and signature_or_macro : 'signature_or_macro Grammar.Entry.e =
     grammar_entry_create "signature_or_macro"
   and opt_macro_expr : 'opt_macro_expr Grammar.Entry.e =
     grammar_entry_create "opt_macro_expr"
   and opt_macro_type : 'opt_macro_type Grammar.Entry.e =
     grammar_entry_create "opt_macro_type"
   and macro_param : 'macro_param Grammar.Entry.e =
     grammar_entry_create "macro_param"
   and else_expr : 'else_expr Grammar.Entry.e =
     grammar_entry_create "else_expr"
   and else_patt : 'else_patt Grammar.Entry.e =
     grammar_entry_create "else_patt"
   and else_match_case : 'else_match_case Grammar.Entry.e =
     grammar_entry_create "else_match_case"
   and dexpr : 'dexpr Grammar.Entry.e = grammar_entry_create "dexpr"
   and op : 'op Grammar.Entry.e = grammar_entry_create "op"
   and uident : 'uident Grammar.Entry.e = grammar_entry_create "uident" in
   [Grammar.extension (str_item : 'str_item Grammar.Entry.e)
      (Some Gramext.First)
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (str_macro_def : 'str_macro_def Grammar.Entry.e)),
           (fun (x : 'str_macro_def) (loc : Ploc.t) ->
              (match x with
                 SdStr sil ->
                   let sil = Pcaml.unvala sil in
                   List.iter
                     (function
                        MLast.StDir (loc, n, dp) -> apply_directive loc n dp
                      | _ -> ())
                     sil;
                   begin match sil with
                     [si] -> si
                   | sil -> MLast.StDcl (loc, sil)
                   end
               | SdDef (x, eo) -> define eo x; MLast.StDcl (loc, [])
               | SdUnd x -> undef x; MLast.StDcl (loc, [])
               | SdNop -> MLast.StDcl (loc, []) :
               'str_item)))]];
    Grammar.extension (sig_item : 'sig_item Grammar.Entry.e)
      (Some Gramext.First)
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (sig_macro_def : 'sig_macro_def Grammar.Entry.e)),
           (fun (x : 'sig_macro_def) (loc : Ploc.t) ->
              (match x with
                 SdStr sil ->
                   let sil = Pcaml.unvala sil in
                   List.iter
                     (function
                        MLast.SgDir (loc, n, dp) -> apply_directive loc n dp
                      | _ -> ())
                     sil;
                   begin match sil with
                     [si] -> si
                   | sil -> MLast.SgDcl (loc, sil)
                   end
               | SdDef (x, eo) -> define eo x; MLast.SgDcl (loc, [])
               | SdUnd x -> undef x; MLast.SgDcl (loc, [])
               | SdNop -> MLast.SgDcl (loc, []) :
               'sig_item)))]];
    Grammar.extension (str_macro_def : 'str_macro_def Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFNDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   (Grammar.s_nterm
                      (structure_or_macro :
                       'structure_or_macro Grammar.Entry.e)))
                (Grammar.s_nterm (else_str : 'else_str Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (d2 : 'else_str) (d1 : 'structure_or_macro) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then d1 else d2 : 'str_macro_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   (Grammar.s_nterm
                      (structure_or_macro :
                       'structure_or_macro Grammar.Entry.e)))
                (Grammar.s_nterm (else_str : 'else_str Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (d2 : 'else_str) (d1 : 'structure_or_macro) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then d1 else d2 : 'str_macro_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "UNDEF")))
             (Grammar.s_nterm (uident : 'uident Grammar.Entry.e)),
           (fun (i : 'uident) _ (loc : Ploc.t) ->
              (SdUnd i : 'str_macro_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "DEFINE_TYPE")))
                (Grammar.s_nterm (uident : 'uident Grammar.Entry.e)))
             (Grammar.s_nterm
                (opt_macro_type : 'opt_macro_type Grammar.Entry.e)),
           (fun (ome : 'opt_macro_type) (i : 'uident) _ (loc : Ploc.t) ->
              (SdDef (i, ome) : 'str_macro_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "DEFINE")))
                (Grammar.s_nterm (uident : 'uident Grammar.Entry.e)))
             (Grammar.s_nterm
                (opt_macro_expr : 'opt_macro_expr Grammar.Entry.e)),
           (fun (ome : 'opt_macro_expr) (i : 'uident) _ (loc : Ploc.t) ->
              (SdDef (i, ome) : 'str_macro_def)))]];
    Grammar.extension (else_str : 'else_str Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> (SdNop : 'else_str)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "ELSE")))
             (Grammar.s_nterm
                (structure_or_macro : 'structure_or_macro Grammar.Entry.e)),
           (fun (d1 : 'structure_or_macro) _ (loc : Ploc.t) ->
              (d1 : 'else_str)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm
                   (structure_or_macro :
                    'structure_or_macro Grammar.Entry.e)))
             Grammar.s_self,
           (fun (d2 : 'else_str) (d1 : 'structure_or_macro) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then d1 else d2 : 'else_str)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm
                   (structure_or_macro :
                    'structure_or_macro Grammar.Entry.e)))
             Grammar.s_self,
           (fun (d2 : 'else_str) (d1 : 'structure_or_macro) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then d1 else d2 : 'else_str)))]];
    Grammar.extension (sig_macro_def : 'sig_macro_def Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFNDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   (Grammar.s_nterm
                      (signature_or_macro :
                       'signature_or_macro Grammar.Entry.e)))
                (Grammar.s_nterm (else_sig : 'else_sig Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (d2 : 'else_sig) (d1 : 'signature_or_macro) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then d1 else d2 : 'sig_macro_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   (Grammar.s_nterm
                      (signature_or_macro :
                       'signature_or_macro Grammar.Entry.e)))
                (Grammar.s_nterm (else_sig : 'else_sig Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (d2 : 'else_sig) (d1 : 'signature_or_macro) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then d1 else d2 : 'sig_macro_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "UNDEF")))
             (Grammar.s_nterm (uident : 'uident Grammar.Entry.e)),
           (fun (i : 'uident) _ (loc : Ploc.t) ->
              (SdUnd i : 'sig_macro_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "DEFINE_TYPE")))
                (Grammar.s_nterm (uident : 'uident Grammar.Entry.e)))
             (Grammar.s_nterm
                (opt_macro_type : 'opt_macro_type Grammar.Entry.e)),
           (fun (omt : 'opt_macro_type) (i : 'uident) _ (loc : Ploc.t) ->
              (SdDef (i, omt) : 'sig_macro_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "DEFINE")))
                (Grammar.s_nterm (uident : 'uident Grammar.Entry.e)))
             (Grammar.s_nterm
                (opt_macro_type : 'opt_macro_type Grammar.Entry.e)),
           (fun (omt : 'opt_macro_type) (i : 'uident) _ (loc : Ploc.t) ->
              (SdDef (i, omt) : 'sig_macro_def)))]];
    Grammar.extension (else_sig : 'else_sig Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> (SdNop : 'else_sig)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "ELSE")))
             (Grammar.s_nterm
                (signature_or_macro : 'signature_or_macro Grammar.Entry.e)),
           (fun (d1 : 'signature_or_macro) _ (loc : Ploc.t) ->
              (d1 : 'else_sig)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm
                   (signature_or_macro :
                    'signature_or_macro Grammar.Entry.e)))
             Grammar.s_self,
           (fun (d2 : 'else_sig) (d1 : 'signature_or_macro) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then d1 else d2 : 'else_sig)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm
                   (signature_or_macro :
                    'signature_or_macro Grammar.Entry.e)))
             Grammar.s_self,
           (fun (d2 : 'else_sig) (d1 : 'signature_or_macro) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then d1 else d2 : 'else_sig)))]];
    Grammar.extension
      (structure_or_macro : 'structure_or_macro Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (structure : 'structure Grammar.Entry.e)),
           (fun (sil : 'structure) (loc : Ploc.t) ->
              (SdStr sil : 'structure_or_macro)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (str_macro_def : 'str_macro_def Grammar.Entry.e)),
           (fun (d : 'str_macro_def) (loc : Ploc.t) ->
              (d : 'structure_or_macro)))]];
    Grammar.extension
      (signature_or_macro : 'signature_or_macro Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (signature : 'signature Grammar.Entry.e)),
           (fun (sil : 'signature) (loc : Ploc.t) ->
              (SdStr sil : 'signature_or_macro)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (sig_macro_def : 'sig_macro_def Grammar.Entry.e)),
           (fun (d : 'sig_macro_def) (loc : Ploc.t) ->
              (d : 'signature_or_macro)))]];
    Grammar.extension (opt_macro_expr : 'opt_macro_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (MvNone : 'opt_macro_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (MvExpr ([], e) : 'opt_macro_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (macro_param : 'macro_param Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (pl : 'macro_param) (loc : Ploc.t) ->
              (MvExpr (pl, e) : 'opt_macro_expr)))]];
    Grammar.extension (opt_macro_type : 'opt_macro_type Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (MvNone : 'opt_macro_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (loc : Ploc.t) ->
              (MvType ([], t) : 'opt_macro_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_list1 (Grammar.s_token ("LIDENT", ""))))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (pl : string list) (loc : Ploc.t) ->
              (MvType (pl, t) : 'opt_macro_type)))]];
    Grammar.extension (macro_param : 'macro_param Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_list1sep (Grammar.s_token ("LIDENT", ""))
                   (Grammar.s_token ("", ",")) false))
             (Grammar.s_token ("", ")")),
           (fun _ (sl : string list) _ (loc : Ploc.t) ->
              (sl : 'macro_param)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1 (Grammar.s_token ("LIDENT", ""))),
           (fun (sl : string list) (loc : Ploc.t) -> (sl : 'macro_param)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "top"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFNDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   Grammar.s_self)
                (Grammar.s_nterm (else_expr : 'else_expr Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (e2 : 'else_expr) (e1 : 'expr) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then e1 else e2 : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   Grammar.s_self)
                (Grammar.s_nterm (else_expr : 'else_expr Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (e2 : 'else_expr) (e1 : 'expr) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then e1 else e2 : 'expr)))]];
    Grammar.extension (else_expr : 'else_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "ELSE")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'else_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'else_expr) (e1 : 'expr) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then e1 else e2 : 'else_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'else_expr) (e1 : 'expr) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then e1 else e2 : 'else_expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_token ("LIDENT", "__LOCATION__")),
           (fun _ (loc : Ploc.t) ->
              (let bp = string_of_int (Ploc.first_pos loc) in
               let ep = string_of_int (Ploc.last_pos loc) in
               MLast.ExTup
                 (loc,
                  [MLast.ExInt (loc, bp, ""); MLast.ExInt (loc, ep, "")]) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_token ("LIDENT", "__FILE__")),
           (fun _ (loc : Ploc.t) ->
              (MLast.ExStr (loc, Ploc.file_name loc) : 'expr)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFNDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   Grammar.s_self)
                (Grammar.s_nterm (else_patt : 'else_patt Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (p2 : 'else_patt) (p1 : 'patt) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then p2 else p1 : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   Grammar.s_self)
                (Grammar.s_nterm (else_patt : 'else_patt Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (p2 : 'else_patt) (p1 : 'patt) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then p1 else p2 : 'patt)))]];
    Grammar.extension (else_patt : 'else_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "ELSE")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (loc : Ploc.t) -> (p : 'else_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (p2 : 'else_patt) (p1 : 'patt) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then p1 else p2 : 'else_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (p2 : 'else_patt) (p1 : 'patt) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then p1 else p2 : 'else_patt)))]];
    Grammar.extension
      (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
      (Some Gramext.First)
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "IFNDEF")))
                            (Grammar.s_nterm
                               (dexpr : 'dexpr Grammar.Entry.e)))
                         (Grammar.s_token ("", "THEN")))
                      Grammar.s_self)
                   (Grammar.s_token ("", "ELSE")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (y : 'constructor_declaration) _
                (x : 'constructor_declaration) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then y else x : 'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "IFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (x : 'constructor_declaration) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then Grammar.skip_item x else x :
               'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "IFDEF")))
                            (Grammar.s_nterm
                               (dexpr : 'dexpr Grammar.Entry.e)))
                         (Grammar.s_token ("", "THEN")))
                      Grammar.s_self)
                   (Grammar.s_token ("", "ELSE")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (y : 'constructor_declaration) _
                (x : 'constructor_declaration) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then x else y : 'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "IFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (x : 'constructor_declaration) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then x else Grammar.skip_item x :
               'constructor_declaration)))]];
    Grammar.extension (label_declaration : 'label_declaration Grammar.Entry.e)
      (Some Gramext.First)
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "IFNDEF")))
                            (Grammar.s_nterm
                               (dexpr : 'dexpr Grammar.Entry.e)))
                         (Grammar.s_token ("", "THEN")))
                      Grammar.s_self)
                   (Grammar.s_token ("", "ELSE")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (y : 'label_declaration) _ (x : 'label_declaration) _
                (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then y else x : 'label_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "IFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (x : 'label_declaration) _ (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then Grammar.skip_item x else x : 'label_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "IFDEF")))
                            (Grammar.s_nterm
                               (dexpr : 'dexpr Grammar.Entry.e)))
                         (Grammar.s_token ("", "THEN")))
                      Grammar.s_self)
                   (Grammar.s_token ("", "ELSE")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (y : 'label_declaration) _ (x : 'label_declaration) _
                (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then x else y : 'label_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "IFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (x : 'label_declaration) _ (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then x else Grammar.skip_item x : 'label_declaration)))]];
    Grammar.extension (match_case : 'match_case Grammar.Entry.e)
      (Some Gramext.First)
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "IFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (x : 'match_case) _ (e : 'dexpr) _ (loc : Ploc.t) ->
              (if not e then x else Grammar.skip_item x : 'match_case)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFNDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   Grammar.s_self)
                (Grammar.s_nterm
                   (else_match_case : 'else_match_case Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (y : 'else_match_case) (x : 'match_case) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then x else y : 'match_case)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "IFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                Grammar.s_self)
             (Grammar.s_token ("", "END")),
           (fun _ (x : 'match_case) _ (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then x else Grammar.skip_item x : 'match_case)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "IFDEF")))
                         (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                      (Grammar.s_token ("", "THEN")))
                   Grammar.s_self)
                (Grammar.s_nterm
                   (else_match_case : 'else_match_case Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           (fun _ (y : 'else_match_case) (x : 'match_case) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then x else y : 'match_case)))]];
    Grammar.extension (else_match_case : 'else_match_case Grammar.Entry.e)
      None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "ELSE")))
             (Grammar.s_nterm (match_case : 'match_case Grammar.Entry.e)),
           (fun (x : 'match_case) _ (loc : Ploc.t) ->
              (x : 'else_match_case)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "ELSIFNDEF")))
                   (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                (Grammar.s_token ("", "THEN")))
             (Grammar.s_nterm (match_case : 'match_case Grammar.Entry.e)),
           (fun (x : 'match_case) _ (e : 'dexpr) _ (loc : Ploc.t) ->
              (if not e then x else Grammar.skip_item x : 'else_match_case)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFNDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm (match_case : 'match_case Grammar.Entry.e)))
             Grammar.s_self,
           (fun (y : 'else_match_case) (x : 'match_case) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if not e then x else y : 'else_match_case)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "ELSIFDEF")))
                   (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                (Grammar.s_token ("", "THEN")))
             (Grammar.s_nterm (match_case : 'match_case Grammar.Entry.e)),
           (fun (x : 'match_case) _ (e : 'dexpr) _ (loc : Ploc.t) ->
              (if e then x else Grammar.skip_item x : 'else_match_case)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "ELSIFDEF")))
                      (Grammar.s_nterm (dexpr : 'dexpr Grammar.Entry.e)))
                   (Grammar.s_token ("", "THEN")))
                (Grammar.s_nterm (match_case : 'match_case Grammar.Entry.e)))
             Grammar.s_self,
           (fun (y : 'else_match_case) (x : 'match_case) _ (e : 'dexpr) _
                (loc : Ploc.t) ->
              (if e then x else y : 'else_match_case)))]];
    Grammar.extension (dexpr : 'dexpr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "OR")))
             Grammar.s_self,
           (fun (y : 'dexpr) _ (x : 'dexpr) (loc : Ploc.t) ->
              (x || y : 'dexpr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "AND")))
             Grammar.s_self,
           (fun (y : 'dexpr) _ (x : 'dexpr) (loc : Ploc.t) ->
              (x && y : 'dexpr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "OCAML_VERSION")))
                (Grammar.s_nterm (op : 'op Grammar.Entry.e)))
             (Grammar.s_nterm (uident : 'uident Grammar.Entry.e)),
           (fun (y : 'uident) (f : 'op) _ (loc : Ploc.t) ->
              (f (defined_version loc) y : 'dexpr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "NOT")))
             Grammar.s_self,
           (fun (x : 'dexpr) _ (loc : Ploc.t) -> (not x : 'dexpr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (x : 'dexpr) _ (loc : Ploc.t) -> (x : 'dexpr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (uident : 'uident Grammar.Entry.e)),
           (fun (i : 'uident) (loc : Ploc.t) -> (is_defined i : 'dexpr)))]];
    Grammar.extension (op : 'op Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ">=")),
           (fun _ (loc : Ploc.t) -> ((>=) : 'op)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ">")),
           (fun _ (loc : Ploc.t) -> ((>) : 'op)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "<>")),
           (fun _ (loc : Ploc.t) -> ((<>) : 'op)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")),
           (fun _ (loc : Ploc.t) -> ((=) : 'op)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "<")),
           (fun _ (loc : Ploc.t) -> ((<) : 'op)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "<=")),
           (fun _ (loc : Ploc.t) -> ((<=) : 'op)))]];
    Grammar.extension (uident : 'uident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> (i : 'uident)))]]]);;

Pcaml.add_option "-D" (Arg.String (define MvNone))
  "<string> Define for IFDEF instruction.";;

Pcaml.add_option "-U" (Arg.String undef)
  "<string> Undefine for IFDEF instruction.";;

Pcaml.add_option "-defined" (Arg.Unit print_defined)
  " Print the defined macros and exit.";;
