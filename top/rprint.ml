(* camlp5r pa_macro.cmo *)
(* rprint.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

IFDEF OCAML_VERSION >= OCAML_3_03 THEN

open Format;
open Outcometree;

value string_lowercase =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN String.lowercase
  ELSE String.lowercase_ascii END
;

exception Ellipsis;
value cautious f ppf arg =
  try f ppf arg with [ Ellipsis -> fprintf ppf "..." ]
;

value print_out_name ppf s =
  IFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    fprintf ppf "%s" s
  ELSE
    fprintf ppf "%s" s.printed_name
  END
;

value rec print_ident ppf =
  fun
  [ Oide_ident s -> print_out_name ppf s
  | Oide_dot id s -> fprintf ppf "%a.%s" print_ident id s
  | Oide_apply id1 id2 ->
      fprintf ppf "%a(%a)" print_ident id1 print_ident id2 ]
;

value value_ident ppf name =
  if List.mem name ["or"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]
  then
    fprintf ppf "( %s )" name
  else
    match name.[0] with
    [ 'a'..'z' | '\223'..'\246' | '\248'..'\255' | '_' ->
        fprintf ppf "%s" name
    | _ -> fprintf ppf "( %s )" name ]
;

(* Values *)

value print_out_value ppf tree =
  let rec print_tree ppf =
    fun
    [ Oval_constr name ([_ :: _] as params) ->
        fprintf ppf "@[<2>%a@ %a@]" print_ident name
          (print_tree_list print_simple_tree "") params
    | Oval_variant name (Some param) ->
        fprintf ppf "@[<2>`%s@ %a@]" name print_simple_tree param
    | tree -> print_simple_tree ppf tree ]
  and print_simple_tree ppf =
    fun
    [ Oval_int i -> fprintf ppf "%i" i
    | IFDEF OCAML_VERSION >= OCAML_3_07 THEN
        Oval_int32 i -> fprintf ppf "%lil" i
      END
    | IFDEF OCAML_VERSION >= OCAML_3_07 THEN
        Oval_int64 i -> fprintf ppf "%LiL" i
      END
    | IFDEF OCAML_VERSION >= OCAML_3_07 THEN
        Oval_nativeint i -> fprintf ppf "%nin" i
      END
    | Oval_float f -> fprintf ppf "%.12g" f
    | Oval_char c -> fprintf ppf "'%s'" (Char.escaped c)
    | IFDEF OCAML_VERSION < OCAML_4_06 THEN
      Oval_string s ->
        try fprintf ppf "\"%s\"" (String.escaped s) with
        [ Invalid_argument _ -> fprintf ppf "<huge string>" ]
      ELSE
      Oval_string s _ _ ->
        try fprintf ppf "\"%s\"" (String.escaped s) with
        [ Invalid_argument _ -> fprintf ppf "<huge string>" ]
      END
    | Oval_list tl ->
        fprintf ppf "@[<1>[%a]@]" (print_tree_list print_tree ";") tl
    | Oval_array tl ->
        fprintf ppf "@[<2>[|%a|]@]" (print_tree_list print_tree ";") tl
    | IFDEF OCAML_VERSION < OCAML_4_08_0 THEN
      Oval_constr (Oide_ident "true") [] -> fprintf ppf "True"
      ELSE
      Oval_constr (Oide_ident {printed_name = "true"}) [] ->
        fprintf ppf "True"
      END
    | IFDEF OCAML_VERSION < OCAML_4_08_0 THEN
      Oval_constr (Oide_ident "false") [] -> fprintf ppf "False"
      ELSE
      Oval_constr (Oide_ident {printed_name = "false"}) [] ->
        fprintf ppf "False"
      END
    | Oval_constr name [] -> print_ident ppf name
    | Oval_variant name None -> fprintf ppf "`%s" name
    | Oval_stuff s -> fprintf ppf "%s" s
    | Oval_record fel ->
        fprintf ppf "@[<1>{%a}@]" (cautious (print_fields True)) fel
    | Oval_tuple tree_list ->
        fprintf ppf "@[<1>(%a)@]" (print_tree_list print_tree ",") tree_list
    | Oval_ellipsis -> raise Ellipsis
    | Oval_printer f -> f ppf
    | tree -> fprintf ppf "@[<1>(%a)@]" (cautious print_tree) tree ]
  and print_fields first ppf =
    fun
    [ [] -> ()
    | [(name, tree) :: fields] ->
        let name =
          match name with
          | IFDEF OCAML_VERSION < OCAML_4_08_0 THEN
            Oide_ident "contents" -> Oide_ident "val"
            ELSE
            Oide_ident {printed_name = "contents"} ->
              Oide_ident {printed_name = "val"}
            END
          | x -> x
          end
        in
        do {
          if not first then fprintf ppf ";@ " else ();
          fprintf ppf "@[<1>%a=@,%a@]" print_ident name (cautious print_tree)
            tree;
          print_fields False ppf fields
        } ]
  and print_tree_list print_item sep ppf tree_list =
    let rec print_list first ppf =
      fun
      [ [] -> ()
      | [tree :: tree_list] ->
          do {
            if not first then fprintf ppf "%s@ " sep else ();
            print_item ppf tree;
            print_list False ppf tree_list
          } ]
    in
    cautious (print_list True) ppf tree_list
  in
  cautious print_tree ppf tree
;

value rec print_list pr sep ppf =
  fun
  [ [] -> ()
  | [a] -> pr ppf a
  | [a :: l] -> do { pr ppf a; sep ppf; print_list pr sep ppf l } ]
;

value pr_present =
  print_list (fun ppf s -> fprintf ppf "`%s" s) (fun ppf -> fprintf ppf "@ ")
;

value default_lang =
  try Sys.getenv "LC_ALL" with
  [ Not_found ->
      try Sys.getenv "LC_MESSAGES" with
      [ Not_found -> try Sys.getenv "LANG" with [ Not_found -> "" ] ] ]
;

value utf8 =
  let s = default_lang in
  let utf8_str = "utf-8" in
  let slen = String.length s in
  let ulen = String.length utf8_str in
  slen >= ulen &&
  string_lowercase (String.sub s (slen - ulen) ulen) = utf8_str
;

(* Type variables in Greek *)

value greek_tab =
  [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ";
     "ο"; "π"; "ρ"; "σ"; "τ"; "υ"; "φ"; "χ"; "ψ"; "ω" |]
;
value index_tab = [| ""; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉" |];

value try_greek s = do {
  if utf8 then do {
    if String.length s = 1 then do {
      let c = Char.code s.[0] - Char.code 'a' in
      let g = greek_tab.(c mod Array.length greek_tab) in
      let n = c / Array.length greek_tab in
      if n < Array.length index_tab then ("", g ^ index_tab.(n))
      else ("'", s)
    }
    else ("'", s)
  }
  else ("'", s)
};

(* Types *)

value rec print_out_type ppf =
  fun
  [ Otyp_alias ty s ->
      let (q, s) = try_greek s in
      fprintf ppf "@[%a as %s%s@]" print_out_type ty q s
  | ty -> print_out_type_1 ppf ty ]
and print_out_type_1 ppf =
  fun
  [ Otyp_arrow lab ty1 ty2 ->
      fprintf ppf "@[%s%a %s@ %a@]" (if lab <> "" then lab ^ ":" else "")
        print_out_type_2 ty1 (if utf8 then "→" else "->") print_out_type_1 ty2
  | ty -> print_out_type_2 ppf ty ]
and print_out_type_2 ppf =
  fun
  [ Otyp_constr id ([_ :: _] as tyl) ->
      fprintf ppf "@[%a@;<1 2>%a@]" print_ident id
        (print_typlist print_simple_out_type "") tyl
  | ty -> print_simple_out_type ppf ty ]
and print_simple_out_type ppf =
  fun
  [ Otyp_var ng s ->
      let (q, s) = try_greek s in
      fprintf ppf "%s%s%s" q (if ng then "_" else "") s
  | Otyp_constr id [] -> fprintf ppf "@[%a@]" print_ident id
  | Otyp_tuple tyl ->
      fprintf ppf "@[<1>(%a)@]" (print_typlist print_out_type " *") tyl
  | Otyp_stuff s -> fprintf ppf "%s" s
  | Otyp_variant non_gen poly_variants closed tags ->
      let print_present ppf =
        fun
        [ None | Some [] -> ()
        | Some l -> fprintf ppf "@;<1 -2>> @[<hov>%a@]" pr_present l ]
      in
      let print_fields ppf =
        fun
        | Ovar_fields fields ->
            print_list print_poly_variant
              (fun ppf -> fprintf ppf "@;<1 -2>| ") ppf fields
        | IFDEF OCAML_VERSION < OCAML_4_05_0 THEN
          Ovar_name id tyl ->
            fprintf ppf "@[%a%a@]" print_typargs tyl print_ident id
          ELSE
          Ovar_typ ty ->
            fprintf ppf "%a@ " print_simple_out_type ty
          END
        end
      in
      fprintf ppf "%s[%s@[<hv>@[<hv>%a@]%a ]@]" (if non_gen then "_" else "")
        (if closed then if tags = None then "= " else "< "
         else if tags = None then "> "
         else "? ")
        print_fields poly_variants
        print_present tags
  | Otyp_object fields rest ->
      fprintf ppf "@[<2>< %a >@]" (print_fields rest) fields
  | Otyp_class ng id tyl ->
      fprintf ppf "@[%a%s#%a@]" print_typargs tyl (if ng then "_" else "")
        print_ident id
  | Otyp_manifest ty1 ty2 ->
      fprintf ppf "@[<2>%a ==@ %a@]" print_out_type ty1 print_out_type ty2
  | Otyp_abstract -> fprintf ppf "'abstract"
  | IFDEF OCAML_VERSION >= OCAML_4_02_0 THEN
    Otyp_open -> fprintf ppf "open"
    END
  | Otyp_alias _ _ | Otyp_arrow _ _ _ | Otyp_constr _ [_ :: _] as ty ->
      fprintf ppf "@[<1>(%a)@]" print_out_type ty
  | IFDEF OCAML_VERSION >= OCAML_3_05 THEN
      Otyp_poly _ _ as ty ->
        fprintf ppf "@[<1>(%a)@]" print_out_type ty
    END
  | IFDEF OCAML_VERSION >= OCAML_3_12_0 THEN
      Otyp_module p n tyl -> do {
        IFDEF OCAML_VERSION < OCAML_4_08_0 THEN
          fprintf ppf "@[<1>(module %s" p
        ELSE
          fprintf ppf "@[<1>(module %a" print_ident p
        END;
        let first = ref True in
        List.iter2
          (fun s t ->
             let sep =
               if first.val then do { first.val := False; "with" } else "and"
             in
             fprintf ppf " %s type %s = %a" sep s print_out_type t)
          n tyl;
        fprintf ppf ")@]"
      }
    END
  | IFDEF OCAML_VERSION >= OCAML_3_13_0 AND NOT JOCAML THEN
      Otyp_sum constrs ->
        fprintf ppf "@[<hv>[ %a ]@]"
          (print_list print_out_constr_gadt_opt
             (fun ppf -> fprintf ppf "@ | "))
          constrs
    ELSIFDEF OCAML_VERSION > OCAML_3_06 AND OCAML_VERSION <= OCAML_3_08_4 THEN
      Otyp_sum constrs _ ->
        fprintf ppf "@[<hv>[ %a ]@]"
          (print_list print_out_constr (fun ppf -> fprintf ppf "@ | "))
          constrs
    ELSE
      Otyp_sum constrs ->
        fprintf ppf "@[<hv>[ %a ]@]"
          (print_list print_out_constr (fun ppf -> fprintf ppf "@ | "))
          constrs
    END
  | IFDEF OCAML_VERSION > OCAML_3_06 AND OCAML_VERSION <= OCAML_3_08_4 THEN
      Otyp_record lbls _ ->
        fprintf ppf "@[<hv 2>{ %a }@]"
          (print_list print_out_label (fun ppf -> fprintf ppf ";@ ")) lbls
    ELSE
      Otyp_record lbls ->
        fprintf ppf "@[<hv 2>{ %a }@]"
          (print_list print_out_label (fun ppf -> fprintf ppf ";@ ")) lbls
    END
  | IFDEF OCAML_VERSION >= OCAML_4_03_0 THEN
      Otyp_attribute _ _ -> ()
    END
  | IFDEF JOCAML THEN
      Otyp_proc ->
        failwith "Rprint: Otyp_proc not impl"
    END ]
and print_out_constr ppf (name, tyl) =
  match tyl with
  [ [] -> fprintf ppf "%s" name
  | _ ->
      fprintf ppf "@[<2>%s of@ %a@]" name
        (print_typlist print_out_type " and") tyl ]
and print_out_constr_gadt_opt ppf (name, tyl, rto) =
  match rto with
  [ Some rt ->
      let t = List.fold_right (fun t1 t2 -> Otyp_arrow "" t1 t2) tyl rt in
      fprintf ppf "%s : %a" name print_out_type t
  | None -> print_out_constr ppf (name, tyl) ]
and print_out_label ppf (name, mut, arg) =
  fprintf ppf "@[<2>%s :@ %s%a@]" name (if mut then "mutable " else "")
    print_out_type arg
and print_fields rest ppf =
  fun
  [ [] ->
      match rest with
      [ Some non_gen -> fprintf ppf "%s.." (if non_gen then "_" else "")
      | None -> () ]
  | [(s, t)] ->
      do {
        fprintf ppf "%s : %a" s print_out_type t;
        match rest with
        [ Some _ -> fprintf ppf ";@ "
        | None -> () ];
        print_fields rest ppf []
      }
  | [(s, t) :: l] ->
      fprintf ppf "%s : %a;@ %a" s print_out_type t (print_fields rest) l ]
and print_poly_variant ppf (l, opt_amp, tyl) =
  let pr_of ppf =
    if opt_amp then fprintf ppf " of@ &@ "
    else if tyl <> [] then fprintf ppf " of@ "
    else fprintf ppf ""
  in
  fprintf ppf "@[<hv 2>`%s%t%a@]" l pr_of (print_typlist print_out_type " &")
    tyl
and print_typlist print_elem sep ppf =
  fun
  [ [] -> ()
  | [ty] -> print_elem ppf ty
  | [ty :: tyl] ->
      fprintf ppf "%a%s@ %a" print_elem ty sep (print_typlist print_elem sep)
        tyl ]
and print_typargs ppf =
  fun
  [ [] -> ()
  | [ty1] -> fprintf ppf "%a@ " print_simple_out_type ty1
  | tyl ->
      fprintf ppf "@[<1>(%a)@]@ " (print_typlist print_out_type ",") tyl ]
;

value print_out_class_params ppf =
  fun
  [ [] -> ()
  | tyl ->
      fprintf ppf "@[<1>[%a]@]@ "
        (print_list (fun ppf (x, _) -> fprintf ppf "'%s" x)
           (fun ppf -> fprintf ppf ", "))
        tyl ]
;

(* Signature items *)

value rec print_out_class_type ppf =
  fun
  [ Octy_constr id tyl ->
      let pr_tyl ppf =
        fun
        [ [] -> ()
        | tyl ->
            fprintf ppf "@[<1>[%a]@]@ "
              (print_typlist print_out_type ",") tyl ]
      in
      fprintf ppf "@[%a%a@]" pr_tyl tyl print_ident id
  | IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Octy_fun lab ty cty ->
      fprintf ppf "@[%s[ %a ] ->@ %a@]" (if lab <> "" then lab ^ ":" else "")
        print_out_type ty print_out_class_type cty
    ELSE
    Octy_arrow lab ty cty ->
      fprintf ppf "@[%s[ %a ] ->@ %a@]" (if lab <> "" then lab ^ ":" else "")
        print_out_type ty print_out_class_type cty
    END
  | Octy_signature self_ty csil ->
      let pr_param ppf =
        fun
        [ Some ty -> fprintf ppf "@ @[(%a)@]" print_out_type ty
        | None -> () ]
      in
      fprintf ppf "@[<hv 2>@[<2>object%a@]@ %a@;<1 -2>end@]" pr_param self_ty
        (print_list print_out_class_sig_item (fun ppf -> fprintf ppf "@ "))
        csil ]
and print_out_class_sig_item ppf =
  fun
  [ Ocsg_constraint ty1 ty2 ->
      fprintf ppf "@[<2>type %a =@ %a;@]" print_out_type ty1
        print_out_type ty2
  | Ocsg_method name priv virt ty ->
      fprintf ppf "@[<2>method %s%s%s :@ %a;@]"
        (if priv then "private " else "") (if virt then "virtual " else "")
        name print_out_type ty
  | x ->
      IFDEF OCAML_VERSION >= OCAML_3_10 THEN
        failwith "Rprint.print_out_class_sig_item: not impl"
      ELSE
        match x with
        [ Ocsg_value name mut ty ->
            fprintf ppf "@[<2>value %s%s :@ %a;@]"
               (if mut then "mutable " else "") name
               print_out_type ty
        | _ -> assert False ]
      END ]
;

value rec print_out_module_type ppf =
  fun
  [ Omty_ident id -> fprintf ppf "%a" print_ident id
  | Omty_signature sg ->
      fprintf ppf "@[<hv 2>sig@ %a@;<1 -2>end@]" print_out_signature sg
  | Omty_functor name mty_arg mty_res ->
      IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
        fprintf ppf "@[<2>functor@ (%s : %a) ->@ %a@]" name
          print_out_module_type mty_arg print_out_module_type mty_res
      ELSE
        match mty_arg with
        [ Some mty_arg ->
            fprintf ppf "@[<2>functor@ (%s : %a) ->@ %a@]" name
              print_out_module_type mty_arg print_out_module_type mty_res
        | None ->
            fprintf ppf "@[<2>functor@ (%s) ->@ %a@]" name
              print_out_module_type mty_res ]
      END
  | Omty_abstract -> ()
  | IFDEF OCAML_VERSION >= OCAML_4_02_0 THEN
    Omty_alias oi -> fprintf ppf "<rprint.ml: Omty_alias not impl>"
    END ]
and print_out_signature ppf =
  fun
  [ [] -> ()
  | [item] -> fprintf ppf "%a;" print_out_sig_item item
  | [item :: items] ->
      fprintf ppf "%a;@ %a" print_out_sig_item item
        print_out_signature items ]
and print_out_sig_item ppf =
  fun
  [ IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Osig_exception id tyl ->
      fprintf ppf "@[<2>exception %a@]" print_out_constr (id, tyl)
    END
  | Osig_modtype name Omty_abstract ->
      fprintf ppf "@[<2>module type %s = 'a@]" name
  | Osig_modtype name mty ->
      fprintf ppf "@[<2>module type %s =@ %a@]" name print_out_module_type mty
  | IFDEF OCAML_VERSION <= OCAML_3_07 THEN
      Osig_module name mty ->
        fprintf ppf "@[<2>module %s :@ %a@]" name print_out_module_type mty
    ELSE
      Osig_module name mty _ ->
        fprintf ppf "@[<2>module %s :@ %a@]" name
          print_out_module_type mty
    END
  | IFDEF OCAML_VERSION <= OCAML_3_07 THEN
      Osig_type tdl -> do {
        print_out_type_decl "type" ppf (List.hd tdl);
        List.iter (print_out_type_decl "and" ppf) (List.tl tdl);
      }
    ELSE
      Osig_type td rs ->
        print_out_type_decl (if rs = Orec_next then "and" else "type" )
          ppf td
    END
  | IFDEF OCAML_VERSION < OCAML_4_03 THEN
      Osig_value name ty prims ->
        let kwd = if prims = [] then "value" else "external" in
        let pr_prims ppf =
          fun
          [ [] -> ()
          | [s :: sl] ->
              do {
                fprintf ppf "@ = \"%s\"" s;
                List.iter (fun s -> fprintf ppf "@ \"%s\"" s) sl
              } ]
        in
        fprintf ppf "@[<2>%s %a :@ %a%a@]" kwd value_ident name
          print_out_type ty pr_prims prims
    ELSE
      Osig_value ovd ->
        let name = ovd.oval_name in
        let ty = ovd.oval_type in
        let prims = ovd.oval_prims in
        let kwd = if prims = [] then "value" else "external" in
        let pr_prims ppf =
          fun
          [ [] -> ()
          | [s :: sl] ->
              do {
                fprintf ppf "@ = \"%s\"" s;
                List.iter (fun s -> fprintf ppf "@ \"%s\"" s) sl
              } ]
        in
        fprintf ppf "@[<2>%s %a :@ %a%a@]" kwd value_ident name
          print_out_type ty pr_prims prims
      END
  | x ->
      IFDEF OCAML_VERSION <= OCAML_3_08_4 THEN
        failwith "Rprint.print_out_sig_item: not implemented case"
      ELSE
        match x with
        [ Osig_class vir_flag name params clt _ ->
            fprintf ppf "@[<2>class%s@ %a%s@ :@ %a@]"
              (if vir_flag then " virtual" else "") print_out_class_params
              params name print_out_class_type clt
        | Osig_class_type vir_flag name params clt _ ->
            fprintf ppf "@[<2>class type%s@ %a%s@ =@ %a@]"
              (if vir_flag then " virtual" else "") print_out_class_params
              params name print_out_class_type clt
        | _ -> assert False ]
      END ]
and print_out_type_decl kwd ppf x =
  let (name, args, ty, priv, constraints) =
    IFDEF OCAML_VERSION <= OCAML_3_08_4 THEN
      let (name, args, ty, priv) = x in
      (name, args, ty, priv, [])
    ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
      x
    ELSE
      (x.otype_name, x.otype_params, x.otype_type, x.otype_private,
       x.otype_cstrs)
    END
  in
  let constrain ppf (ty, ty') =
    fprintf ppf "@ @[<2>constraint %a =@ %a@]" print_out_type ty
      print_out_type ty'
  in
  let print_constraints ppf params = List.iter (constrain ppf) params in
  let type_parameter ppf (ty, (co, cn)) =
    let (q, ty) = try_greek ty in
    fprintf ppf "%s%s%s" (if not cn then "+" else if not co then "-" else "")
      q ty
  in
  let type_defined ppf =
    match args with
    [ [] -> fprintf ppf "%s" name
    | [arg] -> fprintf ppf "%s %a" name type_parameter arg
    | _ ->
        fprintf ppf "%s@ %a" name
          (print_list type_parameter (fun ppf -> fprintf ppf "@ ")) args ]
  in
  fprintf ppf "@[<2>@[<hv 2>@[%s %t@] =@ %a@]%a@]" kwd type_defined
    print_out_type ty print_constraints constraints
;

(* Phrases *)

value print_out_exception ppf exn outv =
  match exn with
  [ Sys.Break -> fprintf ppf "Interrupted.@."
  | Out_of_memory -> fprintf ppf "Out of memory during evaluation.@."
  | Stack_overflow ->
      fprintf ppf "Stack overflow during evaluation (looping recursion?).@."
  | _ ->
      fprintf ppf "@[Exception:@ %a.@]@." print_out_value outv ]
;

value rec print_items ppf =
  fun
  [ [] -> ()
  | [(tree, valopt) :: items] ->
      do {
        match valopt with
        [ Some v ->
            fprintf ppf "@[<2>%a =@ %a@]" print_out_sig_item tree
              print_out_value v
        | None -> fprintf ppf "@[%a@]" print_out_sig_item tree ];
        if items <> [] then fprintf ppf "@ %a" print_items items else ()
      } ]
;

value print_out_phrase ppf =
  fun
  [ Ophr_eval outv ty ->
      fprintf ppf "@[- : %a@ =@ %a@]@." print_out_type ty print_out_value
        outv
  | Ophr_signature [] -> ()
  | Ophr_signature items -> fprintf ppf "@[<v>%a@]@." print_items items
  | Ophr_exception (exn, outv) -> print_out_exception ppf exn outv ]
;

Toploop.print_out_value.val := print_out_value;
Toploop.print_out_type.val := print_out_type;
IFDEF OCAML_VERSION >= OCAML_3_05 THEN
  Toploop.print_out_class_type.val := print_out_class_type;
  Toploop.print_out_module_type.val := print_out_module_type;
  Toploop.print_out_signature.val := print_out_signature;
END;
Toploop.print_out_sig_item.val := print_out_sig_item;
Toploop.print_out_phrase.val := print_out_phrase;

END;
