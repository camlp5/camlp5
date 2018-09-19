(* camlp5r pa_macro.cmo *)
(* versdep.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Parsetree;
open Longident;
open Asttypes;

type choice 'a 'b =
  [ Left of 'a
  | Right of 'b ]
;

value option_map f x =
  match x with
  | Some x -> Some (f x)
  | None -> None
  end
;

value ocaml_name = IFDEF JOCAML THEN "jocaml" ELSE "ocaml" END;

value sys_ocaml_version =
  IFDEF OCAML_1_06 THEN "1.06"
  ELSIFDEF OCAML_1_07 THEN "1.07"
  ELSIFDEF OCAML_2_00 THEN "2.00"
  ELSIFDEF OCAML_2_01 THEN "2.01"
  ELSIFDEF OCAML_2_02 THEN "2.02"
  ELSIFDEF OCAML_2_03 THEN "2.03"
  ELSIFDEF OCAML_2_04 THEN "2.04"
  ELSIFDEF OCAML_2_99 THEN "2.99"
  ELSIFDEF OCAML_3_00 THEN "3.00"
  ELSIFDEF OCAML_3_01 THEN "3.01"
  ELSIFDEF OCAML_3_02 THEN "3.02"
  ELSIFDEF OCAML_3_03 THEN "3.03"
  ELSIFDEF OCAML_3_04 THEN "3.04"
  ELSIFDEF OCAML_3_13_0_gadt THEN "3.13.0-gadt"
  ELSE Sys.ocaml_version END
;

value ocaml_location (fname, lnum, bolp, lnuml, bolpl, bp, ep) =
  IFDEF OCAML_VERSION <= OCAML_2_02 THEN
    {Location.loc_start = bp; Location.loc_end = ep}
  ELSIFDEF OCAML_VERSION <= OCAML_3_06 THEN
    {Location.loc_start = bp; Location.loc_end = ep;
     Location.loc_ghost = bp = 0 && ep = 0}
  ELSE
    let loc_at n lnum bolp =
      {Lexing.pos_fname = if lnum = -1 then "" else fname;
       Lexing.pos_lnum = lnum; Lexing.pos_bol = bolp; Lexing.pos_cnum = n}
    in
    {Location.loc_start = loc_at bp lnum bolp;
     Location.loc_end = loc_at ep lnuml bolpl;
     Location.loc_ghost = bp = 0 && ep = 0}
  END
;

IFDEF OCAML_VERSION >= OCAML_3_01_1 THEN
value loc_none =
  let loc =
    {Lexing.pos_fname = "_none_"; pos_lnum = 1; pos_bol = 0; pos_cnum = -1}
  in
  {Location.loc_start = loc;
   Location.loc_end = loc;
   Location.loc_ghost = True}
;
END;

value mkloc loc txt =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN txt
  ELSE {Location.txt = txt; loc = loc} END
;
value mknoloc txt =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN txt
  ELSE mkloc loc_none txt END
;

value ocaml_id_or_li_of_string_list loc sl =
  IFDEF OCAML_VERSION < OCAML_3_13_0 OR JOCAML THEN
    match List.rev sl with
    [ [s] -> Some s
    | _ -> None ]
  ELSE
    let mkli s =
      loop (fun s -> Lident s) where rec loop f =
        fun
        [ [i :: il] -> loop (fun s -> Ldot (f i) s) il
        | [] -> f s ]
    in
    match List.rev sl with
    [ [] -> None
    | [s :: sl] -> Some (mkli s (List.rev sl)) ]
  END
;

value list_map_check f l =
  loop [] l where rec loop rev_l =
    fun
    [ [x :: l] ->
        match f x with
        [ Some s -> loop [s :: rev_l] l
        | None -> None ]
    | [] -> Some (List.rev rev_l) ]
;

IFDEF OCAML_VERSION >= OCAML_4_03_0 THEN
  value labelled lab =
    if lab = "" then Nolabel
    else if lab.[0] = '?' then
      Optional (String.sub lab 1 (String.length lab - 1))
    else Labelled lab;
END;

IFDEF OCAML_VERSION > OCAML_3_01_1 AND OCAML_VERSION < OCAML_4_03_0 THEN
  value mkopt t lab =
    if lab = "" then t
    else if lab.[0] = '?' then
      IFDEF OCAML_VERSION < OCAML_3_11_0 THEN
        {ptyp_desc = Ptyp_constr (mknoloc (Lident "option")) [t];
         ptyp_loc = loc_none}
      ELSIFDEF OCAML_VERSION < OCAML_4_02 THEN
        {ptyp_desc =
           Ptyp_constr (mknoloc (Ldot (Lident "*predef*") "option")) [t];
         ptyp_loc = loc_none}
      ELSE
        {ptyp_desc =
           Ptyp_constr (mknoloc (Ldot (Lident "*predef*") "option")) [t];
         ptyp_loc = loc_none;
         ptyp_attributes = []}
      END
    else t
  ;
END;

value ocaml_value_description vn t p =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN {pval_type = t; pval_prim = p}
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    {pval_type = t; pval_prim = p; pval_loc = t.ptyp_loc}
  ELSE
    {pval_type = t; pval_prim = p; pval_loc = t.ptyp_loc;
     pval_name = mkloc t.ptyp_loc vn; pval_attributes = []}
  END
;

value ocaml_class_type_field loc ctfd =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN ctfd
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    {pctf_desc = ctfd; pctf_loc = loc}
  ELSE
    {pctf_desc = ctfd; pctf_loc = loc; pctf_attributes = []}
  END
;

value ocaml_class_field loc cfd =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN cfd
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN {pcf_desc = cfd; pcf_loc = loc}
  ELSE {pcf_desc = cfd; pcf_loc = loc; pcf_attributes = []} END
;

value ocaml_mktyp loc x =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN {ptyp_desc = x; ptyp_loc = loc}
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    {ptyp_desc = x; ptyp_loc = loc; ptyp_attributes = []}
  ELSE
    {ptyp_desc = x; ptyp_loc = loc; ptyp_loc_stack = []; ptyp_attributes = []}
  END
;
value ocaml_mkpat loc x =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN {ppat_desc = x; ppat_loc = loc}
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    {ppat_desc = x; ppat_loc = loc; ppat_attributes = []}
  ELSE
    {ppat_desc = x; ppat_loc = loc; ppat_loc_stack = []; ppat_attributes = []}
  END
;
value ocaml_mkexp loc x =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN {pexp_desc = x; pexp_loc = loc}
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    {pexp_desc = x; pexp_loc = loc; pexp_attributes = []}
  ELSE
    {pexp_desc = x; pexp_loc = loc; pexp_loc_stack = []; pexp_attributes = []}
  END
;
value ocaml_mkmty loc x =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN {pmty_desc = x; pmty_loc = loc}
  ELSE {pmty_desc = x; pmty_loc = loc; pmty_attributes = []} END
;
value ocaml_mkmod loc x =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN {pmod_desc = x; pmod_loc = loc}
  ELSE {pmod_desc = x; pmod_loc = loc; pmod_attributes = []} END
;
value ocaml_mkfield loc (lab, x) fl =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    [{pfield_desc = Pfield lab x; pfield_loc = loc} :: fl]
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    [(lab, x) :: fl]
  ELSE
    [{pof_desc = Otag (mkloc loc lab) x; pof_loc = loc;
      pof_attributes = []} :: fl]
  END
;
value ocaml_mkfield_var loc =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    [{pfield_desc = Pfield_var; pfield_loc = loc}]
  ELSE [] END
;

IFDEF OCAML_VERSION >= OCAML_4_02_0 THEN
  value variance_of_bool_bool =
    fun
    [ (False, True) -> Contravariant
    | (True, False) -> Covariant
    | _ -> Invariant ]
  ;
END;

value ocaml_type_declaration tn params cl tk pf tm loc variance =
  IFDEF OCAML_VERSION = OCAML_3_13_0_gadt THEN
    Right
      {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
       ptype_private = pf; ptype_manifest = tm; ptype_loc = loc;
       ptype_variance = variance}
  ELSE
    match list_map_check (fun s_opt -> s_opt) params with
    [ Some params ->
        IFDEF OCAML_VERSION <= OCAML_1_07 THEN
          let cl_opt =
            list_map_check
              (fun (t1, t2, loc) ->
                 match t1.ptyp_desc with
                 [ Ptyp_var s -> Some (s, t2, loc)
                 | _ -> None ])
              cl
          in
          match cl_opt with
          [ Some cl ->
              Right
                {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
                 ptype_manifest = tm; ptype_loc = loc}
          | None ->
               Left "no such 'with' constraint in this ocaml version" ]
        ELSIFDEF OCAML_VERSION <= OCAML_3_00 THEN
          Right
            {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
             ptype_manifest = tm; ptype_loc = loc}
        ELSIFDEF OCAML_VERSION < OCAML_3_11 THEN
          Right
            {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
             ptype_manifest = tm; ptype_loc = loc; ptype_variance = variance}
        ELSIFDEF OCAML_VERSION < OCAML_3_13_0 OR JOCAML THEN
          Right
            {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
             ptype_private = pf; ptype_manifest = tm; ptype_loc = loc;
             ptype_variance = variance}
        ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
          let params = List.map (fun os -> Some (mkloc loc os)) params in
          Right
            {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
             ptype_private = pf; ptype_manifest = tm; ptype_loc = loc;
             ptype_variance = variance}
        ELSE
          let _ =
            if List.length params <> List.length variance then
              failwith "internal error: ocaml_type_declaration"
            else ()
          in
          let params =
            List.map2
              (fun os va ->
                 (ocaml_mktyp loc (Ptyp_var os), variance_of_bool_bool va))
              params variance
          in
          Right
            {ptype_params = params; ptype_cstrs = cl; ptype_kind = tk;
             ptype_private = pf; ptype_manifest = tm; ptype_loc = loc;
             ptype_name = mkloc loc tn; ptype_attributes = []}
        END
    | None -> Left "no '_' type param in this ocaml version" ]
  END
;

value ocaml_class_type =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun d loc -> {pcty_desc = d; pcty_loc = loc})
  ELSE
    Some (fun d loc -> {pcty_desc = d; pcty_loc = loc; pcty_attributes = []})
  END
;

value ocaml_class_expr =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun d loc -> {pcl_desc = d; pcl_loc = loc})
  ELSE
    Some (fun d loc -> {pcl_desc = d; pcl_loc = loc; pcl_attributes = []})
  END
;

value ocaml_class_structure p cil =
  IFDEF OCAML_VERSION <= OCAML_4_00 THEN (p, cil)
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    {pcstr_pat = p; pcstr_fields = cil}
  ELSE {pcstr_self = p; pcstr_fields = cil} END
;

value ocaml_pmty_ident loc li = Pmty_ident (mkloc loc li);

value ocaml_pmty_functor sloc s mt1 mt2 =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pmty_functor (mkloc sloc s) mt1 mt2
  ELSE Pmty_functor (mkloc sloc s) (Some mt1) mt2 END
;

value ocaml_pmty_typeof =
  IFDEF OCAML_VERSION < OCAML_3_12 THEN None
  ELSE Some (fun me -> Pmty_typeof me) END
;

value ocaml_pmty_with mt lcl =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    let lcl = List.map (fun (s, c) → (mknoloc s, c)) lcl in
    Pmty_with mt lcl
  ELSE
    let lcl = List.map snd lcl in Pmty_with mt lcl
  END
;

value ocaml_ptype_abstract =
  IFDEF OCAML_VERSION <= OCAML_3_08_4 OR OCAML_VERSION >= OCAML_3_11 THEN
    Ptype_abstract
  ELSE
    Ptype_private
  END
;

value ocaml_ptype_record ltl priv =
  IFDEF OCAML_VERSION <= OCAML_3_08_4 THEN
    let ltl = List.map (fun (n, m, t, _) -> (n, m, t)) ltl in
    IFDEF OCAML_VERSION <= OCAML_3_06 THEN
      Ptype_record ltl
    ELSE
      let priv = if priv then Private else Public in
      Ptype_record ltl priv
    END
  ELSIFDEF OCAML_VERSION < OCAML_3_11 THEN
    let priv = if priv then Private else Public in
    Ptype_record ltl priv
  ELSIFDEF OCAML_VERSION < OCAML_4_00 THEN
    Ptype_record ltl
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Ptype_record
      (List.map (fun (s, mf, ct, loc) → (mkloc loc s, mf, ct, loc)) ltl)
  ELSE
    Ptype_record
      (List.map
         (fun (s, mf, ct, loc) ->
            {pld_name = mkloc loc s; pld_mutable = mf; pld_type = ct;
             pld_loc = loc; pld_attributes = []})
         ltl)
  END
;

value ocaml_ptype_variant ctl priv =
  IFDEF OCAML_VERSION = OCAML_3_13_0_gadt THEN
    Some (Ptype_variant ctl)
  ELSE
    try
      IFDEF OCAML_VERSION <= OCAML_3_08_4 THEN
        let ctl =
          List.map
            (fun (c, tl, rto, loc) ->
               if rto <> None then raise Exit else (c, tl))
            ctl
        in
        IFDEF OCAML_VERSION <= OCAML_3_06 THEN
          Some (Ptype_variant ctl)
        ELSE
          let priv = if priv then Private else Public in
          Some (Ptype_variant ctl priv)
        END
      ELSIFDEF OCAML_VERSION < OCAML_3_11 THEN
        let ctl =
          List.map
            (fun (c, tl, rto, loc) ->
               if rto <> None then raise Exit else (c, tl, loc))
            ctl
        in
          let priv = if priv then Private else Public in
          Some (Ptype_variant ctl priv)
      ELSIFDEF OCAML_VERSION < OCAML_3_13_0 OR JOCAML THEN
        let ctl =
          List.map
            (fun (c, tl, rto, loc) ->
               if rto <> None then raise Exit else (c, tl, loc))
            ctl
        in
          Some (Ptype_variant ctl)
      ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
        let ctl =
          List.map
            (fun (c, tl, rto, loc) ->
               if rto <> None then raise Exit else (mknoloc c, tl, None, loc))
            ctl
        in
          Some (Ptype_variant ctl)
      ELSE
        let ctl =
          List.map
            (fun (c, tl, rto, loc) ->
               if rto <> None then raise Exit
               else
                 IFDEF OCAML_VERSION < OCAML_4_03_0 THEN
                   {pcd_name = mkloc loc c; pcd_args = tl; pcd_res = None;
                    pcd_loc = loc; pcd_attributes = []}
                 ELSE
                   let tl = Pcstr_tuple tl in
                   {pcd_name = mkloc loc c; pcd_args = tl; pcd_res = None;
                    pcd_loc = loc; pcd_attributes = []}
                 END)
            ctl
        in
        Some (Ptype_variant ctl)
      END
    with
    [ Exit -> None ]
  END
;

value ocaml_ptyp_arrow lab t1 t2 =
  IFDEF OCAML_VERSION < OCAML_3_00 THEN Ptyp_arrow t1 t2
  ELSIFDEF OCAML_VERSION <= OCAML_3_01 THEN Ptyp_arrow lab t1 t2
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN Ptyp_arrow lab (mkopt t1 lab) t2
  ELSE Ptyp_arrow (labelled lab) t1 t2 END
;

value ocaml_ptyp_class li tl ll =
  IFDEF OCAML_VERSION <= OCAML_2_04 THEN Ptyp_class li tl
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Ptyp_class (mknoloc li) tl ll
  ELSE Ptyp_class (mknoloc li) tl END
;

value ocaml_ptyp_constr loc li tl = Ptyp_constr (mkloc loc li) tl;

value ocaml_ptyp_object loc ml is_open =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Ptyp_object ml
  ELSIFDEF OCAML_VERSION < OCAML_4_05_0 THEN
    let ml = List.map (fun (s, t) -> (s, [], t)) ml in
    Ptyp_object ml (if is_open then Open else Closed)
  ELSIFDEF OCAML_VERSION < OCAML_4_06_0 THEN
    let ml = List.map (fun (s, t) -> (mkloc loc s, [], t)) ml in
    Ptyp_object ml (if is_open then Open else Closed)
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    let ml = List.map (fun (s, t) -> Otag (mkloc loc s) [] t) ml in
    Ptyp_object ml (if is_open then Open else Closed)
  ELSE
    Ptyp_object ml (if is_open then Open else Closed)
  END
;

value ocaml_ptyp_package =
  IFDEF OCAML_VERSION < OCAML_3_12_0 THEN None
  ELSE Some (fun pt -> Ptyp_package pt) END
;

value ocaml_ptyp_poly =
  IFDEF OCAML_VERSION <= OCAML_3_04 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun loc cl t -> Ptyp_poly cl t)
  ELSIFDEF OCAML_VERSION < OCAML_4_05_0 THEN
    Some
      (fun loc cl t ->
         match cl with
         [ [] -> t.ptyp_desc
         | _ -> Ptyp_poly cl t ])
  ELSE
    Some
      (fun loc cl t ->
         match cl with
         [ [] -> t.ptyp_desc
         | _ -> Ptyp_poly (List.map (mkloc loc) cl) t ])
  END
;

value ocaml_ptyp_variant loc catl clos sl_opt =
  IFDEF OCAML_VERSION <= OCAML_2_04 THEN None
  ELSIFDEF OCAML_VERSION <= OCAML_3_02 THEN
    try
      let catl =
        List.map
          (fun
           [ Left (c, a, tl) -> (c, a, tl)
           | Right t -> raise Exit ])
          catl
      in
      let sl = match sl_opt with [ Some sl -> sl | None -> [] ] in
      Some (Ptyp_variant catl clos sl)
    with
    [ Exit -> None ]
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    let catl =
      List.map
        (fun
         [ Left (c, a, tl) -> Rtag c a tl
         | Right t -> Rinherit t ])
        catl
    in
    Some (Ptyp_variant catl clos sl_opt)
  ELSIFDEF OCAML_VERSION < OCAML_4_06_0 THEN
    let catl =
      List.map
        (fun
         [ Left (c, a, tl) -> Rtag c [] a tl
         | Right t -> Rinherit t ])
        catl
    in
    let clos = if clos then Closed else Open in
    Some (Ptyp_variant catl clos sl_opt)
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    let catl =
      List.map
        (fun
         [ Left (c, a, tl) -> Rtag (mkloc loc c) [] a tl
         | Right t -> Rinherit t ])
        catl
    in
    let clos = if clos then Closed else Open in
    Some (Ptyp_variant catl clos sl_opt)
  ELSE
    let catl =
      List.map
        (fun c ->
           let d =
             match c with
             | Left (c, a, tl) -> Rtag (mkloc loc c) a tl
             | Right t -> Rinherit t
             end
         in
	 {prf_desc = d; prf_loc = loc; prf_attributes = []})
      catl
    in
    let clos = if clos then Closed else Open in
    Some (Ptyp_variant catl clos sl_opt)
  END
;

value ocaml_package_type li ltl =
  (mknoloc li, List.map (fun (li, t) → (mkloc t.ptyp_loc li, t)) ltl)
;

value ocaml_pconst_char c =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN Const_char c
  ELSE Pconst_char c END
;
value ocaml_pconst_int i =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN Const_int i
  ELSE Pconst_integer (string_of_int i) None END
;
value ocaml_pconst_float s =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN Const_float s
  ELSE Pconst_float s None END
;

value ocaml_const_string s =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Const_string s
  ELSE Const_string s None END
;
value ocaml_pconst_string s so =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Const_string s
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN Const_string s so
  ELSE Pconst_string s so END
;

value pconst_of_const =
  IFDEF OCAML_VERSION <= OCAML_3_07 THEN
    fun
    [ Const_int i -> ocaml_pconst_int i
    | Const_char c -> ocaml_pconst_char c
    | Const_string s -> ocaml_pconst_string s None
    | Const_float s -> ocaml_pconst_float s ]
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN
    fun
    [ Const_int i -> ocaml_pconst_int i
    | Const_char c -> ocaml_pconst_char c
    | IFDEF OCAML_VERSION < OCAML_4_02 THEN
        Const_string s -> ocaml_pconst_string s None
      ELSE
        Const_string s so -> ocaml_pconst_string s so
      END
    | Const_float s -> ocaml_pconst_float s
    | Const_int32 i32 -> Const_int32 i32
    | Const_int64 i64 -> Const_int64 i64
    | Const_nativeint ni -> Const_nativeint ni ]
  ELSE
    fun
    [ Const_int i -> ocaml_pconst_int i
    | Const_char c -> ocaml_pconst_char c
    | Const_string s so -> ocaml_pconst_string s so
    | Const_float s -> ocaml_pconst_float s
    | Const_int32 i32 -> Pconst_integer (Int32.to_string i32) (Some 'l')
    | Const_int64 i64 -> Pconst_integer (Int64.to_string i64) (Some 'L')
    | Const_nativeint ni -> Pconst_integer (Nativeint.to_string ni) (Some 'n') ]
  END
;

value ocaml_const_int32 =
  IFDEF OCAML_VERSION <= OCAML_3_06 THEN None
  ELSE Some (fun s -> Const_int32 (Int32.of_string s)) END
;

value ocaml_const_int64 =
  IFDEF OCAML_VERSION <= OCAML_3_06 THEN None
  ELSE Some (fun s -> Const_int64 (Int64.of_string s)) END
;

value ocaml_const_nativeint =
  IFDEF OCAML_VERSION <= OCAML_3_06 THEN None
  ELSE Some (fun s -> Const_nativeint (Nativeint.of_string s)) END
;

value ocaml_pexp_apply f lel =
  IFDEF OCAML_VERSION <= OCAML_2_04 THEN Pexp_apply f (List.map snd lel)
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN Pexp_apply f lel
  ELSE Pexp_apply f (List.map (fun (l, e) -> (labelled l, e)) lel) END
;

value ocaml_pexp_assertfalse fname loc =
  IFDEF OCAML_VERSION <= OCAML_3_00 THEN
    let ghexp d = {pexp_desc = d; pexp_loc = loc} in
    let triple =
      ghexp (Pexp_tuple
             [ghexp (Pexp_constant (Const_string fname));
              ghexp (Pexp_constant (Const_int loc.Location.loc_start));
              ghexp (Pexp_constant (Const_int loc.Location.loc_end))])
    in
    let excep = Ldot (Lident "Pervasives") "Assert_failure" in
    let bucket = ghexp (Pexp_construct excep (Some triple) False) in
    let raise_ = ghexp (Pexp_ident (Ldot (Lident "Pervasives") "raise")) in
    ocaml_pexp_apply raise_ [("", bucket)]
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pexp_assertfalse
  ELSE
    Pexp_assert
      (ocaml_mkexp loc (Pexp_construct (mkloc loc (Lident "false")) None))
  END
;

value ocaml_pexp_assert fname loc e =
  IFDEF OCAML_VERSION <= OCAML_3_00 THEN
    let ghexp d = {pexp_desc = d; pexp_loc = loc} in
    let ghpat d = {ppat_desc = d; ppat_loc = loc} in
    let triple =
      ghexp (Pexp_tuple
             [ghexp (Pexp_constant (Const_string fname));
              ghexp (Pexp_constant (Const_int loc.Location.loc_start));
              ghexp (Pexp_constant (Const_int loc.Location.loc_end))])
    in
    let excep = Ldot (Lident "Pervasives") "Assert_failure" in
    let bucket = ghexp (Pexp_construct excep (Some triple) False) in
    let raise_ = ghexp (Pexp_ident (Ldot (Lident "Pervasives") "raise")) in
    let raise_af = ghexp (ocaml_pexp_apply raise_ [("", bucket)]) in
    let under = ghpat Ppat_any in
    let false_ = ghexp (Pexp_construct (Lident "false") None False) in
    let try_e = ghexp (Pexp_try e [(under, false_)]) in

    let not_ = ghexp (Pexp_ident (Ldot (Lident "Pervasives") "not")) in
    let not_try_e = ghexp (ocaml_pexp_apply not_ [("", try_e)]) in
    Pexp_ifthenelse not_try_e raise_af None
  ELSE Pexp_assert e END
;

value ocaml_pexp_constraint e ot1 ot2 =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pexp_constraint e ot1 ot2
  ELSE
    match ot2 with
    | Some t2 -> Pexp_coerce e ot1 t2
    | None ->
        match ot1 with
        | Some t1 -> Pexp_constraint e t1
        | None -> failwith "internal error: ocaml_pexp_constraint"
        end
    end
  END
;

value ocaml_pexp_construct loc li po chk_arity =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Pexp_construct (mkloc loc li) po chk_arity
  ELSE
    Pexp_construct (mkloc loc li) po
  END
;

value ocaml_pexp_construct_args =
  IFDEF OCAML_VERSION < OCAML_4_00_0 THEN
    fun
    [ Pexp_construct li po chk_arity -> Some (li, 0, po, chk_arity)
    | _ -> None ]
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    fun
    [ Pexp_construct li po chk_arity -> Some (li.txt, li.loc, po, chk_arity)
    | _ -> None ]
  ELSE
    fun
    [ Pexp_construct li po -> Some (li.txt, li.loc, po, 0)
    | _ -> None ]
  END
;

value mkexp_ocaml_pexp_construct_arity loc li_loc li al =
  let a = ocaml_mkexp loc (Pexp_tuple al) in
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    ocaml_mkexp loc (ocaml_pexp_construct li_loc li (Some a) True)
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    {pexp_desc = ocaml_pexp_construct li_loc li (Some a) True;
     pexp_loc = loc;
     pexp_attributes = [(mkloc loc "ocaml.explicit_arity", PStr [])]}
  ELSE
    {pexp_desc = ocaml_pexp_construct li_loc li (Some a) True;
     pexp_loc = loc; pexp_loc_stack = [];
     pexp_attributes =
       [{attr_name = mkloc loc "ocaml.explicit_arity";
         attr_payload = PStr []; attr_loc = loc}]}
  END
;

value ocaml_pexp_field loc e li = Pexp_field e (mkloc loc li);

value ocaml_pexp_for i e1 e2 df e =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pexp_for (mknoloc i) e1 e2 df e
  ELSE Pexp_for (ocaml_mkpat loc_none (Ppat_var (mknoloc i))) e1 e2 df e END
;

value ocaml_case (p, wo, loc, e) =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    match wo with
    | Some w -> (p, ocaml_mkexp loc (Pexp_when w e))
    | None -> (p, e)
    end
  ELSE
    {pc_lhs = p; pc_guard = wo; pc_rhs = e}
  END
;

value ocaml_pexp_function lab eo pel =
  IFDEF OCAML_VERSION <= OCAML_2_04 THEN Pexp_function pel
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pexp_function lab eo pel
  ELSE
    match pel with
    | [{pc_lhs = p; pc_guard = None; pc_rhs = e}] ->
        IFDEF OCAML_VERSION < OCAML_4_03_0 THEN Pexp_fun lab eo p e
        ELSE Pexp_fun (labelled lab) eo p e END
    | pel ->
        if lab = "" && eo = None then Pexp_function pel
        else failwith "internal error: bad ast in ocaml_pexp_function"
    end
  END
;

value ocaml_pexp_lazy =
  IFDEF OCAML_VERSION <= OCAML_3_04 THEN None
  ELSE Some (fun e -> Pexp_lazy e) END
;

value ocaml_pexp_ident loc li = Pexp_ident (mkloc loc li);

value ocaml_pexp_letmodule =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun i me e -> Pexp_letmodule (mknoloc i) me e) END
;

value ocaml_pexp_new loc li = Pexp_new (mkloc loc li);

value ocaml_pexp_newtype =
  IFDEF OCAML_VERSION < OCAML_3_12_0 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_05_0 THEN
    Some (fun loc s e -> Pexp_newtype s e)
  ELSE
    Some (fun loc s e -> Pexp_newtype (mkloc loc s) e)
  END
;

value ocaml_pexp_object =
  IFDEF OCAML_VERSION <= OCAML_3_07 THEN None
  ELSE Some (fun cs -> Pexp_object cs) END
;

value ocaml_pexp_open =
  IFDEF OCAML_VERSION < OCAML_3_12 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_01 THEN
    Some (fun li e -> Pexp_open (mknoloc li) e)
  ELSE
    Some (fun li e -> Pexp_open Fresh (mknoloc li) e)
  END
;

value ocaml_pexp_override sel =
  let sel = List.map (fun (s, e) → (mknoloc s, e)) sel in
  Pexp_override sel
;

value ocaml_pexp_pack =
  IFDEF OCAML_VERSION < OCAML_3_12 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_3_13_0 THEN
    Some (Left (fun me pt -> Pexp_pack me pt))
  ELSE
    (Some (Right (fun me -> Pexp_pack me, fun pt -> Ptyp_package pt)) :
     option (choice ('a -> 'b -> 'c) 'd))
  END
;

value ocaml_pexp_poly =
  IFDEF OCAML_VERSION <= OCAML_3_04 THEN None
  ELSE Some (fun e t -> Pexp_poly e t) END
;

value ocaml_pexp_record lel eo =
  let lel = List.map (fun (li, loc, e) → (mkloc loc li, e)) lel in
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN
    match eo with
    [ Some _ -> invalid_arg "ocaml_pexp_record"
    | None -> Pexp_record lel ]
  ELSE
    Pexp_record lel eo
  END
;

value ocaml_pexp_send loc e s =
  IFDEF OCAML_VERSION < OCAML_4_05_0 THEN Pexp_send e s
  ELSE Pexp_send e (mkloc loc s) END
;

value ocaml_pexp_setinstvar s e = Pexp_setinstvar (mknoloc s) e;

value ocaml_pexp_variant =
  IFDEF OCAML_VERSION <= OCAML_2_04 THEN None
  ELSE
    let pexp_variant_pat =
      fun
      [ Pexp_variant lab eo -> Some (lab, eo)
      | _ -> None ]
    in
    let pexp_variant (lab, eo) = Pexp_variant lab eo in
    Some (pexp_variant_pat, pexp_variant)
  END
;

value ocaml_value_binding loc p e =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN (p, e)
  ELSE {pvb_pat = p; pvb_expr = e; pvb_loc = loc; pvb_attributes = []} END
;

value ocaml_ppat_alias p i iloc = Ppat_alias p (mkloc iloc i);

value ocaml_ppat_array =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun pl -> Ppat_array pl) END
;

value ocaml_ppat_construct loc li po chk_arity  =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN
    Ppat_construct li po chk_arity
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Ppat_construct (mkloc loc li) po chk_arity
  ELSE
    Ppat_construct (mkloc loc li) po
  END
;

value ocaml_ppat_construct_args =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    fun
    [ Ppat_construct li po chk_arity ->
        IFDEF OCAML_VERSION < OCAML_4_00 THEN Some (li, 0, po, chk_arity)
        ELSE Some (li.txt, li.loc, po, chk_arity) END
    | _ -> None ]
  ELSE
    fun
    [ Ppat_construct li po -> Some (li.txt, li.loc, po, 0)
    | _ -> None ]
  END
;

value mkpat_ocaml_ppat_construct_arity loc li_loc li al =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    let a = ocaml_mkpat loc (Ppat_tuple al) in
    ocaml_mkpat loc (ocaml_ppat_construct li_loc li (Some a) True)
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    let a = ocaml_mkpat loc (Ppat_tuple al) in
    {ppat_desc = ocaml_ppat_construct li_loc li (Some a) True;
     ppat_loc = loc;
     ppat_attributes = [(mkloc loc "ocaml.explicit_arity", PStr [])]}
  ELSE
    let a = ocaml_mkpat loc (Ppat_tuple al) in
    {ppat_desc = ocaml_ppat_construct li_loc li (Some a) True;
     ppat_loc = loc; ppat_loc_stack = [];
     ppat_attributes =
       [{attr_name = mkloc loc "ocaml.explicit_arity";
         attr_payload = PStr []; attr_loc = loc}]}
  END
;

value ocaml_ppat_lazy =
  IFDEF OCAML_VERSION >= OCAML_3_11 THEN Some (fun p -> Ppat_lazy p)
  ELSE None END
;

value ocaml_ppat_record lpl is_closed =
  let lpl = List.map (fun (li, loc, p) → (mkloc loc li, p)) lpl in
  IFDEF OCAML_VERSION < OCAML_3_12 THEN Ppat_record lpl
  ELSE Ppat_record lpl (if is_closed then Closed else Open) END
;

value ocaml_ppat_type =
  IFDEF OCAML_VERSION <= OCAML_2_99 THEN None
  ELSE Some (fun loc li -> Ppat_type (mkloc loc li)) END
;

value ocaml_ppat_unpack =
  IFDEF OCAML_VERSION < OCAML_3_13_0 OR JOCAML THEN None
  ELSE
    Some (fun loc s -> Ppat_unpack (mkloc loc s), fun pt -> Ptyp_package pt)
  END
;

value ocaml_ppat_var loc s = Ppat_var (mkloc loc s);

value ocaml_ppat_variant =
  IFDEF OCAML_VERSION <= OCAML_2_04 THEN None
  ELSE
    let ppat_variant_pat =
      fun
      [ Ppat_variant lab po -> Some (lab, po)
      | _ -> None ]
    in
    let ppat_variant (lab, po) = Ppat_variant lab po in
    Some (ppat_variant_pat, ppat_variant)
  END
;

value ocaml_psig_class_type =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun ctl -> Psig_class_type ctl) END
;

value ocaml_psig_exception loc s ed =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Psig_exception (mkloc loc s) ed
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN
    Psig_exception
      {pext_name = mkloc loc s; pext_kind = Pext_decl ed None;
       pext_loc = loc; pext_attributes = []}
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    Psig_exception
      {pext_name = mkloc loc s; pext_kind = Pext_decl (Pcstr_tuple ed) None;
       pext_loc = loc; pext_attributes = []}
  ELSE
    Psig_exception
      {ptyexn_constructor =
         {pext_name = mkloc loc s;
          pext_kind = Pext_decl (Pcstr_tuple ed) None;
          pext_loc = loc; pext_attributes = []};
       ptyexn_attributes = [];
       ptyexn_loc = loc}
  END
;

value ocaml_psig_include loc mt =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Psig_include mt
  ELSE
    Psig_include {pincl_mod = mt; pincl_loc = loc; pincl_attributes = []}
  END
;

value ocaml_psig_module loc s mt =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Psig_module (mknoloc s) mt
  ELSE
    Psig_module
      {pmd_name = mkloc loc s; pmd_type = mt; pmd_attributes = [];
       pmd_loc = loc}
  END
;

value ocaml_psig_modtype loc s mto =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    let mtd =
      match mto with
      | None -> Pmodtype_abstract
      | Some t -> Pmodtype_manifest t
      end
    in
    Psig_modtype (mknoloc s) mtd
  ELSE
    let pmtd =
      {pmtd_name = mkloc loc s; pmtd_type = mto; pmtd_attributes = [];
       pmtd_loc = loc}
    in
    Psig_modtype pmtd
  END
;

value ocaml_psig_open loc li =
  IFDEF OCAML_VERSION < OCAML_4_01 THEN Psig_open (mkloc loc li)
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Psig_open Fresh (mkloc loc li)
  ELSE
    Psig_open
      {popen_lid = mknoloc li; popen_override = Fresh; popen_loc = loc;
       popen_attributes = []}
  END
;

value ocaml_psig_recmodule =
  IFDEF OCAML_VERSION <= OCAML_3_06 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    let f ntl =
      let ntl = List.map (fun (s, mt) → (mknoloc s, mt)) ntl in
      Psig_recmodule ntl
    in
    Some f
  ELSE
    let f ntl =
      let ntl =
        List.map
          (fun (s, mt) ->
             {pmd_name = mknoloc s; pmd_type = mt; pmd_attributes = [];
              pmd_loc = loc_none})
          ntl
      in
      Psig_recmodule ntl
    in
    Some f
  END
;

value ocaml_psig_type stl =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    let stl = List.map (fun (s, t) → (mknoloc s, t)) stl in
    Psig_type stl
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN
    let stl = List.map (fun (s, t) -> t) stl in Psig_type stl
  ELSE
    let stl = List.map (fun (s, t) -> t) stl in Psig_type Recursive stl
  END
;

value ocaml_psig_value s vd =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Psig_value (mknoloc s) vd
  ELSE Psig_value vd END
;

value ocaml_pstr_class_type =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun ctl -> Pstr_class_type ctl) END
;

value ocaml_pstr_eval e =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pstr_eval e
  ELSE Pstr_eval e [] END
;

value ocaml_pstr_exception loc s ed =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pstr_exception (mkloc loc s) ed
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN
    Pstr_exception
      {pext_name = mkloc loc s; pext_kind = Pext_decl ed None;
       pext_loc = loc; pext_attributes = []}
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    Pstr_exception
      {pext_name = mkloc loc s; pext_kind = Pext_decl (Pcstr_tuple ed) None;
       pext_loc = loc; pext_attributes = []}
  ELSE
    Pstr_exception
      {ptyexn_constructor =
         {pext_name = mkloc loc s;
          pext_kind = Pext_decl (Pcstr_tuple ed) None;
          pext_loc = loc; pext_attributes = []};
       ptyexn_attributes = [];
       ptyexn_loc = loc}
  END
;

value ocaml_pstr_exn_rebind =
  IFDEF OCAML_VERSION <= OCAML_2_99 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun loc s li -> Pstr_exn_rebind (mkloc loc s) (mkloc loc li))
  ELSIFDEF OCAML_VERSION < OCAML_4_08_0 THEN
    Some
      (fun loc s li ->
         Pstr_exception
           {pext_name = mkloc loc s; pext_kind = Pext_rebind (mkloc loc li);
            pext_loc = loc; pext_attributes = []})
  ELSE
    Some
      (fun loc s li ->
         Pstr_exception
           {ptyexn_constructor =
              {pext_name = mkloc loc s;
               pext_kind = Pext_rebind (mkloc loc li);
               pext_loc = loc; pext_attributes = []};
            ptyexn_attributes = [];
	    ptyexn_loc = loc})
  END
;

value ocaml_pstr_include =
  IFDEF OCAML_VERSION <= OCAML_3_00 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun loc me -> Pstr_include me)
  ELSE
    Some
      (fun loc me ->
         Pstr_include
           {pincl_mod = me; pincl_loc = loc; pincl_attributes = []})
  END
;

value ocaml_pstr_modtype loc s mt =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pstr_modtype (mkloc loc s) mt
  ELSE
    let pmtd =
      {pmtd_name = mkloc loc s; pmtd_type = Some mt; pmtd_attributes = [];
       pmtd_loc = loc}
    in
    Pstr_modtype pmtd
  END
;

value ocaml_pstr_module loc s me =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pstr_module (mkloc loc s) me
  ELSE
    let mb =
      {pmb_name = mkloc loc s; pmb_expr = me; pmb_attributes = [];
       pmb_loc = loc}
    in
    Pstr_module mb
  END
;

value ocaml_pstr_open loc li =
  IFDEF OCAML_VERSION < OCAML_4_01 THEN Pstr_open (mknoloc li)
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pstr_open Fresh (mknoloc li)
  ELSE
    Pstr_open
      {popen_lid = mknoloc li; popen_override = Fresh; popen_loc = loc;
       popen_attributes = []}
  END
;

value ocaml_pstr_primitive s vd =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pstr_primitive (mknoloc s) vd
  ELSE Pstr_primitive vd END
;

value ocaml_pstr_recmodule =
  IFDEF OCAML_VERSION <= OCAML_3_06 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_00 THEN
    Some (fun nel -> Pstr_recmodule nel)
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    let f nel =
      Pstr_recmodule (List.map (fun (s, mt, me) → (mknoloc s, mt, me)) nel)
    in
    Some f
  ELSE
    let f nel =
      Pstr_recmodule
        (List.map
           (fun (s, mt, me) ->
              {pmb_name = mknoloc s; pmb_expr = me; pmb_attributes = [];
               pmb_loc = loc_none})
           nel)
    in
    Some f
  END
;

value ocaml_pstr_type is_nonrec stl =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN Pstr_type stl
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    let stl = List.map (fun (s, t) → (mknoloc s, t)) stl in
    Pstr_type stl
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN
    let stl = List.map (fun (s, t) -> t) stl in Pstr_type stl
  ELSE
    let stl = List.map (fun (s, t) -> t) stl in
    Pstr_type (if is_nonrec then Nonrecursive else Recursive) stl
  END
;

value ocaml_class_infos =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSIFDEF OCAML_VERSION <= OCAML_3_00 THEN
    Some
      (fun virt params name expr loc variance ->
         {pci_virt = virt; pci_params = params; pci_name = name;
          pci_expr = expr; pci_loc = loc})
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some
      (fun virt (sl, sloc) name expr loc variance ->
        let params = (List.map (fun s → mkloc loc s) sl, sloc) in
        {pci_virt = virt; pci_params = params; pci_name = mkloc loc name;
         pci_expr = expr; pci_loc = loc; pci_variance = variance})
  ELSE
    Some
      (fun virt (sl, sloc) name expr loc variance ->
         let _ =
           if List.length sl <> List.length variance then
             failwith "internal error: ocaml_class_infos"
           else ()
         in
         let params =
           List.map2
            (fun os va ->
               (ocaml_mktyp loc (Ptyp_var os), variance_of_bool_bool va))
            sl variance
         in
         {pci_virt = virt; pci_params = params; pci_name = mkloc loc name;
          pci_expr = expr; pci_loc = loc; pci_attributes = []})
  END
;

value ocaml_pmod_constraint loc me mt =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN me
  ELSE ocaml_mkmod loc (Pmod_constraint me mt) END
;

value ocaml_pmod_ident li = Pmod_ident (mknoloc li);

value ocaml_pmod_functor s mt me =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pmod_functor (mknoloc s) mt me
  ELSE Pmod_functor (mknoloc s) (Some mt) me END
;

value ocaml_pmod_unpack =
  IFDEF OCAML_VERSION < OCAML_3_12 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_3_13_0 THEN
    Some (Left (fun e pt -> Pmod_unpack e pt))
  ELSE
    (Some (Right (fun e -> Pmod_unpack e, fun pt -> Ptyp_package pt)) :
     option (choice ('a -> 'b -> 'c) 'd))
  END
;

value ocaml_pcf_cstr =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_00 THEN
    Some (fun (t1, t2, loc) -> Pcf_cstr (t1, t2, loc))
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun (t1, t2, loc) -> Pcf_constr (t1, t2))
  ELSE
    Some (fun (t1, t2, loc) -> Pcf_constraint (t1, t2))
  END
;

value ocaml_pcf_inher =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN
    fun _ (id, cl, el, loc) pb -> Pcf_inher (id, cl, el, pb, loc)
  ELSIFDEF OCAML_VERSION < OCAML_3_12 THEN
    fun loc ce pb -> Pcf_inher ce pb
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    fun loc ce pb -> Pcf_inher Fresh ce pb
  ELSIFDEF OCAML_VERSION < OCAML_4_05_0 THEN
    fun loc ce pb -> Pcf_inherit Fresh ce pb
  ELSE
    fun loc ce pb -> Pcf_inherit Fresh ce (option_map (mkloc loc) pb)
  END
;

value ocaml_pcf_init =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Some (fun e -> Pcf_init e)
  ELSE Some (fun e -> Pcf_initializer e) END
;

value ocaml_pcf_meth (s, pf, ovf, e, loc) =
  let pf = if pf then Private else Public in
  IFDEF OCAML_VERSION < OCAML_3_12 THEN Pcf_meth (s, pf, e, loc)
  ELSE
    let ovf = if ovf then Override else Fresh in
    IFDEF OCAML_VERSION < OCAML_4_00 THEN Pcf_meth (s, pf, ovf, e, loc)
    ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
      Pcf_meth (mkloc loc s, pf, ovf, e)
    ELSE
      Pcf_method (mkloc loc s, pf, Cfk_concrete ovf e)
    END
  END
;

value ocaml_pcf_val (s, mf, ovf, e, loc) =
  let mf = if mf then Mutable else Immutable in
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN Pcf_val (s, Public, mf, Some e, loc)
  ELSIFDEF OCAML_VERSION < OCAML_3_12 THEN Pcf_val (s, mf, e,  loc)
  ELSE
    let ovf = if ovf then Override else Fresh in
    IFDEF OCAML_VERSION < OCAML_4_00 THEN Pcf_val (s, mf, ovf, e, loc)
    ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
      Pcf_val (mkloc loc s, mf, ovf, e)
    ELSE
      Pcf_val (mkloc loc s, mf, Cfk_concrete ovf e)
    END
  END
;

value ocaml_pcf_valvirt =
  IFDEF OCAML_VERSION < OCAML_3_10_0 THEN None
  ELSE
    let ocaml_pcf (s, mf, t, loc) =
      let mf = if mf then Mutable else Immutable in
      IFDEF OCAML_VERSION < OCAML_4_00 THEN Pcf_valvirt (s, mf, t, loc)
      ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
        Pcf_valvirt (mkloc loc s, mf, t)
      ELSE Pcf_val (mkloc loc s, mf, Cfk_virtual t) END
    in
    Some ocaml_pcf
  END
;

value ocaml_pcf_virt (s, pf, t, loc) =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN Pcf_virt (s, pf, t, loc)
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pcf_virt (mkloc loc s, pf, t)
  ELSE Pcf_method (mkloc loc s, pf, Cfk_virtual t) END
;

value ocaml_pcl_apply =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSIFDEF OCAML_VERSION <= OCAML_2_04 THEN
    Some (fun ce lel -> Pcl_apply ce (List.map snd lel))
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN
    Some (fun ce lel -> Pcl_apply ce lel)
  ELSE
    Some
      (fun ce lel ->
         Pcl_apply ce (List.map (fun (l, e) -> (labelled l, e)) lel))
  END
;

value ocaml_pcl_constr =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun li ctl -> Pcl_constr (mknoloc li) ctl) END
;

value ocaml_pcl_constraint =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun ce ct -> Pcl_constraint ce ct) END
;

value ocaml_pcl_fun =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN
    None
  ELSIFDEF OCAML_VERSION <= OCAML_2_04 THEN
    Some (fun lab ceo p ce -> Pcl_fun p ce)
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN
    Some (fun lab ceo p ce -> Pcl_fun lab ceo p ce)
  ELSE
    Some (fun lab ceo p ce -> Pcl_fun (labelled lab) ceo p ce)
  END
;

value ocaml_pcl_let =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun rf pel ce -> Pcl_let rf pel ce) END
;

value ocaml_pcl_structure =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun cs -> Pcl_structure cs) END
;

value ocaml_pctf_cstr =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_00 THEN
    Some (fun (t1, t2, loc) -> Pctf_cstr (t1, t2, loc))
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun (t1, t2, loc) -> Pctf_cstr (t1, t2))
  ELSE
    Some (fun (t1, t2, loc) -> Pctf_constraint (t1, t2))
  END
;

value ocaml_pctf_inher ct =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pctf_inher ct
  ELSE Pctf_inherit ct END
;

value ocaml_pctf_meth (s, pf, t, loc) =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN Pctf_meth (s, pf, t, loc)
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pctf_meth (s, pf, t)
  ELSIFDEF OCAML_VERSION < OCAML_4_05_0 THEN Pctf_method (s, pf, Concrete, t)
  ELSE Pctf_method (mkloc loc s, pf, Concrete, t) END
;

value ocaml_pctf_val (s, mf, t, loc) =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN Pctf_val (s, Public, mf, Some t, loc)
  ELSIFDEF OCAML_VERSION < OCAML_3_10 THEN Pctf_val (s, mf, Some t, loc)
  ELSIFDEF OCAML_VERSION < OCAML_4_00 THEN Pctf_val (s, mf, Concrete, t, loc)
  ELSIFDEF OCAML_VERSION < OCAML_4_05_0 THEN Pctf_val (s, mf, Concrete, t)
  ELSE Pctf_val (mkloc loc s, mf, Concrete, t) END
;

value ocaml_pctf_virt (s, pf, t, loc) =
  IFDEF OCAML_VERSION < OCAML_4_00 THEN Pctf_virt (s, pf, t, loc)
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pctf_virt (s, pf, t)
  ELSIFDEF OCAML_VERSION < OCAML_4_05_0 THEN Pctf_method (s, pf, Virtual, t)
  ELSE Pctf_method (mkloc loc s, pf, Virtual, t) END
;

value ocaml_pcty_constr =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSE Some (fun li ltl -> Pcty_constr (mknoloc li) ltl) END
;

value ocaml_pcty_fun =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN
    None
  ELSIFDEF OCAML_VERSION <= OCAML_2_04 THEN
    Some (fun lab t ot ct -> Pcty_fun ot ct)
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun lab t ot ct -> Pcty_fun lab ot ct)
  ELSIFDEF OCAML_VERSION < OCAML_4_03_0 THEN
    Some (fun lab t ot ct -> Pcty_arrow lab (mkopt t lab) ct)
  ELSE
    Some (fun lab t ot ct -> Pcty_arrow (labelled lab) t ct)
  END
;

value ocaml_pcty_signature =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_00 THEN
    Some (fun (t, cil) -> Pcty_signature (t, cil))
  ELSE
    let f (t, ctfl) =
      let cs =
        IFDEF OCAML_VERSION < OCAML_4_02_0 THEN
          {pcsig_self = t; pcsig_fields = ctfl; pcsig_loc = t.ptyp_loc}
        ELSE
          {pcsig_self = t; pcsig_fields = ctfl}
        END
      in
      Pcty_signature cs
    in
    Some f
  END
;

value ocaml_pdir_bool =
  IFDEF OCAML_VERSION <= OCAML_2_04 THEN None
  ELSE Some (fun b -> Pdir_bool b) END
;
value ocaml_pdir_int i s =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN Pdir_int s
  ELSE Pdir_int i None END
;
value ocaml_pdir_some x =
  IFDEF OCAML_VERSION < OCAML_4_08_0 THEN x ELSE Some x END
;
value ocaml_pdir_none =
  IFDEF OCAML_VERSION < OCAML_4_08_0 THEN Pdir_none ELSE None END
;
value ocaml_ptop_dir loc s da =
  IFDEF OCAML_VERSION < OCAML_4_08_0 THEN Ptop_dir s da
  ELSE
    Ptop_dir
      {pdir_name = mkloc loc s;
       pdir_arg =
         match da with
         | Some da -> Some {pdira_desc = da; pdira_loc = loc}
         | None -> None
         end;
       pdir_loc = loc}
  END
;

value ocaml_pwith_modsubst =
  IFDEF OCAML_VERSION < OCAML_3_12_0 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_02_0 THEN
    Some (fun loc me -> Pwith_modsubst (mkloc loc me))
  ELSIFDEF OCAML_VERSION < OCAML_4_06_0 THEN
    Some (fun loc me -> Pwith_modsubst (mkloc loc "") (mkloc loc me))
  ELSE
    Some (fun loc me -> Pwith_modsubst (mkloc loc (Lident "")) (mkloc loc me))
  END
;

value ocaml_pwith_type loc (i, td) =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pwith_type td
  ELSE Pwith_type (mkloc loc i) td END
;

value ocaml_pwith_module loc mname me =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Pwith_module (mkloc loc me)
  ELSE Pwith_module (mkloc loc mname) (mkloc loc me) END
;

value ocaml_pwith_typesubst =
  IFDEF OCAML_VERSION < OCAML_3_12_0 THEN None
  ELSIFDEF OCAML_VERSION < OCAML_4_06_0 THEN
    Some (fun loc td -> Pwith_typesubst td)
  ELSE
    Some (fun loc td -> Pwith_typesubst (mkloc loc (Lident "")) td)
 END
;

value module_prefix_can_be_in_first_record_label_only =
  IFDEF OCAML_VERSION <= OCAML_3_07 THEN False ELSE True END
;

value split_or_patterns_with_bindings =
  IFDEF OCAML_VERSION <= OCAML_3_01 THEN True ELSE False END
;

value has_records_with_with =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN False ELSE True END
;

IFDEF JOCAML THEN
  value joinclause (loc, jc) =
    let jc =
      List.map
        (fun (loc, (jpl, e)) ->
           let jpl =
             List.map
               (fun (locp, (loci, s), p) ->
                  let ji = {pjident_desc = s; pjident_loc = loci} in
                  {pjpat_desc = (ji, p); pjpat_loc = locp})
               jpl
           in
           {pjclause_desc = (jpl, e); pjclause_loc = loc})
        jc
    in
    {pjauto_desc = jc; pjauto_loc = loc}
  ;
END;

value jocaml_pstr_def =
  IFDEF JOCAML THEN Some (fun jcl -> Pstr_def (List.map joinclause jcl))
  ELSE (None : option (_ -> _)) END
;

value jocaml_pexp_def =
  IFDEF JOCAML THEN Some (fun jcl e -> Pexp_def (List.map joinclause jcl) e)
  ELSE (None : option (_ -> _ -> _)) END
;

value jocaml_pexp_par =
  IFDEF JOCAML THEN Some (fun e1 e2 -> Pexp_par e1 e2)
  ELSE (None : option (_ -> _ -> _)) END
;

value jocaml_pexp_reply =
  IFDEF JOCAML THEN
    let pexp_reply loc e (sloc, s) =
      let ji = {pjident_desc = s; pjident_loc = sloc} in
      Pexp_reply e ji
    in
    Some pexp_reply
  ELSE (None : option (_ -> _ -> _ -> _)) END
;

value jocaml_pexp_spawn =
  IFDEF JOCAML THEN Some (fun e -> Pexp_spawn e)
  ELSE (None : option (_ -> _)) END
;

value arg_rest =
  fun
  [ IFDEF OCAML_VERSION >= OCAML_2_00 THEN Arg.Rest r -> Some r END
  | _ -> None ]
;

value arg_set_string =
  fun
  [ IFDEF OCAML_VERSION >= OCAML_3_07 THEN Arg.Set_string r -> Some r END
  | _ -> None ]
;

value arg_set_int =
  fun
  [ IFDEF OCAML_VERSION >= OCAML_3_07 THEN Arg.Set_int r -> Some r END
  | _ -> None ]
;

value arg_set_float =
  fun
  [ IFDEF OCAML_VERSION >= OCAML_3_07 THEN Arg.Set_float r -> Some r END
  | _ -> None ]
;

value arg_symbol =
  fun
  [ IFDEF OCAML_VERSION >= OCAML_3_07 THEN Arg.Symbol s f -> Some (s, f) END
  | _ -> None ]
;

value arg_tuple =
  fun
  [ IFDEF OCAML_VERSION >= OCAML_3_07 THEN Arg.Tuple t -> Some t END
  | _ -> None ]
;

value arg_bool =
  fun
  [ IFDEF OCAML_VERSION >= OCAML_3_07 THEN Arg.Bool f -> Some f END
  | _ -> None ]
;

value char_escaped =
  IFDEF OCAML_VERSION >= OCAML_3_11 THEN Char.escaped
  ELSE
    fun
    [ '\r' -> "\\r"
    | c -> Char.escaped c ]
  END
;

value hashtbl_mem =
  IFDEF OCAML_VERSION <= OCAML_2_01 THEN
    fun ht a ->
      try let _ = Hashtbl.find ht a in True with [ Not_found -> False ]
  ELSE
    Hashtbl.mem
  END
;

IFDEF OCAML_VERSION <= OCAML_1_07 THEN
  value rec list_rev_append l1 l2 =
    match l1 with
    [ [x :: l] -> list_rev_append l [x :: l2]
    | [] -> l2 ]
  ;
ELSE
  value list_rev_append = List.rev_append;
END;

value list_rev_map =
  IFDEF OCAML_VERSION <= OCAML_2_02 THEN
    fun f ->
      loop [] where rec loop r =
        fun
        [ [x :: l] -> loop [f x :: r] l
        | [] -> r ]
  ELSE
    List.rev_map
  END
;

value list_sort =
  IFDEF OCAML_VERSION <= OCAML_2_99 THEN
    fun f l -> Sort.list (fun x y -> f x y <= 0) l
  ELSE List.sort END
;

value pervasives_set_binary_mode_out =
  IFDEF OCAML_VERSION <= OCAML_1_07 THEN fun _ _ -> ()
  ELSE set_binary_mode_out END
;

IFDEF OCAML_VERSION <= OCAML_3_04 THEN
  declare
    value scan_format fmt i kont =
      match fmt.[i+1] with
      [ 'c' -> Obj.magic (fun (c : char) -> kont (String.make 1 c) (i + 2))
      | 'd' -> Obj.magic (fun (d : int) -> kont (string_of_int d) (i + 2))
      | 's' -> Obj.magic (fun (s : string) -> kont s (i + 2))
      | c ->
          failwith
            (Printf.sprintf "Pretty.sprintf \"%s\" '%%%c' not impl" fmt c) ]
    ;
    value printf_ksprintf kont fmt =
      let fmt = (Obj.magic fmt : string) in
      let len = String.length fmt in
      doprn [] 0 where rec doprn rev_sl i =
        if i >= len then do {
          let s = String.concat "" (List.rev rev_sl) in
          Obj.magic (kont s)
        }
        else do {
          match fmt.[i] with
          [ '%' -> scan_format fmt i (fun s -> doprn [s :: rev_sl])
          | c -> doprn [String.make 1 c :: rev_sl] (i + 1)  ]
        }
    ;
  end;
ELSIFDEF OCAML_VERSION <= OCAML_3_08_4 THEN
  value printf_ksprintf = Printf.kprintf;
ELSE
  value printf_ksprintf = Printf.ksprintf;
END;

value char_uppercase =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN Char.uppercase
  ELSE Char.uppercase_ascii END
;

value bytes_modname =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN "String"
  ELSE "Bytes" END
;

value bytes_of_string s =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN s
  ELSE Bytes.of_string s END
;

value bytes_to_string s =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN s
  ELSE Bytes.to_string s END
;

value string_capitalize =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN String.capitalize
  ELSE String.capitalize_ascii END
;

value string_contains =
  IFDEF OCAML_VERSION <= OCAML_2_00 THEN
    fun s c ->
      loop 0 where rec loop i =
        if i = String.length s then False
        else if s.[i] = c then True
        else loop (i + 1)
  ELSIFDEF OCAML_2_01 THEN
    fun s c -> s <> "" && String.contains s c
  ELSE
    String.contains
  END
;

value string_cat s1 s2 =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN s1 ^ s2
  ELSE Bytes.cat s1 s2 END
;

value string_copy =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN String.copy
  ELSE Bytes.copy END
;

value string_create =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN String.create
  ELSE Bytes.create END
;

value string_get =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN String.get
  ELSE Bytes.get END
;

value string_index =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN String.index
  ELSE Bytes.index END
;

value string_length =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN String.length
  ELSE Bytes.length END
;

value string_lowercase =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN String.lowercase
  ELSE String.lowercase_ascii END
;

value string_unsafe_set =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN String.unsafe_set
  ELSE Bytes.unsafe_set END
;

value string_uncapitalize =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN String.uncapitalize
  ELSE String.uncapitalize_ascii END
;

value string_uppercase =
  IFDEF OCAML_VERSION < OCAML_4_03_0 THEN String.uppercase
  ELSE String.uppercase_ascii END
;

value string_set =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN String.set
  ELSE Bytes.set END
;

value string_sub =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN String.sub
  ELSE Bytes.sub END
;

value array_create =
  IFDEF OCAML_VERSION < OCAML_4_02_0 THEN Array.create
  ELSE Array.make END
;
