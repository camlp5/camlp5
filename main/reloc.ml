(* camlp5r *)
(* reloc.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";

open MLast;

value option_map f =
  fun
  [ Some x -> Some (f x)
  | None -> None ]
;

value vala_map f =
  IFNDEF STRICT THEN
    fun x -> f x
  ELSE
    fun
    [ Ploc.VaAnt s -> Ploc.VaAnt s
    | Ploc.VaVal x -> Ploc.VaVal (f x) ]
  END
;

value class_infos_map floc sh ~{attributes} f x =
  {ciLoc = floc x.ciLoc; ciVir = x.ciVir;
   ciPrm =
     let (x1, x2) = x.ciPrm in
     (floc x1, x2);
   ciNam = x.ciNam; ciExp = f x.ciExp; ciAttributes = attributes floc sh x.ciAttributes }
;

value anti_loc qloc sh loc loc1 =
  (*
    ...<:expr<.....$lid:...xxxxxxxx...$...>>...
    |..|-----------------------------------|    qloc
       <----->                                  sh
              |.........|------------|          loc
                        |..|------|             loc1
  *)
  let sh1 = Ploc.first_pos qloc + sh in
  let sh2 = sh1 + Ploc.first_pos loc in
  let line_nb_qloc = Ploc.line_nb qloc in
  let line_nb_loc = Ploc.line_nb loc in
  let line_nb_loc1 = Ploc.line_nb loc1 in
  if line_nb_qloc < 0 || line_nb_loc < 0 || line_nb_loc1 < 0 then
    Ploc.make_unlined
      (sh2 + Ploc.first_pos loc1, sh2 + Ploc.last_pos loc1)
  else
    Ploc.make_loc (Ploc.file_name loc)
      (line_nb_qloc + line_nb_loc + line_nb_loc1 - 2)
      (if line_nb_loc1 = 1 then
         if line_nb_loc = 1 then Ploc.bol_pos qloc
         else sh1 + Ploc.bol_pos loc
       else sh2 + Ploc.bol_pos loc1)
      (sh2 + Ploc.first_pos loc1, sh2 + Ploc.last_pos loc1) ""
;

value rec ctyp floc sh =
  self where rec self =
    fun
    [ TyAtt loc ct attr ->
       let loc = floc loc in
       TyAtt loc (self ct) (attribute_body floc sh attr)
    | TyAcc loc x1 x2 ->
        let loc = floc loc in
        TyAcc loc (longid floc sh x1) x2
    | TyAli loc x1 x2 →
        let loc = floc loc in
        TyAli loc (self x1) (self x2)
    | TyAny loc →
        let loc = floc loc in
        TyAny loc
    | TyApp loc x1 x2 →
        let loc = floc loc in
        TyApp loc (self x1) (self x2)
    | TyArr loc x1 x2 →
        let loc = floc loc in
        TyArr loc (self x1) (self x2)
    | TyCls loc x1 →
        let loc = floc loc in
        TyCls loc (vala_map (longid_lident floc sh) x1)
    | TyLab loc x1 x2 →
        let loc = floc loc in
        TyLab loc x1 (self x2)
    | TyLid loc x1 →
        let loc = floc loc in
        TyLid loc x1
    | TyMan loc x1 x2 x3 →
        let loc = floc loc in
        TyMan loc (self x1) x2 (self x3)
    | TyObj loc x1 x2 →
        let loc = floc loc in
        TyObj loc (vala_map (List.map (fun (x1, x2, x3) → (x1, self x2, attributes floc sh x3))) x1) x2
    | TyOlb loc x1 x2 →
        let loc = floc loc in
        TyOlb loc x1 (self x2)
    | TyOpn loc ->
       let loc = floc loc in
       TyOpn loc
    | TyPck loc x1 →
        let loc = floc loc in
        TyPck loc (module_type floc sh x1)
    | TyPol loc x1 x2 →
        let loc = floc loc in
        TyPol loc x1 (self x2)
    | TyPot loc x1 x2 →
        let loc = floc loc in
        TyPot loc x1 (self x2)
    | TyQuo loc x1 →
        let loc = floc loc in
        TyQuo loc x1
    | TyRec loc x1 →
        let loc = floc loc in
        TyRec loc
          (vala_map
             (List.map (fun (loc, x1, x2, x3, x4) → (floc loc, x1, x2, self x3, attributes floc sh x4)))
             x1)
    | TySum loc x1 →
        let loc = floc loc in
        TySum loc
          (vala_map
             (List.map
                (generic_constructor floc sh))
             x1)
    | TyTup loc x1 →
        let loc = floc loc in
        TyTup loc (vala_map (List.map self) x1)
      | TyVrn loc x1 x2 →
        let loc = floc loc in
        TyVrn loc (vala_map (List.map (poly_variant floc sh)) x1) x2
    | TyXtr loc x1 x2 →
        let loc = floc loc in
        TyXtr loc x1 (option_map (vala_map self) x2)
    | TyExten loc exten ->
        let loc = floc loc in
        TyExten loc (attribute_body floc sh exten)
    ]
and generic_constructor floc sh = fun (loc, x1, x2, x3, x4, x5) ->
    (floc loc, x1, x2, vala_map (List.map (ctyp floc sh)) x3,
     vala_map (option_map (ctyp floc sh)) x4, attributes floc sh x5)
and poly_variant floc sh =
  fun
  [ PvTag loc x1 x2 x3 x4 →
      let loc = floc loc in
      PvTag loc x1 x2 (vala_map (List.map (ctyp floc sh)) x3) (attributes floc sh x4)
  | PvInh loc x1 →
      let loc = floc loc in
      PvInh loc (ctyp floc sh x1) ]
and patt floc sh =
  self where rec self =
    fun
    [ PaAtt loc p attr ->
       let loc = floc loc in
       PaAtt loc (self p) (attribute_body floc sh attr)
    | PaPfx loc li p ->
       let loc = floc loc in
       PaPfx loc (longid floc sh li) (self p)
    | PaLong loc li loc_ids ->
       let loc = floc loc in
       PaLong loc (longid floc sh li) (vala_map (List.map (fun (loc, id) -> (floc loc, id))) loc_ids)
    | PaAli loc x1 x2 →
        let loc = floc loc in
        PaAli loc (self x1) (self x2)
    | PaAnt loc x1 →
        let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
        patt new_floc sh x1
    | PaAny loc →
        let loc = floc loc in
        PaAny loc
    | PaApp loc x1 x2 →
        let loc = floc loc in
        PaApp loc (self x1) (self x2)
    | PaArr loc x1 →
        let loc = floc loc in
        PaArr loc (vala_map (List.map self) x1)
    | PaChr loc x1 →
        let loc = floc loc in
        PaChr loc x1
    | PaExc loc x1 →
        let loc = floc loc in
        PaExc loc (self x1)
    | PaFlo loc x1 →
        let loc = floc loc in
        PaFlo loc x1
    | PaInt loc x1 x2 →
        let loc = floc loc in
        PaInt loc x1 x2
    | PaLab loc x1 →
        let loc = floc loc in
        PaLab loc
          (vala_map
             (List.map
                (fun (x1, x2) → (self x1, vala_map (option_map self) x2)))
             x1)
    | PaLaz loc x1 →
        let loc = floc loc in
        PaLaz loc (self x1)
    | PaLid loc x1 →
        let loc = floc loc in
        PaLid loc x1
    | PaNty loc x1 →
        let loc = floc loc in
        PaNty loc x1
    | PaOlb loc x1 x2 →
        let loc = floc loc in
        PaOlb loc (self x1) (vala_map (option_map (expr floc sh)) x2)
    | PaOrp loc x1 x2 →
        let loc = floc loc in
        PaOrp loc (self x1) (self x2)
    | PaRec loc x1 →
        let loc = floc loc in
        PaRec loc (vala_map (List.map (fun (x1, x2) → (self x1, self x2))) x1)
    | PaRng loc x1 x2 →
        let loc = floc loc in
        PaRng loc (self x1) (self x2)
    | PaStr loc x1 →
        let loc = floc loc in
        PaStr loc x1
    | PaTup loc x1 →
        let loc = floc loc in
        PaTup loc (vala_map (List.map self) x1)
    | PaTyc loc x1 x2 →
        let loc = floc loc in
        PaTyc loc (self x1) (ctyp floc sh x2)
    | PaTyp loc x1 →
        let loc = floc loc in
        PaTyp loc (vala_map (longid_lident floc sh) x1)
    | PaUnp loc x1 x2 →
        let loc = floc loc in
        PaUnp loc x1 (option_map (module_type floc sh) x2)
    | PaVrn loc x1 →
        let loc = floc loc in
        PaVrn loc x1
    | PaXtr loc x1 x2 →
        let loc = floc loc in
        PaXtr loc x1 (option_map (vala_map self) x2)
    | PaExten loc exten ->
        let loc = floc loc in
        PaExten loc (attribute_body floc sh exten)
    ]
and expr floc sh =
  self where rec self =
    fun
    [ ExAtt loc e attr ->
        let loc = floc loc in
       ExAtt loc (self e) (attribute_body floc sh attr)

    | ExLong loc x1 ->
      let loc = floc loc in
      ExLong loc (longid floc sh x1)

    | ExOpen loc x1 x2 ->
      let loc = floc loc in
      ExOpen loc (longid floc sh x1) (self x2)

    | ExFle loc x1 x2 ->
      let loc = floc loc in
      ExFle loc (self x1) (vala_map (longid_lident floc sh) x2)

    | ExAnt loc x1 →
        let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
        expr new_floc sh x1
    | ExApp loc x1 x2 →
        let loc = floc loc in
        ExApp loc (self x1) (self x2)
    | ExAre loc x1 x2 x3 →
        let loc = floc loc in
        ExAre loc x1 (self x2) (vala_map (List.map self) x3)
    | ExArr loc x1 →
        let loc = floc loc in
        ExArr loc (vala_map (List.map self) x1)
    | ExAsr loc x1 →
        let loc = floc loc in
        ExAsr loc (self x1)
    | ExAss loc x1 x2 →
        let loc = floc loc in
        ExAss loc (self x1) (self x2)
    | ExBae loc x1 x2 x3 →
        let loc = floc loc in
        ExBae loc x1 (self x2) (vala_map (List.map self) x3)
    | ExChr loc x1 →
        let loc = floc loc in
        ExChr loc x1
    | ExCoe loc x1 x2 x3 →
        let loc = floc loc in
        ExCoe loc (self x1) (option_map (ctyp floc sh) x2) (ctyp floc sh x3)
    | ExFlo loc x1 →
        let loc = floc loc in
        ExFlo loc x1
    | ExFor loc x1 x2 x3 x4 x5 →
        let loc = floc loc in
        ExFor loc (patt floc sh x1) (self x2) (self x3) x4 (vala_map (List.map self) x5)
    | ExFun loc x1 →
        let loc = floc loc in
        ExFun loc
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt floc sh x1, vala_map (option_map self) x2, self x3)))
             x1)
    | ExIfe loc x1 x2 x3 →
        let loc = floc loc in
        ExIfe loc (self x1) (self x2) (self x3)
    | ExInt loc x1 x2 →
        let loc = floc loc in
        ExInt loc x1 x2
    | ExLab loc x1 →
        let loc = floc loc in
        ExLab loc
          (vala_map
             (List.map
                (fun (x1, x2) →
                   (patt floc sh x1, vala_map (option_map self) x2)))
             x1)
    | ExLaz loc x1 →
        let loc = floc loc in
        ExLaz loc (self x1)
    | ExLet loc x1 x2 x3 →
        let loc = floc loc in
        ExLet loc x1
          (vala_map (List.map (fun (x1, x2, x3) → (patt floc sh x1, self x2, attributes floc sh x3))) x2)
          (self x3)
    | ExLEx loc x1 x2 x3 x4 ->
        let loc = floc loc in
        ExLEx loc x1 (vala_map (List.map (ctyp floc sh)) x2) (self x3) (attributes floc sh x4)
    | ExLid loc x1 →
        let loc = floc loc in
        ExLid loc x1
    | ExLmd loc x1 x2 x3 →
        let loc = floc loc in
        ExLmd loc x1 (module_expr floc sh x2) (self x3)
    | ExLop loc b x1 x2 →
        let loc = floc loc in
        ExLop loc b (module_expr floc sh x1) (self x2)
    | ExMat loc x1 x2 →
        let loc = floc loc in
        ExMat loc (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt floc sh x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExNew loc x1 →
        let loc = floc loc in
        ExNew loc (vala_map (longid_lident floc sh) x1)
    | ExObj loc x1 x2 →
        let loc = floc loc in
        ExObj loc (vala_map (option_map (patt floc sh)) x1)
          (vala_map (List.map (class_str_item floc sh)) x2)
    | ExOlb loc x1 x2 →
        let loc = floc loc in
        ExOlb loc (patt floc sh x1) (vala_map (option_map self) x2)
    | ExOvr loc x1 →
        let loc = floc loc in
        ExOvr loc (vala_map (List.map (fun (x1, x2) → (x1, self x2))) x1)
    | ExPck loc x1 x2 →
        let loc = floc loc in
        ExPck loc (module_expr floc sh x1)
          (option_map (module_type floc sh) x2)
    | ExRec loc x1 x2 →
        let loc = floc loc in
        ExRec loc
          (vala_map (List.map (fun (x1, x2) → (patt floc sh x1, self x2))) x1)
          (option_map self x2)
    | ExSeq loc x1 →
        let loc = floc loc in
        ExSeq loc (vala_map (List.map self) x1)
    | ExSnd loc x1 x2 →
        let loc = floc loc in
        ExSnd loc (self x1) x2
    | ExSte loc x1 x2 x3 →
        let loc = floc loc in
        ExSte loc x1 (self x2) (vala_map (List.map self) x3)
    | ExStr loc x1 →
        let loc = floc loc in
        ExStr loc x1
    | ExTry loc x1 x2 →
        let loc = floc loc in
        ExTry loc (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt floc sh x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExTup loc x1 →
        let loc = floc loc in
        ExTup loc (vala_map (List.map self) x1)
    | ExTyc loc x1 x2 →
        let loc = floc loc in
        ExTyc loc (self x1) (ctyp floc sh x2)
    | ExVrn loc x1 →
        let loc = floc loc in
        ExVrn loc x1
    | ExWhi loc x1 x2 →
        let loc = floc loc in
        ExWhi loc (self x1) (vala_map (List.map self) x2)
    | ExXtr loc x1 x2 →
        let loc = floc loc in
        ExXtr loc x1 (option_map (vala_map self) x2)
    | ExExten loc exten ->
        let loc = floc loc in
        ExExten loc (attribute_body floc sh exten)
    | ExUnr loc ->
        let loc = floc loc in
        ExUnr loc
    ]
and module_type floc sh =
  self where rec self =
    fun
    [ MtAtt loc e attr ->
        let loc = floc loc in
       MtAtt loc (self e) (attribute_body floc sh attr)
    | MtLong loc x1 →
        let loc = floc loc in
        MtLong loc (longid floc sh x1)
    | MtLongLid loc x1 x2 →
        let loc = floc loc in
        MtLongLid loc (longid floc sh x1) x2
    | MtFun loc arg x3 →
        let loc = floc loc in
        MtFun loc (vala_map (functor_parameter floc sh) arg) (self x3)
    | MtLid loc x1 →
        let loc = floc loc in
        MtLid loc x1
    | MtQuo loc x1 →
        let loc = floc loc in
        MtQuo loc x1
    | MtSig loc x1 →
        let loc = floc loc in
        MtSig loc (vala_map (List.map (sig_item floc sh)) x1)
    | MtTyo loc x1 →
        let loc = floc loc in
        MtTyo loc (module_expr floc sh x1)
    | MtWit loc x1 x2 →
        let loc = floc loc in
        MtWit loc (self x1) (vala_map (List.map (with_constr floc sh)) x2)
    | MtXtr loc x1 x2 →
        let loc = floc loc in
        MtXtr loc x1 (option_map (vala_map self) x2)
    | MtExten loc exten ->
        let loc = floc loc in
        MtExten loc (attribute_body floc sh exten)
    ]
and functor_parameter floc sh =
  option_map (fun (idopt, m) -> (idopt, module_type floc sh m))

and sig_item floc sh =
  self where rec self =
    fun
    [ SgCls loc x1 →
        let loc = floc loc in
        SgCls loc
          (vala_map (List.map (class_infos_map floc sh ~{attributes=attributes}  (class_type floc sh))) x1)
    | SgClt loc x1 →
        let loc = floc loc in
        SgClt loc
          (vala_map (List.map (class_infos_map floc sh ~{attributes=attributes} (class_type floc sh))) x1)
    | SgDcl loc x1 →
        let loc = floc loc in
        SgDcl loc (vala_map (List.map self) x1)
    | SgDir loc x1 x2 →
        let loc = floc loc in
        SgDir loc x1 (vala_map (option_map (expr floc sh)) x2)
    | SgExc loc x1 x2 →
        let loc = floc loc in
        SgExc loc (generic_constructor floc sh x1) (attributes floc sh x2)
    | SgExt loc x1 x2 x3 x4 x5 →
        let loc = floc loc in
        SgExt loc x1 x2 (ctyp floc sh x3) x4 (attributes floc sh x5)
    | SgInc loc x1 x2 →
        let loc = floc loc in
        SgInc loc (module_type floc sh x1) (attributes floc sh x2)
    | SgMod loc x1 x2 →
        let loc = floc loc in
        SgMod loc x1
          (vala_map (List.map (fun (x1, x2, x3) → (x1, module_type floc sh x2, attributes floc sh x3)))
             x2)
    | SgMty loc x1 x2 x3 →
        let loc = floc loc in
        SgMty loc x1 (module_type floc sh x2) (attributes floc sh x3)
    | SgMtySubst loc x1 x2 x3 →
        let loc = floc loc in
        SgMtySubst loc x1 (module_type floc sh x2) (attributes floc sh x3)
    | SgMtyAlias loc x1 x2 x3 →
        let loc = floc loc in
        SgMtyAlias loc x1 (vala_map (longid floc sh) x2) (attributes floc sh x3)
    | SgModSubst loc x1 x2 x3 →
        let loc = floc loc in
        SgModSubst loc x1 (longid floc sh x2) (attributes floc sh x3)
    | SgOpn loc x1 x2 →
        let loc = floc loc in
        SgOpn loc (longid floc sh x1) (attributes floc sh x2)
    | SgTyp loc x1 x2 →
        let loc = floc loc in
        SgTyp loc x1 (vala_map (List.map (type_decl floc sh)) x2)
    | SgTypExten loc x1 →
        let loc = floc loc in
        SgTypExten loc (type_extension floc sh x1)
    | SgUse loc x1 x2 →
        let loc = floc loc in
        SgUse loc x1
          (vala_map (List.map (fun (x1, loc) → (self x1, floc loc))) x2)
    | SgVal loc x1 x2 x3 →
        let loc = floc loc in
        SgVal loc x1 (ctyp floc sh x2) (attributes floc sh x3)
    | SgXtr loc x1 x2 →
        let loc = floc loc in
        SgXtr loc x1 (option_map (vala_map self) x2)
    | SgFlAtt loc a ->
        let loc = floc loc in
        SgFlAtt loc (attribute_body floc sh a)
    | SgExten loc exten attrs ->
        let loc = floc loc in
        SgExten loc (attribute_body floc sh exten) (attributes floc sh attrs)
    ]
and with_constr floc sh =
  fun
  [ WcMod loc x1 x2 →
      let loc = floc loc in
      WcMod loc (vala_map (longid floc sh) x1) (module_expr floc sh x2)
  | WcMos loc x1 x2 →
      let loc = floc loc in
      WcMos loc (vala_map (longid floc sh) x1) (module_expr floc sh x2)
  | WcMty loc x1 x2 →
      let loc = floc loc in
      WcMty loc (vala_map (longid floc sh) x1) (module_type floc sh x2)
  | WcMts loc x1 x2 →
      let loc = floc loc in
      WcMts loc (vala_map (longid floc sh) x1) (module_type floc sh x2)
  | WcTyp loc x1 x2 x3 x4 →
      let loc = floc loc in
      WcTyp loc (vala_map (longid_lident floc sh) x1) x2 x3 (ctyp floc sh x4)
  | WcTys loc x1 x2 x3 →
      let loc = floc loc in
      WcTys loc (vala_map (longid_lident floc sh) x1) x2 (ctyp floc sh x3) ]
and longid floc sh =
  self where rec self =
    fun
    [ LiAcc loc x1 x2 →
        let loc = floc loc in
        LiAcc loc (self x1) x2
    | LiApp loc x1 x2 →
        let loc = floc loc in
        LiApp loc (self x1) (self x2)
    | LiUid loc x1 →
        let loc = floc loc in
        LiUid loc x1
    | LiXtr loc x1 x2 →
        let loc = floc loc in
        LiXtr loc x1 (option_map (vala_map self) x2)
    ]
and module_expr floc sh =
  self where rec self =
    fun
    [ MeAtt loc e attr ->
        let loc = floc loc in
       MeAtt loc (self e) (attribute_body floc sh attr)
    | MeAcc loc x1 x2 →
        let loc = floc loc in
        MeAcc loc (self x1) (self x2)
    | MeApp loc x1 x2 →
        let loc = floc loc in
        MeApp loc (self x1) (self x2)
    | MeFun loc arg x3 →
        let loc = floc loc in
        MeFun loc (vala_map (functor_parameter floc sh) arg) (self x3)
    | MeStr loc x1 →
        let loc = floc loc in
        MeStr loc (vala_map (List.map (str_item floc sh)) x1)
    | MeTyc loc x1 x2 →
        let loc = floc loc in
        MeTyc loc (self x1) (module_type floc sh x2)
    | MeUid loc x1 →
        let loc = floc loc in
        MeUid loc x1
    | MeUnp loc x1 x2 x3 →
        let loc = floc loc in
        MeUnp loc (expr floc sh x1) (option_map (module_type floc sh) x2) (option_map (module_type floc sh) x3)
    | MeXtr loc x1 x2 →
        let loc = floc loc in
        MeXtr loc x1 (option_map (vala_map self) x2)
    | MeExten loc exten ->
        let loc = floc loc in
        MeExten loc (attribute_body floc sh exten)
    ]
and str_item floc sh =
  self where rec self =
    fun
    [ StCls loc x1 →
        let loc = floc loc in
        StCls loc
          (vala_map (List.map (class_infos_map floc sh ~{attributes=attributes} (class_expr floc sh))) x1)
    | StClt loc x1 →
        let loc = floc loc in
        StClt loc
          (vala_map (List.map (class_infos_map floc sh ~{attributes=attributes} (class_type floc sh))) x1)
    | StDcl loc x1 →
        let loc = floc loc in
        StDcl loc (vala_map (List.map self) x1)
    | StDir loc x1 x2 →
        let loc = floc loc in
        StDir loc x1 (vala_map (option_map (expr floc sh)) x2)
    | StExc loc x1 x2 →
        let loc = floc loc in
        StExc loc (vala_map (extension_constructor floc sh) x1) (attributes floc sh x2)
    | StExp loc x1 x2 →
        let loc = floc loc in
        StExp loc (expr floc sh x1) (attributes floc sh x2)
    | StExt loc x1 x2 x3 x4 x5 →
        let loc = floc loc in
        StExt loc x1 x2 (ctyp floc sh x3) x4 (attributes floc sh x5)
    | StInc loc x1 x2 →
        let loc = floc loc in
        StInc loc (module_expr floc sh x1) (attributes floc sh x2)
    | StMod loc x1 x2 →
        let loc = floc loc in
        StMod loc x1
          (vala_map (List.map (fun (x1, x2, x3) → (x1, module_expr floc sh x2, attributes floc sh x3)))
             x2)
    | StMty loc x1 x2 x3 →
        let loc = floc loc in
        StMty loc x1 (module_type floc sh x2) (attributes floc sh x3)
    | StOpn loc x1 x2 x3 →
        let loc = floc loc in
        StOpn loc x1 (module_expr floc sh x2) (attributes floc sh x3)
    | StTyp loc x1 x2 →
        let loc = floc loc in
        StTyp loc x1 (vala_map (List.map (type_decl floc sh)) x2)
    | StTypExten loc x1 →
        let loc = floc loc in
        StTypExten loc (type_extension floc sh x1)
    | StUse loc x1 x2 →
        let loc = floc loc in
        StUse loc x1
          (vala_map (List.map (fun (x1, loc) → (self x1, floc loc))) x2)
    | StVal loc x1 x2 →
        let loc = floc loc in
        StVal loc x1
          (vala_map
             (List.map (fun (x1, x2, x3) → (patt floc sh x1, expr floc sh x2, attributes floc sh x3)))
             x2)
    | StXtr loc x1 x2 →
        let loc = floc loc in
        StXtr loc x1 (option_map (vala_map self) x2)
    | StFlAtt loc a ->
        let loc = floc loc in
        StFlAtt loc (attribute_body floc sh a)
    | StExten loc exten attrs ->
        let loc = floc loc in
        StExten loc (attribute_body floc sh exten) (attributes floc sh attrs)
    ]
and type_decl floc sh x =
  {tdIsDecl = x.tdIsDecl ;
   tdNam = vala_map (fun (loc, x1) → (floc loc, x1)) x.tdNam; tdPrm = x.tdPrm;
   tdPrv = x.tdPrv; tdDef = ctyp floc sh x.tdDef;
   tdCon =
     vala_map (List.map (fun (x1, x2) → (ctyp floc sh x1, ctyp floc sh x2)))
       x.tdCon;
   tdAttributes = attributes floc sh x.tdAttributes}
and type_extension floc sh x =
  {teNam = vala_map (longid_lident floc sh) x.teNam; tePrm = x.tePrm;
   tePrv = x.tePrv;
   teECs = vala_map (List.map (extension_constructor floc sh)) x.teECs ;
   teAttributes = attributes floc sh x.teAttributes}
and extension_constructor floc sh = fun [
    EcTuple loc x1 -> EcTuple (floc loc) (generic_constructor floc sh x1)
  | EcRebind loc x1 x2 x3 -> EcRebind (floc loc) x1 x2 (attributes floc sh x3)
]
and class_type floc sh =
  self where rec self =
    fun
    [ CtAtt loc e attr ->
        let loc = floc loc in
        CtAtt loc (self e) (attribute_body floc sh attr)
    | CtLongLid loc x1 x2 →
        let loc = floc loc in
        CtLongLid loc (longid floc sh x1) x2
    | CtLid loc x1 →
        let loc = floc loc in
        CtLid loc x1
    | CtLop loc x1 x2 x3 →
        let loc = floc loc in
        CtLop loc x1 (longid floc sh x2) (self x3)
    | CtCon loc x1 x2 →
        let loc = floc loc in
        CtCon loc (self x1) (vala_map (List.map (ctyp floc sh)) x2)
    | CtFun loc x1 x2 →
        let loc = floc loc in
        CtFun loc (ctyp floc sh x1) (self x2)
    | CtSig loc x1 x2 →
        let loc = floc loc in
        CtSig loc (vala_map (option_map (ctyp floc sh)) x1)
          (vala_map (List.map (class_sig_item floc sh)) x2)
    | CtXtr loc x1 x2 →
        let loc = floc loc in
        CtXtr loc x1 (option_map (vala_map self) x2)
    | CtExten loc exten ->
        let loc = floc loc in
        CtExten loc (attribute_body floc sh exten)
    ]
and class_sig_item floc sh =
  self where rec self =
    fun
    [ CgCtr loc x1 x2 x3 →
        let loc = floc loc in
        CgCtr loc (ctyp floc sh x1) (ctyp floc sh x2) (attributes floc sh x3)
    | CgDcl loc x1 →
        let loc = floc loc in
        CgDcl loc (vala_map (List.map self) x1)
    | CgInh loc x1 x2 →
        let loc = floc loc in
        CgInh loc (class_type floc sh x1) (attributes floc sh x2)
    | CgMth loc x1 x2 x3 x4 →
        let loc = floc loc in
        CgMth loc x1 x2 (ctyp floc sh x3) (attributes floc sh x4)
    | CgVal loc x1 x2 x3 x4 x5 →
        let loc = floc loc in
        CgVal loc x1 x2 x3 (ctyp floc sh x4) (attributes floc sh x5)
    | CgVir loc x1 x2 x3 x4 →
        let loc = floc loc in
        CgVir loc x1 x2 (ctyp floc sh x3) (attributes floc sh x4)
    | CgFlAtt loc a ->
        let loc = floc loc in
        CgFlAtt loc (attribute_body floc sh a)
    | CgExten loc exten ->
        let loc = floc loc in
        CgExten loc (attribute_body floc sh exten)
    ]
and class_expr floc sh =
  self where rec self =
    fun
    [ CeAtt loc e attr ->
        let loc = floc loc in
       CeAtt loc (self e) (attribute_body floc sh attr)
    | CeApp loc x1 x2 →
        let loc = floc loc in
        CeApp loc (self x1) (expr floc sh x2)
    | CeCon loc x1 x2 →
        let loc = floc loc in
        CeCon loc (vala_map (longid_lident floc sh) x1) (vala_map (List.map (ctyp floc sh)) x2)
    | CeFun loc x1 x2 →
        let loc = floc loc in
        CeFun loc (patt floc sh x1) (self x2)
    | CeLet loc x1 x2 x3 →
        let loc = floc loc in
        CeLet loc x1
          (vala_map
             (List.map (fun (x1, x2, x3) → (patt floc sh x1, expr floc sh x2, attributes floc sh x3)))
             x2)
          (self x3)
    | CeLop loc x1 x2 x3 →
        let loc = floc loc in
        CeLop loc x1 (longid floc sh x2) (self x3)
    | CeStr loc x1 x2 →
        let loc = floc loc in
        CeStr loc (vala_map (option_map (patt floc sh)) x1)
          (vala_map (List.map (class_str_item floc sh)) x2)
    | CeTyc loc x1 x2 →
        let loc = floc loc in
        CeTyc loc (self x1) (class_type floc sh x2)
    | CeXtr loc x1 x2 →
        let loc = floc loc in
        CeXtr loc x1 (option_map (vala_map self) x2)
    | CeExten loc exten ->
        let loc = floc loc in
        CeExten loc (attribute_body floc sh exten)
    ]
and class_str_item floc sh =
  self where rec self =
    fun
    [ CrCtr loc x1 x2 x3 →
        let loc = floc loc in
        CrCtr loc (ctyp floc sh x1) (ctyp floc sh x2) (attributes floc sh x3)
    | CrDcl loc x1 →
        let loc = floc loc in
        CrDcl loc (vala_map (List.map self) x1)
    | CrInh loc ovf x1 x2 x3 →
        let loc = floc loc in
        CrInh loc ovf (class_expr floc sh x1) x2 (attributes floc sh x3)
    | CrIni loc x1 x2 →
        let loc = floc loc in
        CrIni loc (expr floc sh x1) (attributes floc sh x2)
    | CrMth loc x1 x2 x3 x4 x5 x6 →
        let loc = floc loc in
        CrMth loc x1 x2 x3 (vala_map (option_map (ctyp floc sh)) x4)
          (expr floc sh x5) (attributes floc sh x6)
    | CrVal loc x1 x2 x3 x4 x5 →
        let loc = floc loc in
        CrVal loc x1 x2 x3 (expr floc sh x4) (attributes floc sh x5)
    | CrVav loc x1 x2 x3 x4 →
        let loc = floc loc in
        CrVav loc x1 x2 (ctyp floc sh x3) (attributes floc sh x4)
    | CrVir loc x1 x2 x3 x4 →
        let loc = floc loc in
        CrVir loc x1 x2 (ctyp floc sh x3) (attributes floc sh x4)
    | CrFlAtt loc a -> 
        let loc = floc loc in
        CrFlAtt loc (attribute_body floc sh a)
    | CrExten loc exten -> 
        let loc = floc loc in
        CrExten loc (attribute_body floc sh exten)
    ]
and longid_lident floc sh (x1, x2) =
    (option_map (vala_map (longid floc sh)) x1, x2)
and attribute_body floc sh x1 =
    vala_map (fun (s, p) ->
        let s = vala_map (fun (loc, s) -> (floc loc, s)) s in
        let p = match p with [
          StAttr loc x1 ->
            let loc = floc loc in
            StAttr loc (vala_map (List.map (str_item floc sh)) x1)
        | SiAttr loc x1 ->
            let loc = floc loc in
            SiAttr loc (vala_map (List.map (sig_item floc sh)) x1)
        | TyAttr loc x1 ->
            let loc = floc loc in
            TyAttr loc (vala_map (ctyp floc sh) x1)
        | PaAttr loc x1 x2 ->
            let loc = floc loc in
            PaAttr loc (vala_map (patt floc sh) x1) (option_map (vala_map (expr floc sh)) x2)
        ] in
        (s, p)) x1
and attributes_no_anti floc sh x1 = List.map (attribute_body floc sh) x1
and attributes floc sh x1 = vala_map (attributes_no_anti floc sh) x1
;

(* Equality over syntax trees *)

value eq_longid x y =
  longid (fun _ -> Ploc.dummy) 0 x =
  longid (fun _ -> Ploc.dummy) 0 y
;

value eq_longid_lident x y =
  longid_lident (fun _ -> Ploc.dummy) 0 x =
  longid_lident (fun _ -> Ploc.dummy) 0 y
;
value eq_expr x y =
  expr (fun _ -> Ploc.dummy) 0 x =
  expr (fun _ -> Ploc.dummy) 0 y
;
value eq_patt x y =
  patt (fun _ -> Ploc.dummy) 0 x =
  patt (fun _ -> Ploc.dummy) 0 y
;
value eq_ctyp x y =
  ctyp (fun _ -> Ploc.dummy) 0 x =
  ctyp (fun _ -> Ploc.dummy) 0 y
;
value eq_str_item x y =
  str_item (fun _ -> Ploc.dummy) 0 x =
  str_item (fun _ -> Ploc.dummy) 0 y
;
value eq_sig_item x y =
  sig_item (fun _ -> Ploc.dummy) 0 x =
  sig_item (fun _ -> Ploc.dummy) 0 y
;
value eq_module_expr x y =
  module_expr (fun _ -> Ploc.dummy) 0 x =
  module_expr (fun _ -> Ploc.dummy) 0 y
;
value eq_module_type x y =
  module_type (fun _ -> Ploc.dummy) 0 x =
  module_type (fun _ -> Ploc.dummy) 0 y
;
value eq_class_sig_item x y =
  class_sig_item (fun _ -> Ploc.dummy) 0 x =
  class_sig_item (fun _ -> Ploc.dummy) 0 y
;
value eq_class_str_item x y =
  class_str_item (fun _ -> Ploc.dummy) 0 x =
  class_str_item (fun _ -> Ploc.dummy) 0 y
;
value eq_class_type x y =
  class_type (fun _ -> Ploc.dummy) 0 x =
  class_type (fun _ -> Ploc.dummy) 0 y
;
value eq_class_expr x y =
  class_expr (fun _ -> Ploc.dummy) 0 x =
  class_expr (fun _ -> Ploc.dummy) 0 y
;
