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

value class_infos_map floc f x =
  {ciLoc = floc x.ciLoc; ciVir = x.ciVir;
   ciPrm =
     let (x1, x2) = x.ciPrm in
     (floc x1, x2);
   ciNam = x.ciNam; ciExp = f x.ciExp}
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
    [ TyAcc loc x1 x2 →
        let loc = floc loc in
        TyAcc loc (self x1) (self x2)
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
        TyCls loc x1
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
        TyObj loc (vala_map (List.map (fun (x1, x2) → (x1, self x2))) x1) x2
    | TyOlb loc x1 x2 →
        let loc = floc loc in
        TyOlb loc x1 (self x2)
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
             (List.map (fun (loc, x1, x2, x3) → (floc loc, x1, x2, self x3)))
             x1)
    | TySum loc x1 →
        let loc = floc loc in
        TySum loc
          (vala_map
             (List.map
                (fun (loc, x1, x2, x3) →
                   (floc loc, x1, vala_map (List.map self) x2,
                    option_map self x3)))
             x1)
    | TyTup loc x1 →
        let loc = floc loc in
        TyTup loc (vala_map (List.map self) x1)
    | TyUid loc x1 →
        let loc = floc loc in
        TyUid loc x1
    | TyVrn loc x1 x2 →
        let loc = floc loc in
        TyVrn loc (vala_map (List.map (poly_variant floc sh)) x1) x2
    | TyXtr loc x1 x2 →
        let loc = floc loc in
        TyXtr loc x1 (option_map (vala_map self) x2) ]
and poly_variant floc sh =
  fun
  [ PvTag loc x1 x2 x3 →
      let loc = floc loc in
      PvTag loc x1 x2 (vala_map (List.map (ctyp floc sh)) x3)
  | PvInh loc x1 →
      let loc = floc loc in
      PvInh loc (ctyp floc sh x1) ]
and patt floc sh =
  self where rec self =
    fun
    [ PaAcc loc x1 x2 →
        let loc = floc loc in
        PaAcc loc (self x1) (self x2)
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
        PaTyp loc x1
    | PaUid loc x1 →
        let loc = floc loc in
        PaUid loc x1
    | PaUnp loc x1 x2 →
        let loc = floc loc in
        PaUnp loc x1 (option_map (module_type floc sh) x2)
    | PaVrn loc x1 →
        let loc = floc loc in
        PaVrn loc x1
    | PaXtr loc x1 x2 →
        let loc = floc loc in
        PaXtr loc x1 (option_map (vala_map self) x2) ]
and expr floc sh =
  self where rec self =
    fun
    [ ExAcc loc x1 x2 →
        let loc = floc loc in
        ExAcc loc (self x1) (self x2)
    | ExAnt loc x1 →
        let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
        expr new_floc sh x1
    | ExApp loc x1 x2 →
        let loc = floc loc in
        ExApp loc (self x1) (self x2)
    | ExAre loc x1 x2 →
        let loc = floc loc in
        ExAre loc (self x1) (self x2)
    | ExArr loc x1 →
        let loc = floc loc in
        ExArr loc (vala_map (List.map self) x1)
    | ExAsr loc x1 →
        let loc = floc loc in
        ExAsr loc (self x1)
    | ExAss loc x1 x2 →
        let loc = floc loc in
        ExAss loc (self x1) (self x2)
    | ExBae loc x1 x2 →
        let loc = floc loc in
        ExBae loc (self x1) (vala_map (List.map self) x2)
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
        ExFor loc x1 (self x2) (self x3) x4 (vala_map (List.map self) x5)
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
    | ExJdf loc x1 x2 →
        let loc = floc loc in
        ExJdf loc (vala_map (List.map (joinclause floc sh)) x1) (self x2)
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
          (vala_map (List.map (fun (x1, x2) → (patt floc sh x1, self x2))) x2)
          (self x3)
    | ExLid loc x1 →
        let loc = floc loc in
        ExLid loc x1
    | ExLmd loc x1 x2 x3 →
        let loc = floc loc in
        ExLmd loc x1 (module_expr floc sh x2) (self x3)
    | ExLop loc x1 x2 →
        let loc = floc loc in
        ExLop loc (module_expr floc sh x1) (self x2)
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
        ExNew loc x1
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
    | ExPar loc x1 x2 →
        let loc = floc loc in
        ExPar loc (self x1) (self x2)
    | ExPck loc x1 x2 →
        let loc = floc loc in
        ExPck loc (module_expr floc sh x1)
          (option_map (module_type floc sh) x2)
    | ExRec loc x1 x2 →
        let loc = floc loc in
        ExRec loc
          (vala_map (List.map (fun (x1, x2) → (patt floc sh x1, self x2))) x1)
          (option_map self x2)
    | ExRpl loc x1 x2 →
        let loc = floc loc in
        ExRpl loc (vala_map (option_map self) x1)
          (vala_map (fun (loc, x1) → (floc loc, x1)) x2)
    | ExSeq loc x1 →
        let loc = floc loc in
        ExSeq loc (vala_map (List.map self) x1)
    | ExSpw loc x1 →
        let loc = floc loc in
        ExSpw loc (self x1)
    | ExSnd loc x1 x2 →
        let loc = floc loc in
        ExSnd loc (self x1) x2
    | ExSte loc x1 x2 →
        let loc = floc loc in
        ExSte loc (self x1) (self x2)
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
    | ExUid loc x1 →
        let loc = floc loc in
        ExUid loc x1
    | ExVrn loc x1 →
        let loc = floc loc in
        ExVrn loc x1
    | ExWhi loc x1 x2 →
        let loc = floc loc in
        ExWhi loc (self x1) (vala_map (List.map self) x2)
    | ExXtr loc x1 x2 →
        let loc = floc loc in
        ExXtr loc x1 (option_map (vala_map self) x2) ]
and module_type floc sh =
  self where rec self =
    fun
    [ MtAcc loc x1 x2 →
        let loc = floc loc in
        MtAcc loc (self x1) (self x2)
    | MtApp loc x1 x2 →
        let loc = floc loc in
        MtApp loc (self x1) (self x2)
    | MtFun loc x1 x2 x3 →
        let loc = floc loc in
        MtFun loc x1 (self x2) (self x3)
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
    | MtUid loc x1 →
        let loc = floc loc in
        MtUid loc x1
    | MtWit loc x1 x2 →
        let loc = floc loc in
        MtWit loc (self x1) (vala_map (List.map (with_constr floc sh)) x2)
    | MtXtr loc x1 x2 →
        let loc = floc loc in
        MtXtr loc x1 (option_map (vala_map self) x2) ]
and sig_item floc sh =
  self where rec self =
    fun
    [ SgCls loc x1 →
        let loc = floc loc in
        SgCls loc
          (vala_map (List.map (class_infos_map floc (class_type floc sh))) x1)
    | SgClt loc x1 →
        let loc = floc loc in
        SgClt loc
          (vala_map (List.map (class_infos_map floc (class_type floc sh))) x1)
    | SgDcl loc x1 →
        let loc = floc loc in
        SgDcl loc (vala_map (List.map self) x1)
    | SgDir loc x1 x2 →
        let loc = floc loc in
        SgDir loc x1 (vala_map (option_map (expr floc sh)) x2)
    | SgExc loc x1 x2 →
        let loc = floc loc in
        SgExc loc x1 (vala_map (List.map (ctyp floc sh)) x2)
    | SgExt loc x1 x2 x3 →
        let loc = floc loc in
        SgExt loc x1 (ctyp floc sh x2) x3
    | SgInc loc x1 →
        let loc = floc loc in
        SgInc loc (module_type floc sh x1)
    | SgMod loc x1 x2 →
        let loc = floc loc in
        SgMod loc x1
          (vala_map (List.map (fun (x1, x2) → (x1, module_type floc sh x2)))
             x2)
    | SgMty loc x1 x2 →
        let loc = floc loc in
        SgMty loc x1 (module_type floc sh x2)
    | SgOpn loc x1 →
        let loc = floc loc in
        SgOpn loc x1
    | SgTyp loc x1 →
        let loc = floc loc in
        SgTyp loc (vala_map (List.map (type_decl floc sh)) x1)
    | SgUse loc x1 x2 →
        let loc = floc loc in
        SgUse loc x1
          (vala_map (List.map (fun (x1, loc) → (self x1, floc loc))) x2)
    | SgVal loc x1 x2 →
        let loc = floc loc in
        SgVal loc x1 (ctyp floc sh x2)
    | SgXtr loc x1 x2 →
        let loc = floc loc in
        SgXtr loc x1 (option_map (vala_map self) x2) ]
and with_constr floc sh =
  fun
  [ WcMod loc x1 x2 →
      let loc = floc loc in
      WcMod loc x1 (module_expr floc sh x2)
  | WcMos loc x1 x2 →
      let loc = floc loc in
      WcMos loc x1 (module_expr floc sh x2)
  | WcTyp loc x1 x2 x3 x4 →
      let loc = floc loc in
      WcTyp loc x1 x2 x3 (ctyp floc sh x4)
  | WcTys loc x1 x2 x3 →
      let loc = floc loc in
      WcTys loc x1 x2 (ctyp floc sh x3) ]
and module_expr floc sh =
  self where rec self =
    fun
    [ MeAcc loc x1 x2 →
        let loc = floc loc in
        MeAcc loc (self x1) (self x2)
    | MeApp loc x1 x2 →
        let loc = floc loc in
        MeApp loc (self x1) (self x2)
    | MeFun loc x1 x2 x3 →
        let loc = floc loc in
        MeFun loc x1 (module_type floc sh x2) (self x3)
    | MeStr loc x1 →
        let loc = floc loc in
        MeStr loc (vala_map (List.map (str_item floc sh)) x1)
    | MeTyc loc x1 x2 →
        let loc = floc loc in
        MeTyc loc (self x1) (module_type floc sh x2)
    | MeUid loc x1 →
        let loc = floc loc in
        MeUid loc x1
    | MeUnp loc x1 x2 →
        let loc = floc loc in
        MeUnp loc (expr floc sh x1) (option_map (module_type floc sh) x2)
    | MeXtr loc x1 x2 →
        let loc = floc loc in
        MeXtr loc x1 (option_map (vala_map self) x2) ]
and str_item floc sh =
  self where rec self =
    fun
    [ StCls loc x1 →
        let loc = floc loc in
        StCls loc
          (vala_map (List.map (class_infos_map floc (class_expr floc sh))) x1)
    | StClt loc x1 →
        let loc = floc loc in
        StClt loc
          (vala_map (List.map (class_infos_map floc (class_type floc sh))) x1)
    | StDcl loc x1 →
        let loc = floc loc in
        StDcl loc (vala_map (List.map self) x1)
    | StDef loc x1 →
        let loc = floc loc in
        StDef loc (vala_map (List.map (joinclause floc sh)) x1)
    | StDir loc x1 x2 →
        let loc = floc loc in
        StDir loc x1 (vala_map (option_map (expr floc sh)) x2)
    | StExc loc x1 x2 x3 →
        let loc = floc loc in
        StExc loc x1 (vala_map (List.map (ctyp floc sh)) x2) x3
    | StExp loc x1 →
        let loc = floc loc in
        StExp loc (expr floc sh x1)
    | StExt loc x1 x2 x3 →
        let loc = floc loc in
        StExt loc x1 (ctyp floc sh x2) x3
    | StInc loc x1 →
        let loc = floc loc in
        StInc loc (module_expr floc sh x1)
    | StMod loc x1 x2 →
        let loc = floc loc in
        StMod loc x1
          (vala_map (List.map (fun (x1, x2) → (x1, module_expr floc sh x2)))
             x2)
    | StMty loc x1 x2 →
        let loc = floc loc in
        StMty loc x1 (module_type floc sh x2)
    | StOpn loc x1 →
        let loc = floc loc in
        StOpn loc x1
    | StTyp loc x1 x2 →
        let loc = floc loc in
        StTyp loc x1 (vala_map (List.map (type_decl floc sh)) x2)
    | StUse loc x1 x2 →
        let loc = floc loc in
        StUse loc x1
          (vala_map (List.map (fun (x1, loc) → (self x1, floc loc))) x2)
    | StVal loc x1 x2 →
        let loc = floc loc in
        StVal loc x1
          (vala_map
             (List.map (fun (x1, x2) → (patt floc sh x1, expr floc sh x2)))
             x2)
    | StXtr loc x1 x2 →
        let loc = floc loc in
        StXtr loc x1 (option_map (vala_map self) x2) ]
and joinclause floc sh x =
  {jcLoc = floc x.jcLoc;
   jcVal =
     vala_map
       (List.map
          (fun (loc, x1, x2) →
             (floc loc,
              vala_map
                (List.map
                   (fun (loc, x1, x2) →
                      (floc loc, (fun (loc, x1) → (floc loc, x1)) x1,
                       vala_map (option_map (patt floc sh)) x2)))
                x1,
              expr floc sh x2)))
       x.jcVal}
and type_decl floc sh x =
  {tdNam = vala_map (fun (loc, x1) → (floc loc, x1)) x.tdNam; tdPrm = x.tdPrm;
   tdPrv = x.tdPrv; tdDef = ctyp floc sh x.tdDef;
   tdCon =
     vala_map (List.map (fun (x1, x2) → (ctyp floc sh x1, ctyp floc sh x2)))
       x.tdCon}
and class_type floc sh =
  self where rec self =
    fun
    [ CtAcc loc x1 x2 →
        let loc = floc loc in
        CtAcc loc (self x1) (self x2)
    | CtApp loc x1 x2 →
        let loc = floc loc in
        CtApp loc (self x1) (self x2)
    | CtCon loc x1 x2 →
        let loc = floc loc in
        CtCon loc (self x1) (vala_map (List.map (ctyp floc sh)) x2)
    | CtFun loc x1 x2 →
        let loc = floc loc in
        CtFun loc (ctyp floc sh x1) (self x2)
    | CtIde loc x1 →
        let loc = floc loc in
        CtIde loc x1
    | CtSig loc x1 x2 →
        let loc = floc loc in
        CtSig loc (vala_map (option_map (ctyp floc sh)) x1)
          (vala_map (List.map (class_sig_item floc sh)) x2)
    | CtXtr loc x1 x2 →
        let loc = floc loc in
        CtXtr loc x1 (option_map (vala_map self) x2) ]
and class_sig_item floc sh =
  self where rec self =
    fun
    [ CgCtr loc x1 x2 →
        let loc = floc loc in
        CgCtr loc (ctyp floc sh x1) (ctyp floc sh x2)
    | CgDcl loc x1 →
        let loc = floc loc in
        CgDcl loc (vala_map (List.map self) x1)
    | CgInh loc x1 →
        let loc = floc loc in
        CgInh loc (class_type floc sh x1)
    | CgMth loc x1 x2 x3 →
        let loc = floc loc in
        CgMth loc x1 x2 (ctyp floc sh x3)
    | CgVal loc x1 x2 x3 →
        let loc = floc loc in
        CgVal loc x1 x2 (ctyp floc sh x3)
    | CgVir loc x1 x2 x3 →
        let loc = floc loc in
        CgVir loc x1 x2 (ctyp floc sh x3) ]
and class_expr floc sh =
  self where rec self =
    fun
    [ CeApp loc x1 x2 →
        let loc = floc loc in
        CeApp loc (self x1) (expr floc sh x2)
    | CeCon loc x1 x2 →
        let loc = floc loc in
        CeCon loc x1 (vala_map (List.map (ctyp floc sh)) x2)
    | CeFun loc x1 x2 →
        let loc = floc loc in
        CeFun loc (patt floc sh x1) (self x2)
    | CeLet loc x1 x2 x3 →
        let loc = floc loc in
        CeLet loc x1
          (vala_map
             (List.map (fun (x1, x2) → (patt floc sh x1, expr floc sh x2)))
             x2)
          (self x3)
    | CeStr loc x1 x2 →
        let loc = floc loc in
        CeStr loc (vala_map (option_map (patt floc sh)) x1)
          (vala_map (List.map (class_str_item floc sh)) x2)
    | CeTyc loc x1 x2 →
        let loc = floc loc in
        CeTyc loc (self x1) (class_type floc sh x2)
    | CeXtr loc x1 x2 →
        let loc = floc loc in
        CeXtr loc x1 (option_map (vala_map self) x2) ]
and class_str_item floc sh =
  self where rec self =
    fun
    [ CrCtr loc x1 x2 →
        let loc = floc loc in
        CrCtr loc (ctyp floc sh x1) (ctyp floc sh x2)
    | CrDcl loc x1 →
        let loc = floc loc in
        CrDcl loc (vala_map (List.map self) x1)
    | CrInh loc x1 x2 →
        let loc = floc loc in
        CrInh loc (class_expr floc sh x1) x2
    | CrIni loc x1 →
        let loc = floc loc in
        CrIni loc (expr floc sh x1)
    | CrMth loc x1 x2 x3 x4 x5 →
        let loc = floc loc in
        CrMth loc x1 x2 x3 (vala_map (option_map (ctyp floc sh)) x4)
          (expr floc sh x5)
    | CrVal loc x1 x2 x3 x4 →
        let loc = floc loc in
        CrVal loc x1 x2 x3 (expr floc sh x4)
    | CrVav loc x1 x2 x3 →
        let loc = floc loc in
        CrVav loc x1 x2 (ctyp floc sh x3)
    | CrVir loc x1 x2 x3 →
        let loc = floc loc in
        CrVir loc x1 x2 (ctyp floc sh x3) ]
;

(* Equality over syntax trees *)

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
