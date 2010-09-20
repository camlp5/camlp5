(* camlp5r *)
(* $Id: reloc.ml,v 6.6 2010/09/20 12:29:07 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

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
    Ploc.make
      (line_nb_qloc + line_nb_loc + line_nb_loc1 - 2)
      (if line_nb_loc1 = 1 then
         if line_nb_loc = 1 then Ploc.bol_pos qloc
         else sh1 + Ploc.bol_pos loc
       else sh2 + Ploc.bol_pos loc1)
      (sh2 + Ploc.first_pos loc1, sh2 + Ploc.last_pos loc1)
;

value rec ctyp floc sh =
  self where rec self =
    fun
    [ TyAcc loc x1 x2 -> TyAcc (floc loc) (self x1) (self x2)
    | TyAli loc x1 x2 -> TyAli (floc loc) (self x1) (self x2)
    | TyAny loc -> TyAny (floc loc)
    | TyApp loc x1 x2 -> TyApp (floc loc) (self x1) (self x2)
    | TyArr loc x1 x2 -> TyArr (floc loc) (self x1) (self x2)
    | TyCls loc x1 -> TyCls (floc loc) x1
    | TyLab loc x1 x2 -> TyLab (floc loc) x1 (self x2)
    | TyLid loc x1 -> TyLid (floc loc) x1
    | TyMan loc x1 x2 x3 -> TyMan (floc loc) (self x1) x2 (self x3)
    | TyObj loc x1 x2 ->
        TyObj (floc loc)
          (vala_map (List.map (fun (x1, x2) -> (x1, self x2))) x1) x2
    | TyOlb loc x1 x2 -> TyOlb (floc loc) x1 (self x2)
    | TyPck loc x1 -> TyPck (floc loc) (module_type floc sh x1)
    | TyPol loc x1 x2 -> TyPol (floc loc) x1 (self x2)
    | TyQuo loc x1 -> TyQuo (floc loc) x1
    | TyRec loc x1 ->
        TyRec (floc loc)
          (vala_map
             (List.map (fun (loc, x1, x2, x3) -> (floc loc, x1, x2, self x3)))
             x1)
    | TySum loc x1 ->
        TySum (floc loc)
          (vala_map
             (List.map
                (fun (loc, x1, x2) ->
                   (floc loc, x1, vala_map (List.map self) x2)))
             x1)
    | TyTup loc x1 -> TyTup (floc loc) (vala_map (List.map self) x1)
    | TyUid loc x1 -> TyUid (floc loc) x1
    | TyVrn loc x1 x2 ->
        TyVrn (floc loc) (vala_map (List.map (poly_variant floc sh)) x1) x2
    | IFDEF STRICT THEN
        TyXtr loc x1 x2 -> TyXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and poly_variant floc sh =
  fun
  [ PvTag x1 x2 x3 -> PvTag x1 x2 (vala_map (List.map (ctyp floc sh)) x3)
  | PvInh x1 -> PvInh (ctyp floc sh x1) ]
and patt floc sh =
  self where rec self =
    fun
    [ PaAcc loc x1 x2 -> PaAcc (floc loc) (self x1) (self x2)
    | PaAli loc x1 x2 -> PaAli (floc loc) (self x1) (self x2)
    | PaAnt loc x1 ->
        let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
        patt new_floc sh x1
    | PaAny loc -> PaAny (floc loc)
    | PaApp loc x1 x2 -> PaApp (floc loc) (self x1) (self x2)
    | PaArr loc x1 -> PaArr (floc loc) (vala_map (List.map self) x1)
    | PaChr loc x1 -> PaChr (floc loc) x1
    | PaFlo loc x1 -> PaFlo (floc loc) x1
    | PaInt loc x1 x2 -> PaInt (floc loc) x1 x2
    | PaLab loc x1 x2 ->
        PaLab (floc loc) (self x1) (vala_map (option_map self) x2)
    | PaLaz loc x1 -> PaLaz (floc loc) (self x1)
    | PaLid loc x1 -> PaLid (floc loc) x1
    | PaOlb loc x1 x2 ->
        PaOlb (floc loc) (self x1) (vala_map (option_map (expr floc sh)) x2)
    | PaOrp loc x1 x2 -> PaOrp (floc loc) (self x1) (self x2)
    | PaRec loc x1 ->
        PaRec (floc loc)
          (vala_map (List.map (fun (x1, x2) -> (self x1, self x2))) x1)
    | PaRng loc x1 x2 -> PaRng (floc loc) (self x1) (self x2)
    | PaStr loc x1 -> PaStr (floc loc) x1
    | PaTup loc x1 -> PaTup (floc loc) (vala_map (List.map self) x1)
    | PaTyc loc x1 x2 -> PaTyc (floc loc) (self x1) (ctyp floc sh x2)
    | PaTyp loc x1 -> PaTyp (floc loc) x1
    | PaUid loc x1 -> PaUid (floc loc) x1
    | PaVrn loc x1 -> PaVrn (floc loc) x1
    | IFDEF STRICT THEN
        PaXtr loc x1 x2 -> PaXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and expr floc sh =
  self where rec self =
    fun
    [ ExAcc loc x1 x2 -> ExAcc (floc loc) (self x1) (self x2)
    | ExAnt loc x1 ->
        let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
        expr new_floc sh x1
    | ExApp loc x1 x2 -> ExApp (floc loc) (self x1) (self x2)
    | ExAre loc x1 x2 -> ExAre (floc loc) (self x1) (self x2)
    | ExArr loc x1 -> ExArr (floc loc) (vala_map (List.map self) x1)
    | ExAsr loc x1 -> ExAsr (floc loc) (self x1)
    | ExAss loc x1 x2 -> ExAss (floc loc) (self x1) (self x2)
    | ExBae loc x1 x2 ->
        ExBae (floc loc) (self x1) (vala_map (List.map self) x2)
    | ExChr loc x1 -> ExChr (floc loc) x1
    | ExCoe loc x1 x2 x3 ->
        ExCoe (floc loc) (self x1) (option_map (ctyp floc sh) x2)
          (ctyp floc sh x3)
    | ExFlo loc x1 -> ExFlo (floc loc) x1
    | ExFor loc x1 x2 x3 x4 x5 ->
        ExFor (floc loc) x1 (self x2) (self x3) x4
          (vala_map (List.map self) x5)
    | ExFun loc x1 ->
        ExFun (floc loc)
          (vala_map
             (List.map
                (fun (x1, x2, x3) ->
                   (patt floc sh x1, vala_map (option_map self) x2, self x3)))
             x1)
    | ExIfe loc x1 x2 x3 -> ExIfe (floc loc) (self x1) (self x2) (self x3)
    | ExInt loc x1 x2 -> ExInt (floc loc) x1 x2
    | ExLab loc x1 x2 ->
        ExLab (floc loc) (patt floc sh x1) (vala_map (option_map self) x2)
    | ExLaz loc x1 -> ExLaz (floc loc) (self x1)
    | ExLet loc x1 x2 x3 ->
        ExLet (floc loc) x1
          (vala_map (List.map (fun (x1, x2) -> (patt floc sh x1, self x2)))
             x2)
          (self x3)
    | ExLid loc x1 -> ExLid (floc loc) x1
    | ExLmd loc x1 x2 x3 ->
        ExLmd (floc loc) x1 (module_expr floc sh x2) (self x3)
    | ExMat loc x1 x2 ->
        ExMat (floc loc) (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) ->
                   (patt floc sh x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExNew loc x1 -> ExNew (floc loc) x1
    | ExObj loc x1 x2 ->
        ExObj (floc loc) (vala_map (option_map (patt floc sh)) x1)
          (vala_map (List.map (class_str_item floc sh)) x2)
    | ExOlb loc x1 x2 ->
        ExOlb (floc loc) (patt floc sh x1) (vala_map (option_map self) x2)
    | ExOvr loc x1 ->
        ExOvr (floc loc)
          (vala_map (List.map (fun (x1, x2) -> (x1, self x2))) x1)
    | ExPck loc x1 x2 ->
        ExPck (floc loc) (module_expr floc sh x1) (module_type floc sh x2)
    | ExRec loc x1 x2 ->
        ExRec (floc loc)
          (vala_map (List.map (fun (x1, x2) -> (patt floc sh x1, self x2)))
             x1)
          (option_map self x2)
    | ExSeq loc x1 -> ExSeq (floc loc) (vala_map (List.map self) x1)
    | ExSnd loc x1 x2 -> ExSnd (floc loc) (self x1) x2
    | ExSte loc x1 x2 -> ExSte (floc loc) (self x1) (self x2)
    | ExStr loc x1 -> ExStr (floc loc) x1
    | ExTry loc x1 x2 ->
        ExTry (floc loc) (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) ->
                   (patt floc sh x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExTup loc x1 -> ExTup (floc loc) (vala_map (List.map self) x1)
    | ExTyc loc x1 x2 -> ExTyc (floc loc) (self x1) (ctyp floc sh x2)
    | ExUid loc x1 -> ExUid (floc loc) x1
    | ExVrn loc x1 -> ExVrn (floc loc) x1
    | ExWhi loc x1 x2 ->
        ExWhi (floc loc) (self x1) (vala_map (List.map self) x2)
    | IFDEF STRICT THEN
        ExXtr loc x1 x2 -> ExXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and module_type floc sh =
  self where rec self =
    fun
    [ MtAcc loc x1 x2 -> MtAcc (floc loc) (self x1) (self x2)
    | MtApp loc x1 x2 -> MtApp (floc loc) (self x1) (self x2)
    | MtFun loc x1 x2 x3 -> MtFun (floc loc) x1 (self x2) (self x3)
    | MtLid loc x1 -> MtLid (floc loc) x1
    | MtQuo loc x1 -> MtQuo (floc loc) x1
    | MtSig loc x1 ->
        MtSig (floc loc) (vala_map (List.map (sig_item floc sh)) x1)
    | MtTyo loc x1 -> MtTyo (floc loc) (module_expr floc sh x1)
    | MtUid loc x1 -> MtUid (floc loc) x1
    | MtWit loc x1 x2 ->
        MtWit (floc loc) (self x1)
          (vala_map (List.map (with_constr floc sh)) x2)
    | IFDEF STRICT THEN
        MtXtr loc x1 x2 -> MtXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and sig_item floc sh =
  self where rec self =
    fun
    [ SgCls loc x1 ->
        SgCls (floc loc)
          (vala_map (List.map (class_infos_map floc (class_type floc sh))) x1)
    | SgClt loc x1 ->
        SgClt (floc loc)
          (vala_map (List.map (class_infos_map floc (class_type floc sh))) x1)
    | SgDcl loc x1 -> SgDcl (floc loc) (vala_map (List.map self) x1)
    | SgDir loc x1 x2 ->
        SgDir (floc loc) x1 (vala_map (option_map (expr floc sh)) x2)
    | SgExc loc x1 x2 ->
        SgExc (floc loc) x1 (vala_map (List.map (ctyp floc sh)) x2)
    | SgExt loc x1 x2 x3 -> SgExt (floc loc) x1 (ctyp floc sh x2) x3
    | SgInc loc x1 -> SgInc (floc loc) (module_type floc sh x1)
    | SgMod loc x1 x2 ->
        SgMod (floc loc) x1
          (vala_map (List.map (fun (x1, x2) -> (x1, module_type floc sh x2)))
             x2)
    | SgMty loc x1 x2 -> SgMty (floc loc) x1 (module_type floc sh x2)
    | SgOpn loc x1 -> SgOpn (floc loc) x1
    | SgTyp loc x1 ->
        SgTyp (floc loc) (vala_map (List.map (type_decl floc sh)) x1)
    | SgUse loc x1 x2 ->
        SgUse (floc loc) x1
          (vala_map (List.map (fun (x1, loc) -> (self x1, floc loc))) x2)
    | SgVal loc x1 x2 -> SgVal (floc loc) x1 (ctyp floc sh x2)
    | IFDEF STRICT THEN
        SgXtr loc x1 x2 -> SgXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and with_constr floc sh =
  fun
  [ WcMod loc x1 x2 -> WcMod (floc loc) x1 (module_expr floc sh x2)
  | WcMos loc x1 x2 -> WcMos (floc loc) x1 (module_expr floc sh x2)
  | WcTyp loc x1 x2 x3 x4 -> WcTyp (floc loc) x1 x2 x3 (ctyp floc sh x4)
  | WcTys loc x1 x2 x3 -> WcTys (floc loc) x1 x2 (ctyp floc sh x3) ]
and module_expr floc sh =
  self where rec self =
    fun
    [ MeAcc loc x1 x2 -> MeAcc (floc loc) (self x1) (self x2)
    | MeApp loc x1 x2 -> MeApp (floc loc) (self x1) (self x2)
    | MeFun loc x1 x2 x3 ->
        MeFun (floc loc) x1 (module_type floc sh x2) (self x3)
    | MeStr loc x1 ->
        MeStr (floc loc) (vala_map (List.map (str_item floc sh)) x1)
    | MeTyc loc x1 x2 -> MeTyc (floc loc) (self x1) (module_type floc sh x2)
    | MeUid loc x1 -> MeUid (floc loc) x1
    | MeUnp loc x1 x2 ->
        MeUnp (floc loc) (expr floc sh x1) (module_type floc sh x2)
    | IFDEF STRICT THEN
        MeXtr loc x1 x2 -> MeXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and str_item floc sh =
  self where rec self =
    fun
    [ StCls loc x1 ->
        StCls (floc loc)
          (vala_map (List.map (class_infos_map floc (class_expr floc sh))) x1)
    | StClt loc x1 ->
        StClt (floc loc)
          (vala_map (List.map (class_infos_map floc (class_type floc sh))) x1)
    | StDcl loc x1 -> StDcl (floc loc) (vala_map (List.map self) x1)
    | StDir loc x1 x2 ->
        StDir (floc loc) x1 (vala_map (option_map (expr floc sh)) x2)
    | StExc loc x1 x2 x3 ->
        StExc (floc loc) x1 (vala_map (List.map (ctyp floc sh)) x2) x3
    | StExp loc x1 -> StExp (floc loc) (expr floc sh x1)
    | StExt loc x1 x2 x3 -> StExt (floc loc) x1 (ctyp floc sh x2) x3
    | StInc loc x1 -> StInc (floc loc) (module_expr floc sh x1)
    | StMod loc x1 x2 ->
        StMod (floc loc) x1
          (vala_map (List.map (fun (x1, x2) -> (x1, module_expr floc sh x2)))
             x2)
    | StMty loc x1 x2 -> StMty (floc loc) x1 (module_type floc sh x2)
    | StOpn loc x1 -> StOpn (floc loc) x1
    | StTyp loc x1 ->
        StTyp (floc loc) (vala_map (List.map (type_decl floc sh)) x1)
    | StUse loc x1 x2 ->
        StUse (floc loc) x1
          (vala_map (List.map (fun (x1, loc) -> (self x1, floc loc))) x2)
    | StVal loc x1 x2 ->
        StVal (floc loc) x1
          (vala_map
             (List.map (fun (x1, x2) -> (patt floc sh x1, expr floc sh x2)))
             x2)
    | IFDEF STRICT THEN
        StXtr loc x1 x2 -> StXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and type_decl floc sh x =
  {tdNam = vala_map (fun (loc, x1) -> (floc loc, x1)) x.tdNam;
   tdPrm = x.tdPrm; tdPrv = x.tdPrv; tdDef = ctyp floc sh x.tdDef;
   tdCon =
     vala_map (List.map (fun (x1, x2) -> (ctyp floc sh x1, ctyp floc sh x2)))
       x.tdCon}
and class_type floc sh =
  self where rec self =
    fun
    [ CtAcc loc x1 x2 -> CtAcc (floc loc) (self x1) (self x2)
    | CtApp loc x1 x2 -> CtApp (floc loc) (self x1) (self x2)
    | CtCon loc x1 x2 ->
        CtCon (floc loc) (self x1) (vala_map (List.map (ctyp floc sh)) x2)
    | CtFun loc x1 x2 -> CtFun (floc loc) (ctyp floc sh x1) (self x2)
    | CtIde loc x1 -> CtIde (floc loc) x1
    | CtSig loc x1 x2 ->
        CtSig (floc loc) (vala_map (option_map (ctyp floc sh)) x1)
          (vala_map (List.map (class_sig_item floc sh)) x2)
    | IFDEF STRICT THEN
        CtXtr loc x1 x2 -> CtXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and class_sig_item floc sh =
  self where rec self =
    fun
    [ CgCtr loc x1 x2 -> CgCtr (floc loc) (ctyp floc sh x1) (ctyp floc sh x2)
    | CgDcl loc x1 -> CgDcl (floc loc) (vala_map (List.map self) x1)
    | CgInh loc x1 -> CgInh (floc loc) (class_type floc sh x1)
    | CgMth loc x1 x2 x3 -> CgMth (floc loc) x1 x2 (ctyp floc sh x3)
    | CgVal loc x1 x2 x3 -> CgVal (floc loc) x1 x2 (ctyp floc sh x3)
    | CgVir loc x1 x2 x3 -> CgVir (floc loc) x1 x2 (ctyp floc sh x3) ]
and class_expr floc sh =
  self where rec self =
    fun
    [ CeApp loc x1 x2 -> CeApp (floc loc) (self x1) (expr floc sh x2)
    | CeCon loc x1 x2 ->
        CeCon (floc loc) x1 (vala_map (List.map (ctyp floc sh)) x2)
    | CeFun loc x1 x2 -> CeFun (floc loc) (patt floc sh x1) (self x2)
    | CeLet loc x1 x2 x3 ->
        CeLet (floc loc) x1
          (vala_map
             (List.map (fun (x1, x2) -> (patt floc sh x1, expr floc sh x2)))
             x2)
          (self x3)
    | CeStr loc x1 x2 ->
        CeStr (floc loc) (vala_map (option_map (patt floc sh)) x1)
          (vala_map (List.map (class_str_item floc sh)) x2)
    | CeTyc loc x1 x2 -> CeTyc (floc loc) (self x1) (class_type floc sh x2)
    | IFDEF STRICT THEN
        CeXtr loc x1 x2 -> CeXtr (floc loc) x1 (option_map (vala_map self) x2)
      END ]
and class_str_item floc sh =
  self where rec self =
    fun
    [ CrCtr loc x1 x2 -> CrCtr (floc loc) (ctyp floc sh x1) (ctyp floc sh x2)
    | CrDcl loc x1 -> CrDcl (floc loc) (vala_map (List.map self) x1)
    | CrInh loc x1 x2 -> CrInh (floc loc) (class_expr floc sh x1) x2
    | CrIni loc x1 -> CrIni (floc loc) (expr floc sh x1)
    | CrMth loc x1 x2 x3 x4 x5 ->
        CrMth (floc loc) x1 x2 x3 (vala_map (option_map (ctyp floc sh)) x4)
          (expr floc sh x5)
    | CrVal loc x1 x2 x3 x4 -> CrVal (floc loc) x1 x2 x3 (expr floc sh x4)
    | CrVav loc x1 x2 x3 -> CrVav (floc loc) x1 x2 (ctyp floc sh x3)
    | CrVir loc x1 x2 x3 -> CrVir (floc loc) x1 x2 (ctyp floc sh x3) ]
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
