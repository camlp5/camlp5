(* camlp5r *)
(* $Id: mapAst.ml,v 6.10 2011/03/15 11:00:42 deraugla Exp $ *)

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

value class_infos_map mloc f x =
  {ciLoc = mloc x.ciLoc; ciVir = x.ciVir;
   ciPrm =
     let (x1, x2) = x.ciPrm in
     (mloc x1, x2);
   ciNam = x.ciNam; ciExp = f x.ciExp}
;

type map_f =
  { tyAcc : loc → ctyp → ctyp → ctyp;
    tyAli : loc → ctyp → ctyp → ctyp;
    tyAny : loc → ctyp;
    tyApp : loc → ctyp → ctyp → ctyp;
    tyArr : loc → ctyp → ctyp → ctyp;
    tyCls : loc → v (list string) → ctyp;
    tyLab : loc → v string → ctyp → ctyp;
    tyLid : loc → v string → ctyp;
    tyMan : loc → ctyp → v bool → ctyp → ctyp;
    tyObj : loc → v (list (string * ctyp)) → v bool → ctyp;
    tyOlb : loc → v string → ctyp → ctyp;
    tyPck : loc → module_type → ctyp;
    tyPol : loc → v (list string) → ctyp → ctyp;
    tyPot : loc → v (list string) → ctyp → ctyp;
    tyQuo : loc → v string → ctyp;
    tyRec : loc → v (list (loc * string * bool * ctyp)) → ctyp;
    tySum :
      loc → v (list (loc * v string * v (list ctyp) * option ctyp)) → ctyp;
    tyTup : loc → v (list ctyp) → ctyp;
    tyUid : loc → v string → ctyp;
    tyVrn :
      loc → v (list poly_variant) → option (option (v (list string))) → ctyp;
    tyXtr : loc → string → option (v ctyp) → ctyp;
    pvTag : loc → v string → v bool → v (list ctyp) → poly_variant;
    pvInh : loc → ctyp → poly_variant;
    paAcc : loc → patt → patt → patt;
    paAli : loc → patt → patt → patt;
    paAnt : loc → patt → patt;
    paAny : loc → patt;
    paApp : loc → patt → patt → patt;
    paArr : loc → v (list patt) → patt;
    paChr : loc → v string → patt;
    paFlo : loc → v string → patt;
    paInt : loc → v string → string → patt;
    paLab : loc → v (list (patt * v (option patt))) → patt;
    paLaz : loc → patt → patt;
    paLid : loc → v string → patt;
    paNty : loc → v string → patt;
    paOlb : loc → patt → v (option expr) → patt;
    paOrp : loc → patt → patt → patt;
    paRec : loc → v (list (patt * patt)) → patt;
    paRng : loc → patt → patt → patt;
    paStr : loc → v string → patt;
    paTup : loc → v (list patt) → patt;
    paTyc : loc → patt → ctyp → patt;
    paTyp : loc → v (list string) → patt;
    paUid : loc → v string → patt;
    paUnp : loc → v string → option module_type → patt;
    paVrn : loc → v string → patt;
    paXtr : loc → string → option (v patt) → patt;
    exAcc : loc → expr → expr → expr;
    exAnt : loc → expr → expr;
    exApp : loc → expr → expr → expr;
    exAre : loc → expr → expr → expr;
    exArr : loc → v (list expr) → expr;
    exAsr : loc → expr → expr;
    exAss : loc → expr → expr → expr;
    exBae : loc → expr → v (list expr) → expr;
    exChr : loc → v string → expr;
    exCoe : loc → expr → option ctyp → ctyp → expr;
    exFlo : loc → v string → expr;
    exFor : loc → v string → expr → expr → v bool → v (list expr) → expr;
    exFun : loc → v (list (patt * v (option expr) * expr)) → expr;
    exIfe : loc → expr → expr → expr → expr;
    exInt : loc → v string → string → expr;
    exLab : loc → v (list (patt * v (option expr))) → expr;
    exLaz : loc → expr → expr;
    exLet : loc → v bool → v (list (patt * expr)) → expr → expr;
    exLid : loc → v string → expr;
    exLmd : loc → v string → module_expr → expr → expr;
    exMat : loc → expr → v (list (patt * v (option expr) * expr)) → expr;
    exNew : loc → v (list string) → expr;
    exObj : loc → v (option patt) → v (list class_str_item) → expr;
    exOlb : loc → patt → v (option expr) → expr;
    exOvr : loc → v (list (string * expr)) → expr;
    exPck : loc → module_expr → option module_type → expr;
    exRec : loc → v (list (patt * expr)) → option expr → expr;
    exSeq : loc → v (list expr) → expr;
    exSnd : loc → expr → v string → expr;
    exSte : loc → expr → expr → expr;
    exStr : loc → v string → expr;
    exTry : loc → expr → v (list (patt * v (option expr) * expr)) → expr;
    exTup : loc → v (list expr) → expr;
    exTyc : loc → expr → ctyp → expr;
    exUid : loc → v string → expr;
    exVrn : loc → v string → expr;
    exWhi : loc → expr → v (list expr) → expr;
    exXtr : loc → string → option (v expr) → expr;
    mtAcc : loc → module_type → module_type → module_type;
    mtApp : loc → module_type → module_type → module_type;
    mtFun : loc → v string → module_type → module_type → module_type;
    mtLid : loc → v string → module_type;
    mtQuo : loc → v string → module_type;
    mtSig : loc → v (list sig_item) → module_type;
    mtTyo : loc → module_expr → module_type;
    mtUid : loc → v string → module_type;
    mtWit : loc → module_type → v (list with_constr) → module_type;
    mtXtr : loc → string → option (v module_type) → module_type;
    sgCls : loc → v (list (class_infos class_type)) → sig_item;
    sgClt : loc → v (list (class_infos class_type)) → sig_item;
    sgDcl : loc → v (list sig_item) → sig_item;
    sgDir : loc → v string → v (option expr) → sig_item;
    sgExc : loc → v string → v (list ctyp) → sig_item;
    sgExt : loc → v string → ctyp → v (list string) → sig_item;
    sgInc : loc → module_type → sig_item;
    sgMod : loc → v bool → v (list (v string * module_type)) → sig_item;
    sgMty : loc → v string → module_type → sig_item;
    sgOpn : loc → v (list string) → sig_item;
    sgTyp : loc → v (list type_decl) → sig_item;
    sgUse : loc → v string → v (list (sig_item * loc)) → sig_item;
    sgVal : loc → v string → ctyp → sig_item;
    sgXtr : loc → string → option (v sig_item) → sig_item;
    wcMod : loc → v (list string) → module_expr → with_constr;
    wcMos : loc → v (list string) → module_expr → with_constr;
    wcTyp :
      loc → v (list string) → v (list type_var) → v bool → ctyp → with_constr;
    wcTys : loc → v (list string) → v (list type_var) → ctyp → with_constr;
    meAcc : loc → module_expr → module_expr → module_expr;
    meApp : loc → module_expr → module_expr → module_expr;
    meFun : loc → v string → module_type → module_expr → module_expr;
    meStr : loc → v (list str_item) → module_expr;
    meTyc : loc → module_expr → module_type → module_expr;
    meUid : loc → v string → module_expr;
    meUnp : loc → expr → option module_type → module_expr;
    meXtr : loc → string → option (v module_expr) → module_expr;
    stCls : loc → v (list (class_infos class_expr)) → str_item;
    stClt : loc → v (list (class_infos class_type)) → str_item;
    stDcl : loc → v (list str_item) → str_item;
    stDir : loc → v string → v (option expr) → str_item;
    stExc : loc → v string → v (list ctyp) → v (list string) → str_item;
    stExp : loc → expr → str_item;
    stExt : loc → v string → ctyp → v (list string) → str_item;
    stInc : loc → module_expr → str_item;
    stMod : loc → v bool → v (list (v string * module_expr)) → str_item;
    stMty : loc → v string → module_type → str_item;
    stOpn : loc → v (list string) → str_item;
    stTyp : loc → v (list type_decl) → str_item;
    stUse : loc → v string → v (list (str_item * loc)) → str_item;
    stVal : loc → v bool → v (list (patt * expr)) → str_item;
    stXtr : loc → string → option (v str_item) → str_item;
    ctAcc : loc → class_type → class_type → class_type;
    ctApp : loc → class_type → class_type → class_type;
    ctCon : loc → class_type → v (list ctyp) → class_type;
    ctFun : loc → ctyp → class_type → class_type;
    ctIde : loc → v string → class_type;
    ctSig : loc → v (option ctyp) → v (list class_sig_item) → class_type;
    ctXtr : loc → string → option (v class_type) → class_type;
    cgCtr : loc → ctyp → ctyp → class_sig_item;
    cgDcl : loc → v (list class_sig_item) → class_sig_item;
    cgInh : loc → class_type → class_sig_item;
    cgMth : loc → v bool → v string → ctyp → class_sig_item;
    cgVal : loc → v bool → v string → ctyp → class_sig_item;
    cgVir : loc → v bool → v string → ctyp → class_sig_item;
    ceApp : loc → class_expr → expr → class_expr;
    ceCon : loc → v (list string) → v (list ctyp) → class_expr;
    ceFun : loc → patt → class_expr → class_expr;
    ceLet : loc → v bool → v (list (patt * expr)) → class_expr → class_expr;
    ceStr : loc → v (option patt) → v (list class_str_item) → class_expr;
    ceTyc : loc → class_expr → class_type → class_expr;
    ceXtr : loc → string → option (v class_expr) → class_expr;
    crCtr : loc → ctyp → ctyp → class_str_item;
    crDcl : loc → v (list class_str_item) → class_str_item;
    crInh : loc → class_expr → v (option string) → class_str_item;
    crIni : loc → expr → class_str_item;
    crMth :
      loc → v bool → v bool → v string → v (option ctyp) → expr →
        class_str_item;
    crVal : loc → v bool → v bool → v string → expr → class_str_item;
    crVav : loc → v bool → v string → ctyp → class_str_item;
    crVir : loc → v bool → v string → ctyp → class_str_item;
    mloc : loc → loc;
    anti_loc : loc → loc → loc → loc }
;

value with_mloc f mloc = do {
  let f : map_f = Obj.magic (Array.copy (Obj.magic (f : map_f))) in
  f.mloc := mloc;
  f
};

value rec def =
  {tyAcc loc x1 x2 = TyAcc loc x1 x2; tyAli loc x1 x2 = TyAli loc x1 x2;
   tyAny loc = TyAny loc; tyApp loc x1 x2 = TyApp loc x1 x2;
   tyArr loc x1 x2 = TyArr loc x1 x2; tyCls loc x1 = TyCls loc x1;
   tyLab loc x1 x2 = TyLab loc x1 x2; tyLid loc x1 = TyLid loc x1;
   tyMan loc x1 x2 x3 = TyMan loc x1 x2 x3; tyObj loc x1 x2 = TyObj loc x1 x2;
   tyOlb loc x1 x2 = TyOlb loc x1 x2; tyPck loc x1 = TyPck loc x1;
   tyPol loc x1 x2 = TyPol loc x1 x2; tyPot loc x1 x2 = TyPot loc x1 x2;
   tyQuo loc x1 = TyQuo loc x1; tyRec loc x1 = TyRec loc x1;
   tySum loc x1 = TySum loc x1; tyTup loc x1 = TyTup loc x1;
   tyUid loc x1 = TyUid loc x1; tyVrn loc x1 x2 = TyVrn loc x1 x2;
   tyXtr loc x1 x2 = TyXtr loc x1 x2; pvTag loc x1 x2 x3 = PvTag loc x1 x2 x3;
   pvInh loc x1 = PvInh loc x1; paAcc loc x1 x2 = PaAcc loc x1 x2;
   paAli loc x1 x2 = PaAli loc x1 x2; paAnt loc x1 = PaAnt loc x1;
   paAny loc = PaAny loc; paApp loc x1 x2 = PaApp loc x1 x2;
   paArr loc x1 = PaArr loc x1; paChr loc x1 = PaChr loc x1;
   paFlo loc x1 = PaFlo loc x1; paInt loc x1 x2 = PaInt loc x1 x2;
   paLab loc x1 = PaLab loc x1; paLaz loc x1 = PaLaz loc x1;
   paLid loc x1 = PaLid loc x1; paNty loc x1 = PaNty loc x1;
   paOlb loc x1 x2 = PaOlb loc x1 x2; paOrp loc x1 x2 = PaOrp loc x1 x2;
   paRec loc x1 = PaRec loc x1; paRng loc x1 x2 = PaRng loc x1 x2;
   paStr loc x1 = PaStr loc x1; paTup loc x1 = PaTup loc x1;
   paTyc loc x1 x2 = PaTyc loc x1 x2; paTyp loc x1 = PaTyp loc x1;
   paUid loc x1 = PaUid loc x1; paUnp loc x1 x2 = PaUnp loc x1 x2;
   paVrn loc x1 = PaVrn loc x1; paXtr loc x1 x2 = PaXtr loc x1 x2;
   exAcc loc x1 x2 = ExAcc loc x1 x2; exAnt loc x1 = ExAnt loc x1;
   exApp loc x1 x2 = ExApp loc x1 x2; exAre loc x1 x2 = ExAre loc x1 x2;
   exArr loc x1 = ExArr loc x1; exAsr loc x1 = ExAsr loc x1;
   exAss loc x1 x2 = ExAss loc x1 x2; exBae loc x1 x2 = ExBae loc x1 x2;
   exChr loc x1 = ExChr loc x1; exCoe loc x1 x2 x3 = ExCoe loc x1 x2 x3;
   exFlo loc x1 = ExFlo loc x1;
   exFor loc x1 x2 x3 x4 x5 = ExFor loc x1 x2 x3 x4 x5;
   exFun loc x1 = ExFun loc x1; exIfe loc x1 x2 x3 = ExIfe loc x1 x2 x3;
   exInt loc x1 x2 = ExInt loc x1 x2; exLab loc x1 = ExLab loc x1;
   exLaz loc x1 = ExLaz loc x1; exLet loc x1 x2 x3 = ExLet loc x1 x2 x3;
   exLid loc x1 = ExLid loc x1; exLmd loc x1 x2 x3 = ExLmd loc x1 x2 x3;
   exMat loc x1 x2 = ExMat loc x1 x2; exNew loc x1 = ExNew loc x1;
   exObj loc x1 x2 = ExObj loc x1 x2; exOlb loc x1 x2 = ExOlb loc x1 x2;
   exOvr loc x1 = ExOvr loc x1; exPck loc x1 x2 = ExPck loc x1 x2;
   exRec loc x1 x2 = ExRec loc x1 x2; exSeq loc x1 = ExSeq loc x1;
   exSnd loc x1 x2 = ExSnd loc x1 x2; exSte loc x1 x2 = ExSte loc x1 x2;
   exStr loc x1 = ExStr loc x1; exTry loc x1 x2 = ExTry loc x1 x2;
   exTup loc x1 = ExTup loc x1; exTyc loc x1 x2 = ExTyc loc x1 x2;
   exUid loc x1 = ExUid loc x1; exVrn loc x1 = ExVrn loc x1;
   exWhi loc x1 x2 = ExWhi loc x1 x2; exXtr loc x1 x2 = ExXtr loc x1 x2;
   mtAcc loc x1 x2 = MtAcc loc x1 x2; mtApp loc x1 x2 = MtApp loc x1 x2;
   mtFun loc x1 x2 x3 = MtFun loc x1 x2 x3; mtLid loc x1 = MtLid loc x1;
   mtQuo loc x1 = MtQuo loc x1; mtSig loc x1 = MtSig loc x1;
   mtTyo loc x1 = MtTyo loc x1; mtUid loc x1 = MtUid loc x1;
   mtWit loc x1 x2 = MtWit loc x1 x2; mtXtr loc x1 x2 = MtXtr loc x1 x2;
   sgCls loc x1 = SgCls loc x1; sgClt loc x1 = SgClt loc x1;
   sgDcl loc x1 = SgDcl loc x1; sgDir loc x1 x2 = SgDir loc x1 x2;
   sgExc loc x1 x2 = SgExc loc x1 x2; sgExt loc x1 x2 x3 = SgExt loc x1 x2 x3;
   sgInc loc x1 = SgInc loc x1; sgMod loc x1 x2 = SgMod loc x1 x2;
   sgMty loc x1 x2 = SgMty loc x1 x2; sgOpn loc x1 = SgOpn loc x1;
   sgTyp loc x1 = SgTyp loc x1; sgUse loc x1 x2 = SgUse loc x1 x2;
   sgVal loc x1 x2 = SgVal loc x1 x2; sgXtr loc x1 x2 = SgXtr loc x1 x2;
   wcMod loc x1 x2 = WcMod loc x1 x2; wcMos loc x1 x2 = WcMos loc x1 x2;
   wcTyp loc x1 x2 x3 x4 = WcTyp loc x1 x2 x3 x4;
   wcTys loc x1 x2 x3 = WcTys loc x1 x2 x3; meAcc loc x1 x2 = MeAcc loc x1 x2;
   meApp loc x1 x2 = MeApp loc x1 x2; meFun loc x1 x2 x3 = MeFun loc x1 x2 x3;
   meStr loc x1 = MeStr loc x1; meTyc loc x1 x2 = MeTyc loc x1 x2;
   meUid loc x1 = MeUid loc x1; meUnp loc x1 x2 = MeUnp loc x1 x2;
   meXtr loc x1 x2 = MeXtr loc x1 x2; stCls loc x1 = StCls loc x1;
   stClt loc x1 = StClt loc x1; stDcl loc x1 = StDcl loc x1;
   stDir loc x1 x2 = StDir loc x1 x2; stExc loc x1 x2 x3 = StExc loc x1 x2 x3;
   stExp loc x1 = StExp loc x1; stExt loc x1 x2 x3 = StExt loc x1 x2 x3;
   stInc loc x1 = StInc loc x1; stMod loc x1 x2 = StMod loc x1 x2;
   stMty loc x1 x2 = StMty loc x1 x2; stOpn loc x1 = StOpn loc x1;
   stTyp loc x1 = StTyp loc x1; stUse loc x1 x2 = StUse loc x1 x2;
   stVal loc x1 x2 = StVal loc x1 x2; stXtr loc x1 x2 = StXtr loc x1 x2;
   ctAcc loc x1 x2 = CtAcc loc x1 x2; ctApp loc x1 x2 = CtApp loc x1 x2;
   ctCon loc x1 x2 = CtCon loc x1 x2; ctFun loc x1 x2 = CtFun loc x1 x2;
   ctIde loc x1 = CtIde loc x1; ctSig loc x1 x2 = CtSig loc x1 x2;
   ctXtr loc x1 x2 = CtXtr loc x1 x2; cgCtr loc x1 x2 = CgCtr loc x1 x2;
   cgDcl loc x1 = CgDcl loc x1; cgInh loc x1 = CgInh loc x1;
   cgMth loc x1 x2 x3 = CgMth loc x1 x2 x3;
   cgVal loc x1 x2 x3 = CgVal loc x1 x2 x3;
   cgVir loc x1 x2 x3 = CgVir loc x1 x2 x3; ceApp loc x1 x2 = CeApp loc x1 x2;
   ceCon loc x1 x2 = CeCon loc x1 x2; ceFun loc x1 x2 = CeFun loc x1 x2;
   ceLet loc x1 x2 x3 = CeLet loc x1 x2 x3; ceStr loc x1 x2 = CeStr loc x1 x2;
   ceTyc loc x1 x2 = CeTyc loc x1 x2; ceXtr loc x1 x2 = CeXtr loc x1 x2;
   crCtr loc x1 x2 = CrCtr loc x1 x2; crDcl loc x1 = CrDcl loc x1;
   crInh loc x1 x2 = CrInh loc x1 x2; crIni loc x1 = CrIni loc x1;
   crMth loc x1 x2 x3 x4 x5 = CrMth loc x1 x2 x3 x4 x5;
   crVal loc x1 x2 x3 x4 = CrVal loc x1 x2 x3 x4;
   crVav loc x1 x2 x3 = CrVav loc x1 x2 x3;
   crVir loc x1 x2 x3 = CrVir loc x1 x2 x3; mloc loc = loc;
   anti_loc qloc loc loc1 = qloc}
;

value rec ctyp f =
  self where rec self =
    fun
    [ TyAcc loc x1 x2 → f.tyAcc (f.mloc loc) (self x1) (self x2)
    | TyAli loc x1 x2 → f.tyAli (f.mloc loc) (self x1) (self x2)
    | TyAny loc → f.tyAny (f.mloc loc)
    | TyApp loc x1 x2 → f.tyApp (f.mloc loc) (self x1) (self x2)
    | TyArr loc x1 x2 → f.tyArr (f.mloc loc) (self x1) (self x2)
    | TyCls loc x1 → f.tyCls (f.mloc loc) x1
    | TyLab loc x1 x2 → f.tyLab (f.mloc loc) x1 (self x2)
    | TyLid loc x1 → f.tyLid (f.mloc loc) x1
    | TyMan loc x1 x2 x3 → f.tyMan (f.mloc loc) (self x1) x2 (self x3)
    | TyObj loc x1 x2 →
        f.tyObj (f.mloc loc)
          (vala_map (List.map (fun (x1, x2) → (x1, self x2))) x1) x2
    | TyOlb loc x1 x2 → f.tyOlb (f.mloc loc) x1 (self x2)
    | TyPck loc x1 → f.tyPck (f.mloc loc) (module_type f x1)
    | TyPol loc x1 x2 → f.tyPol (f.mloc loc) x1 (self x2)
    | TyPot loc x1 x2 → f.tyPot (f.mloc loc) x1 (self x2)
    | TyQuo loc x1 → f.tyQuo (f.mloc loc) x1
    | TyRec loc x1 →
        f.tyRec (f.mloc loc)
          (vala_map
             (List.map
                (fun (loc, x1, x2, x3) → (f.mloc loc, x1, x2, self x3)))
             x1)
    | TySum loc x1 →
        f.tySum (f.mloc loc)
          (vala_map
             (List.map
                (fun (loc, x1, x2, x3) →
                   (f.mloc loc, x1, vala_map (List.map self) x2,
                    option_map self x3)))
             x1)
    | TyTup loc x1 → f.tyTup (f.mloc loc) (vala_map (List.map self) x1)
    | TyUid loc x1 → f.tyUid (f.mloc loc) x1
    | TyVrn loc x1 x2 →
        f.tyVrn (f.mloc loc) (vala_map (List.map (poly_variant f)) x1) x2
    | TyXtr loc x1 x2 →
        f.tyXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and poly_variant f =
  fun
  [ PvTag loc x1 x2 x3 →
      f.pvTag (f.mloc loc) x1 x2 (vala_map (List.map (ctyp f)) x3)
  | PvInh loc x1 → f.pvInh (f.mloc loc) (ctyp f x1) ]
and patt f =
  self where rec self =
    fun
    [ PaAcc loc x1 x2 → f.paAcc (f.mloc loc) (self x1) (self x2)
    | PaAli loc x1 x2 → f.paAli (f.mloc loc) (self x1) (self x2)
    | PaAnt loc x1 →
        let new_mloc loc1 = f.anti_loc (f.mloc loc) loc loc1 in
        patt {(f) with mloc = new_mloc} x1
    | PaAny loc → f.paAny (f.mloc loc)
    | PaApp loc x1 x2 → f.paApp (f.mloc loc) (self x1) (self x2)
    | PaArr loc x1 → f.paArr (f.mloc loc) (vala_map (List.map self) x1)
    | PaChr loc x1 → f.paChr (f.mloc loc) x1
    | PaFlo loc x1 → f.paFlo (f.mloc loc) x1
    | PaInt loc x1 x2 → f.paInt (f.mloc loc) x1 x2
    | PaLab loc x1 →
        f.paLab (f.mloc loc)
          (vala_map
             (List.map
                (fun (x1, x2) → (self x1, vala_map (option_map self) x2)))
             x1)
    | PaLaz loc x1 → f.paLaz (f.mloc loc) (self x1)
    | PaLid loc x1 → f.paLid (f.mloc loc) x1
    | PaNty loc x1 → f.paNty (f.mloc loc) x1
    | PaOlb loc x1 x2 →
        f.paOlb (f.mloc loc) (self x1) (vala_map (option_map (expr f)) x2)
    | PaOrp loc x1 x2 → f.paOrp (f.mloc loc) (self x1) (self x2)
    | PaRec loc x1 →
        f.paRec (f.mloc loc)
          (vala_map (List.map (fun (x1, x2) → (self x1, self x2))) x1)
    | PaRng loc x1 x2 → f.paRng (f.mloc loc) (self x1) (self x2)
    | PaStr loc x1 → f.paStr (f.mloc loc) x1
    | PaTup loc x1 → f.paTup (f.mloc loc) (vala_map (List.map self) x1)
    | PaTyc loc x1 x2 → f.paTyc (f.mloc loc) (self x1) (ctyp f x2)
    | PaTyp loc x1 → f.paTyp (f.mloc loc) x1
    | PaUid loc x1 → f.paUid (f.mloc loc) x1
    | PaUnp loc x1 x2 →
        f.paUnp (f.mloc loc) x1 (option_map (module_type f) x2)
    | PaVrn loc x1 → f.paVrn (f.mloc loc) x1
    | PaXtr loc x1 x2 →
        f.paXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and expr f =
  self where rec self =
    fun
    [ ExAcc loc x1 x2 → f.exAcc (f.mloc loc) (self x1) (self x2)
    | ExAnt loc x1 →
        let new_mloc loc1 = f.anti_loc (f.mloc loc) loc loc1 in
        expr {(f) with mloc = new_mloc} x1
    | ExApp loc x1 x2 → f.exApp (f.mloc loc) (self x1) (self x2)
    | ExAre loc x1 x2 → f.exAre (f.mloc loc) (self x1) (self x2)
    | ExArr loc x1 → f.exArr (f.mloc loc) (vala_map (List.map self) x1)
    | ExAsr loc x1 → f.exAsr (f.mloc loc) (self x1)
    | ExAss loc x1 x2 → f.exAss (f.mloc loc) (self x1) (self x2)
    | ExBae loc x1 x2 →
        f.exBae (f.mloc loc) (self x1) (vala_map (List.map self) x2)
    | ExChr loc x1 → f.exChr (f.mloc loc) x1
    | ExCoe loc x1 x2 x3 →
        f.exCoe (f.mloc loc) (self x1) (option_map (ctyp f) x2) (ctyp f x3)
    | ExFlo loc x1 → f.exFlo (f.mloc loc) x1
    | ExFor loc x1 x2 x3 x4 x5 →
        f.exFor (f.mloc loc) x1 (self x2) (self x3) x4
          (vala_map (List.map self) x5)
    | ExFun loc x1 →
        f.exFun (f.mloc loc)
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt f x1, vala_map (option_map self) x2, self x3)))
             x1)
    | ExIfe loc x1 x2 x3 → f.exIfe (f.mloc loc) (self x1) (self x2) (self x3)
    | ExInt loc x1 x2 → f.exInt (f.mloc loc) x1 x2
    | ExLab loc x1 →
        f.exLab (f.mloc loc)
          (vala_map
             (List.map
                (fun (x1, x2) → (patt f x1, vala_map (option_map self) x2)))
             x1)
    | ExLaz loc x1 → f.exLaz (f.mloc loc) (self x1)
    | ExLet loc x1 x2 x3 →
        f.exLet (f.mloc loc) x1
          (vala_map (List.map (fun (x1, x2) → (patt f x1, self x2))) x2)
          (self x3)
    | ExLid loc x1 → f.exLid (f.mloc loc) x1
    | ExLmd loc x1 x2 x3 →
        f.exLmd (f.mloc loc) x1 (module_expr f x2) (self x3)
    | ExMat loc x1 x2 →
        f.exMat (f.mloc loc) (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt f x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExNew loc x1 → f.exNew (f.mloc loc) x1
    | ExObj loc x1 x2 →
        f.exObj (f.mloc loc) (vala_map (option_map (patt f)) x1)
          (vala_map (List.map (class_str_item f)) x2)
    | ExOlb loc x1 x2 →
        f.exOlb (f.mloc loc) (patt f x1) (vala_map (option_map self) x2)
    | ExOvr loc x1 →
        f.exOvr (f.mloc loc)
          (vala_map (List.map (fun (x1, x2) → (x1, self x2))) x1)
    | ExPck loc x1 x2 →
        f.exPck (f.mloc loc) (module_expr f x1)
          (option_map (module_type f) x2)
    | ExRec loc x1 x2 →
        f.exRec (f.mloc loc)
          (vala_map (List.map (fun (x1, x2) → (patt f x1, self x2))) x1)
          (option_map self x2)
    | ExSeq loc x1 → f.exSeq (f.mloc loc) (vala_map (List.map self) x1)
    | ExSnd loc x1 x2 → f.exSnd (f.mloc loc) (self x1) x2
    | ExSte loc x1 x2 → f.exSte (f.mloc loc) (self x1) (self x2)
    | ExStr loc x1 → f.exStr (f.mloc loc) x1
    | ExTry loc x1 x2 →
        f.exTry (f.mloc loc) (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt f x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExTup loc x1 → f.exTup (f.mloc loc) (vala_map (List.map self) x1)
    | ExTyc loc x1 x2 → f.exTyc (f.mloc loc) (self x1) (ctyp f x2)
    | ExUid loc x1 → f.exUid (f.mloc loc) x1
    | ExVrn loc x1 → f.exVrn (f.mloc loc) x1
    | ExWhi loc x1 x2 →
        f.exWhi (f.mloc loc) (self x1) (vala_map (List.map self) x2)
    | ExXtr loc x1 x2 →
        f.exXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and module_type f =
  self where rec self =
    fun
    [ MtAcc loc x1 x2 → f.mtAcc (f.mloc loc) (self x1) (self x2)
    | MtApp loc x1 x2 → f.mtApp (f.mloc loc) (self x1) (self x2)
    | MtFun loc x1 x2 x3 → f.mtFun (f.mloc loc) x1 (self x2) (self x3)
    | MtLid loc x1 → f.mtLid (f.mloc loc) x1
    | MtQuo loc x1 → f.mtQuo (f.mloc loc) x1
    | MtSig loc x1 →
        f.mtSig (f.mloc loc) (vala_map (List.map (sig_item f)) x1)
    | MtTyo loc x1 → f.mtTyo (f.mloc loc) (module_expr f x1)
    | MtUid loc x1 → f.mtUid (f.mloc loc) x1
    | MtWit loc x1 x2 →
        f.mtWit (f.mloc loc) (self x1)
          (vala_map (List.map (with_constr f)) x2)
    | MtXtr loc x1 x2 →
        f.mtXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and sig_item f =
  self where rec self =
    fun
    [ SgCls loc x1 →
        f.sgCls (f.mloc loc)
          (vala_map (List.map (class_infos_map f.mloc (class_type f))) x1)
    | SgClt loc x1 →
        f.sgClt (f.mloc loc)
          (vala_map (List.map (class_infos_map f.mloc (class_type f))) x1)
    | SgDcl loc x1 → f.sgDcl (f.mloc loc) (vala_map (List.map self) x1)
    | SgDir loc x1 x2 →
        f.sgDir (f.mloc loc) x1 (vala_map (option_map (expr f)) x2)
    | SgExc loc x1 x2 →
        f.sgExc (f.mloc loc) x1 (vala_map (List.map (ctyp f)) x2)
    | SgExt loc x1 x2 x3 → f.sgExt (f.mloc loc) x1 (ctyp f x2) x3
    | SgInc loc x1 → f.sgInc (f.mloc loc) (module_type f x1)
    | SgMod loc x1 x2 →
        f.sgMod (f.mloc loc) x1
          (vala_map (List.map (fun (x1, x2) → (x1, module_type f x2))) x2)
    | SgMty loc x1 x2 → f.sgMty (f.mloc loc) x1 (module_type f x2)
    | SgOpn loc x1 → f.sgOpn (f.mloc loc) x1
    | SgTyp loc x1 →
        f.sgTyp (f.mloc loc) (vala_map (List.map (type_decl f)) x1)
    | SgUse loc x1 x2 →
        f.sgUse (f.mloc loc) x1
          (vala_map (List.map (fun (x1, loc) → (self x1, f.mloc loc))) x2)
    | SgVal loc x1 x2 → f.sgVal (f.mloc loc) x1 (ctyp f x2)
    | SgXtr loc x1 x2 →
        f.sgXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and with_constr f =
  fun
  [ WcMod loc x1 x2 → f.wcMod (f.mloc loc) x1 (module_expr f x2)
  | WcMos loc x1 x2 → f.wcMos (f.mloc loc) x1 (module_expr f x2)
  | WcTyp loc x1 x2 x3 x4 → f.wcTyp (f.mloc loc) x1 x2 x3 (ctyp f x4)
  | WcTys loc x1 x2 x3 → f.wcTys (f.mloc loc) x1 x2 (ctyp f x3) ]
and module_expr f =
  self where rec self =
    fun
    [ MeAcc loc x1 x2 → f.meAcc (f.mloc loc) (self x1) (self x2)
    | MeApp loc x1 x2 → f.meApp (f.mloc loc) (self x1) (self x2)
    | MeFun loc x1 x2 x3 →
        f.meFun (f.mloc loc) x1 (module_type f x2) (self x3)
    | MeStr loc x1 →
        f.meStr (f.mloc loc) (vala_map (List.map (str_item f)) x1)
    | MeTyc loc x1 x2 → f.meTyc (f.mloc loc) (self x1) (module_type f x2)
    | MeUid loc x1 → f.meUid (f.mloc loc) x1
    | MeUnp loc x1 x2 →
        f.meUnp (f.mloc loc) (expr f x1) (option_map (module_type f) x2)
    | MeXtr loc x1 x2 →
        f.meXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and str_item f =
  self where rec self =
    fun
    [ StCls loc x1 →
        f.stCls (f.mloc loc)
          (vala_map (List.map (class_infos_map f.mloc (class_expr f))) x1)
    | StClt loc x1 →
        f.stClt (f.mloc loc)
          (vala_map (List.map (class_infos_map f.mloc (class_type f))) x1)
    | StDcl loc x1 → f.stDcl (f.mloc loc) (vala_map (List.map self) x1)
    | StDir loc x1 x2 →
        f.stDir (f.mloc loc) x1 (vala_map (option_map (expr f)) x2)
    | StExc loc x1 x2 x3 →
        f.stExc (f.mloc loc) x1 (vala_map (List.map (ctyp f)) x2) x3
    | StExp loc x1 → f.stExp (f.mloc loc) (expr f x1)
    | StExt loc x1 x2 x3 → f.stExt (f.mloc loc) x1 (ctyp f x2) x3
    | StInc loc x1 → f.stInc (f.mloc loc) (module_expr f x1)
    | StMod loc x1 x2 →
        f.stMod (f.mloc loc) x1
          (vala_map (List.map (fun (x1, x2) → (x1, module_expr f x2))) x2)
    | StMty loc x1 x2 → f.stMty (f.mloc loc) x1 (module_type f x2)
    | StOpn loc x1 → f.stOpn (f.mloc loc) x1
    | StTyp loc x1 →
        f.stTyp (f.mloc loc) (vala_map (List.map (type_decl f)) x1)
    | StUse loc x1 x2 →
        f.stUse (f.mloc loc) x1
          (vala_map (List.map (fun (x1, loc) → (self x1, f.mloc loc))) x2)
    | StVal loc x1 x2 →
        f.stVal (f.mloc loc) x1
          (vala_map (List.map (fun (x1, x2) → (patt f x1, expr f x2))) x2)
    | StXtr loc x1 x2 →
        f.stXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and type_decl f x =
  {tdNam = vala_map (fun (loc, x1) → (f.mloc loc, x1)) x.tdNam;
   tdPrm = x.tdPrm; tdPrv = x.tdPrv; tdDef = ctyp f x.tdDef;
   tdCon =
     vala_map (List.map (fun (x1, x2) → (ctyp f x1, ctyp f x2))) x.tdCon}
and class_type f =
  self where rec self =
    fun
    [ CtAcc loc x1 x2 → f.ctAcc (f.mloc loc) (self x1) (self x2)
    | CtApp loc x1 x2 → f.ctApp (f.mloc loc) (self x1) (self x2)
    | CtCon loc x1 x2 →
        f.ctCon (f.mloc loc) (self x1) (vala_map (List.map (ctyp f)) x2)
    | CtFun loc x1 x2 → f.ctFun (f.mloc loc) (ctyp f x1) (self x2)
    | CtIde loc x1 → f.ctIde (f.mloc loc) x1
    | CtSig loc x1 x2 →
        f.ctSig (f.mloc loc) (vala_map (option_map (ctyp f)) x1)
          (vala_map (List.map (class_sig_item f)) x2)
    | CtXtr loc x1 x2 →
        f.ctXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and class_sig_item f =
  self where rec self =
    fun
    [ CgCtr loc x1 x2 → f.cgCtr (f.mloc loc) (ctyp f x1) (ctyp f x2)
    | CgDcl loc x1 → f.cgDcl (f.mloc loc) (vala_map (List.map self) x1)
    | CgInh loc x1 → f.cgInh (f.mloc loc) (class_type f x1)
    | CgMth loc x1 x2 x3 → f.cgMth (f.mloc loc) x1 x2 (ctyp f x3)
    | CgVal loc x1 x2 x3 → f.cgVal (f.mloc loc) x1 x2 (ctyp f x3)
    | CgVir loc x1 x2 x3 → f.cgVir (f.mloc loc) x1 x2 (ctyp f x3) ]
and class_expr f =
  self where rec self =
    fun
    [ CeApp loc x1 x2 → f.ceApp (f.mloc loc) (self x1) (expr f x2)
    | CeCon loc x1 x2 →
        f.ceCon (f.mloc loc) x1 (vala_map (List.map (ctyp f)) x2)
    | CeFun loc x1 x2 → f.ceFun (f.mloc loc) (patt f x1) (self x2)
    | CeLet loc x1 x2 x3 →
        f.ceLet (f.mloc loc) x1
          (vala_map (List.map (fun (x1, x2) → (patt f x1, expr f x2))) x2)
          (self x3)
    | CeStr loc x1 x2 →
        f.ceStr (f.mloc loc) (vala_map (option_map (patt f)) x1)
          (vala_map (List.map (class_str_item f)) x2)
    | CeTyc loc x1 x2 → f.ceTyc (f.mloc loc) (self x1) (class_type f x2)
    | CeXtr loc x1 x2 →
        f.ceXtr (f.mloc loc) x1 (option_map (vala_map self) x2) ]
and class_str_item f =
  self where rec self =
    fun
    [ CrCtr loc x1 x2 → f.crCtr (f.mloc loc) (ctyp f x1) (ctyp f x2)
    | CrDcl loc x1 → f.crDcl (f.mloc loc) (vala_map (List.map self) x1)
    | CrInh loc x1 x2 → f.crInh (f.mloc loc) (class_expr f x1) x2
    | CrIni loc x1 → f.crIni (f.mloc loc) (expr f x1)
    | CrMth loc x1 x2 x3 x4 x5 →
        f.crMth (f.mloc loc) x1 x2 x3 (vala_map (option_map (ctyp f)) x4)
          (expr f x5)
    | CrVal loc x1 x2 x3 x4 → f.crVal (f.mloc loc) x1 x2 x3 (expr f x4)
    | CrVav loc x1 x2 x3 → f.crVav (f.mloc loc) x1 x2 (ctyp f x3)
    | CrVir loc x1 x2 x3 → f.crVir (f.mloc loc) x1 x2 (ctyp f x3) ]
;

