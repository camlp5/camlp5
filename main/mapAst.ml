(* camlp5r *)
(* $Id: mapAst.ml,v 6.2 2011/02/16 19:21:53 deraugla Exp $ *)

#load "pa_macro.cmo";

open MLast;

value vala_map f =
  IFNDEF STRICT THEN
    fun x -> f x
  ELSE
    fun
    [ Ploc.VaAnt s -> Ploc.VaAnt s
    | Ploc.VaVal x -> Ploc.VaVal (f x) ]
  END
;

type map =
  { tyAcc : loc → ctyp → ctyp → ctyp;
    tyAli : loc → ctyp → ctyp → ctyp;
    tyAny : loc → ctyp;
    tyApp : loc → ctyp → ctyp → ctyp;
    tyArr : loc → ctyp → ctyp → ctyp;
    tyCls : loc → Ploc.vala (list string) → ctyp;
    tyLab : loc → Ploc.vala string → ctyp → ctyp;
    tyLid : loc → Ploc.vala string → ctyp;
    tyMan : loc → ctyp → Ploc.vala bool → ctyp → ctyp;
    tyObj :
      loc → Ploc.vala (list (string * ctyp)) → Ploc.vala bool → ctyp;
    tyOlb : loc → Ploc.vala string → ctyp → ctyp;
    tyPck : loc → module_type → ctyp;
    tyPol : loc → Ploc.vala (list string) → ctyp → ctyp;
    tyPot : loc → Ploc.vala (list string) → ctyp → ctyp;
    tyQuo : loc → Ploc.vala string → ctyp;
    tyRec : loc → Ploc.vala (list (loc * string * bool * ctyp)) → ctyp;
    tySum :
      loc →
        Ploc.vala
          (list
             (loc * Ploc.vala string * Ploc.vala (list ctyp) *
              option ctyp)) →
        ctyp;
    tyTup : loc → Ploc.vala (list ctyp) → ctyp;
    tyUid : loc → Ploc.vala string → ctyp;
    tyVrn :
      loc → Ploc.vala (list poly_variant) →
        option (option (Ploc.vala (list string))) → ctyp;
    tyXtr : loc → string → option (Ploc.vala ctyp) → ctyp;
    pvTag :
      loc → Ploc.vala string → Ploc.vala bool →
        Ploc.vala (list ctyp) → poly_variant;
    pvInh : loc → ctyp → poly_variant;
    paAcc : loc → patt → patt → patt;
    paAli : loc → patt → patt → patt;
    paAnt : loc → patt → patt;
    paAny : loc → patt;
    paApp : loc → patt → patt → patt;
    paArr : loc → Ploc.vala (list patt) → patt;
    paChr : loc → Ploc.vala string → patt;
    paFlo : loc → Ploc.vala string → patt;
    paInt : loc → Ploc.vala string → string → patt;
    paLab :
      loc → Ploc.vala (list (patt * Ploc.vala (option patt))) → patt;
    paLaz : loc → patt → patt;
    paLid : loc → Ploc.vala string → patt;
    paNty : loc → Ploc.vala string → patt;
    paOlb : loc → patt → Ploc.vala (option expr) → patt;
    paOrp : loc → patt → patt → patt;
    paRec : loc → Ploc.vala (list (patt * patt)) → patt;
    paRng : loc → patt → patt → patt;
    paStr : loc → Ploc.vala string → patt;
    paTup : loc → Ploc.vala (list patt) → patt;
    paTyc : loc → patt → ctyp → patt;
    paTyp : loc → Ploc.vala (list string) → patt;
    paUid : loc → Ploc.vala string → patt;
    paUnp : loc → Ploc.vala string → option module_type → patt;
    paVrn : loc → Ploc.vala string → patt;
    paXtr : loc → string → option (Ploc.vala patt) → patt;
    exAcc : loc → expr → expr → expr;
    exAnt : loc → expr → expr;
    exApp : loc → expr → expr → expr;
    exAre : loc → expr → expr → expr;
    exArr : loc → Ploc.vala (list expr) → expr;
    exAsr : loc → expr → expr;
    exAss : loc → expr → expr → expr;
    exBae : loc → expr → Ploc.vala (list expr) → expr;
    exChr : loc → Ploc.vala string → expr;
    exCoe : loc → expr → option ctyp → ctyp → expr;
    exFlo : loc → Ploc.vala string → expr;
    exFor :
      loc → Ploc.vala string → expr → expr → Ploc.vala bool →
        Ploc.vala (list expr) → expr;
    exFun :
      loc → Ploc.vala (list (patt * Ploc.vala (option expr) * expr)) →
        expr;
    exIfe : loc → expr → expr → expr → expr;
    exInt : loc → Ploc.vala string → string → expr;
    exLab :
      loc → Ploc.vala (list (patt * Ploc.vala (option expr))) → expr;
    exLaz : loc → expr → expr;
    exLet :
      loc → Ploc.vala bool → Ploc.vala (list (patt * expr)) → expr →
        expr;
    exLid : loc → Ploc.vala string → expr;
    exLmd : loc → Ploc.vala string → module_expr → expr → expr;
    exMat :
      loc → expr →
        Ploc.vala (list (patt * Ploc.vala (option expr) * expr)) → expr;
    exNew : loc → Ploc.vala (list string) → expr;
    exObj :
      loc → Ploc.vala (option patt) → Ploc.vala (list class_str_item) →
        expr;
    exOlb : loc → patt → Ploc.vala (option expr) → expr;
    exOvr : loc → Ploc.vala (list (string * expr)) → expr;
    exPck : loc → module_expr → option module_type → expr;
    exRec : loc → Ploc.vala (list (patt * expr)) → option expr → expr;
    exSeq : loc → Ploc.vala (list expr) → expr;
    exSnd : loc → expr → Ploc.vala string → expr;
    exSte : loc → expr → expr → expr;
    exStr : loc → Ploc.vala string → expr;
    exTry :
      loc → expr →
        Ploc.vala (list (patt * Ploc.vala (option expr) * expr)) → expr;
    exTup : loc → Ploc.vala (list expr) → expr;
    exTyc : loc → expr → ctyp → expr;
    exUid : loc → Ploc.vala string → expr;
    exVrn : loc → Ploc.vala string → expr;
    exWhi : loc → expr → Ploc.vala (list expr) → expr;
    exXtr : loc → string → option (Ploc.vala expr) → expr;
    mtAcc : loc → module_type → module_type → module_type;
    mtApp : loc → module_type → module_type → module_type;
    mtFun :
      loc → Ploc.vala string → module_type → module_type →
        module_type;
    mtLid : loc → Ploc.vala string → module_type;
    mtQuo : loc → Ploc.vala string → module_type;
    mtSig : loc → Ploc.vala (list sig_item) → module_type;
    mtTyo : loc → module_expr → module_type;
    mtUid : loc → Ploc.vala string → module_type;
    mtWit :
      loc → module_type → Ploc.vala (list with_constr) → module_type;
    mtXtr : loc → string → option (Ploc.vala module_type) → module_type;
    sgCls : loc → Ploc.vala (list (class_infos class_type)) → sig_item;
    sgClt : loc → Ploc.vala (list (class_infos class_type)) → sig_item;
    sgDcl : loc → Ploc.vala (list sig_item) → sig_item;
    sgDir : loc → Ploc.vala string → Ploc.vala (option expr) → sig_item;
    sgExc : loc → Ploc.vala string → Ploc.vala (list ctyp) → sig_item;
    sgExt :
      loc → Ploc.vala string → ctyp → Ploc.vala (list string) →
        sig_item;
    sgInc : loc → module_type → sig_item;
    sgMod :
      loc → Ploc.vala bool →
        Ploc.vala (list (Ploc.vala string * module_type)) → sig_item;
    sgMty : loc → Ploc.vala string → module_type → sig_item;
    sgOpn : loc → Ploc.vala (list string) → sig_item;
    sgTyp : loc → Ploc.vala (list type_decl) → sig_item;
    sgUse :
      loc → Ploc.vala string → Ploc.vala (list (sig_item * loc)) →
        sig_item;
    sgVal : loc → Ploc.vala string → ctyp → sig_item;
    sgXtr : loc → string → option (Ploc.vala sig_item) → sig_item;
    wcMod : loc → Ploc.vala (list string) → module_expr → with_constr;
    wcMos : loc → Ploc.vala (list string) → module_expr → with_constr;
    wcTyp :
      loc → Ploc.vala (list string) → Ploc.vala (list type_var) →
        Ploc.vala bool → ctyp → with_constr;
    wcTys :
      loc → Ploc.vala (list string) → Ploc.vala (list type_var) →
        ctyp → with_constr;
    meAcc : loc → module_expr → module_expr → module_expr;
    meApp : loc → module_expr → module_expr → module_expr;
    meFun :
      loc → Ploc.vala string → module_type → module_expr →
        module_expr;
    meStr : loc → Ploc.vala (list str_item) → module_expr;
    meTyc : loc → module_expr → module_type → module_expr;
    meUid : loc → Ploc.vala string → module_expr;
    meUnp : loc → expr → option module_type → module_expr;
    meXtr : loc → string → option (Ploc.vala module_expr) → module_expr;
    stCls : loc → Ploc.vala (list (class_infos class_expr)) → str_item;
    stClt : loc → Ploc.vala (list (class_infos class_type)) → str_item;
    stDcl : loc → Ploc.vala (list str_item) → str_item;
    stDir : loc → Ploc.vala string → Ploc.vala (option expr) → str_item;
    stExc :
      loc → Ploc.vala string → Ploc.vala (list ctyp) →
        Ploc.vala (list string) → str_item;
    stExp : loc → expr → str_item;
    stExt :
      loc → Ploc.vala string → ctyp → Ploc.vala (list string) →
        str_item;
    stInc : loc → module_expr → str_item;
    stMod :
      loc → Ploc.vala bool →
        Ploc.vala (list (Ploc.vala string * module_expr)) → str_item;
    stMty : loc → Ploc.vala string → module_type → str_item;
    stOpn : loc → Ploc.vala (list string) → str_item;
    stTyp : loc → Ploc.vala (list type_decl) → str_item;
    stUse :
      loc → Ploc.vala string → Ploc.vala (list (str_item * loc)) →
        str_item;
    stVal :
      loc → Ploc.vala bool → Ploc.vala (list (patt * expr)) → str_item;
    stXtr : loc → string → option (Ploc.vala str_item) → str_item;
    ctAcc : loc → class_type → class_type → class_type;
    ctApp : loc → class_type → class_type → class_type;
    ctCon : loc → class_type → Ploc.vala (list ctyp) → class_type;
    ctFun : loc → ctyp → class_type → class_type;
    ctIde : loc → Ploc.vala string → class_type;
    ctSig :
      loc → Ploc.vala (option ctyp) → Ploc.vala (list class_sig_item) →
        class_type;
    ctXtr : loc → string → option (Ploc.vala class_type) → class_type;
    cgCtr : loc → ctyp → ctyp → class_sig_item;
    cgDcl : loc → Ploc.vala (list class_sig_item) → class_sig_item;
    cgInh : loc → class_type → class_sig_item;
    cgMth :
      loc → Ploc.vala bool → Ploc.vala string → ctyp → class_sig_item;
    cgVal :
      loc → Ploc.vala bool → Ploc.vala string → ctyp → class_sig_item;
    cgVir :
      loc → Ploc.vala bool → Ploc.vala string → ctyp → class_sig_item;
    ceApp : loc → class_expr → expr → class_expr;
    ceCon :
      loc → Ploc.vala (list string) → Ploc.vala (list ctyp) →
        class_expr;
    ceFun : loc → patt → class_expr → class_expr;
    ceLet :
      loc → Ploc.vala bool → Ploc.vala (list (patt * expr)) →
        class_expr → class_expr;
    ceStr :
      loc → Ploc.vala (option patt) → Ploc.vala (list class_str_item) →
        class_expr;
    ceTyc : loc → class_expr → class_type → class_expr;
    ceXtr : loc → string → option (Ploc.vala class_expr) → class_expr;
    crCtr : loc → ctyp → ctyp → class_str_item;
    crDcl : loc → Ploc.vala (list class_str_item) → class_str_item;
    crInh :
      loc → class_expr → Ploc.vala (option string) → class_str_item;
    crIni : loc → expr → class_str_item;
    crMth :
      loc → Ploc.vala bool → Ploc.vala bool → Ploc.vala string →
        Ploc.vala (option ctyp) → expr → class_str_item;
    crVal :
      loc → Ploc.vala bool → Ploc.vala bool → Ploc.vala string →
        expr → class_str_item;
    crVav :
      loc → Ploc.vala bool → Ploc.vala string → ctyp → class_str_item;
    crVir :
      loc → Ploc.vala bool → Ploc.vala string → ctyp →
        class_str_item }
;

value def =
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
   crVir loc x1 x2 x3 = CrVir loc x1 x2 x3}
;

value rec ctyp f =
  self where rec self =
    fun
    [ TyAcc loc x1 x2 -> f.tyAcc loc (self x1) (self x2)
    | TyAli loc x1 x2 -> f.tyAli loc (self x1) (self x2)
    | TyAny loc -> f.tyAny loc
    | TyApp loc x1 x2 -> f.tyApp loc (self x1) (self x2)
    | TyArr loc x1 x2 -> f.tyArr loc (self x1) (self x2)
    | TyCls loc x1 -> f.tyCls loc x1
    | TyLab loc x1 x2 -> f.tyLab loc x1 (self x2)
    | TyLid loc x1 -> f.tyLid loc x1
    | TyMan loc x1 x2 x3 -> f.tyMan loc (self x1) x2 (self x3)
    | TyObj loc x1 x2 ->
        f.tyObj loc (vala_map (List.map (fun (x1, x2) -> (x1, self x2))) x1)
          x2
    | TyOlb loc x1 x2 -> f.tyOlb loc x1 (self x2)
    | TyPck loc x1 -> f.tyPck loc (module_type f x1)
    | TyPol loc x1 x2 -> f.tyPol loc x1 (self x2)
    | TyPot loc x1 x2 -> f.tyPot loc x1 (self x2)
    | TyQuo loc x1 -> f.tyQuo loc x1
    | TyRec loc x1 ->
        f.tyRec loc
          (vala_map
             (List.map (fun (loc, x1, x2, x3) -> (floc loc, x1, x2, self x3)))
             x1)
    | TySum loc x1 ->
        f.tySum loc
          (vala_map
             (List.map
                (fun (loc, x1, x2, x3) ->
                   (floc loc, x1, vala_map (List.map self) x2,
                    option_map self x3)))
             x1)
    | TyTup loc x1 -> f.tyTup loc (vala_map (List.map self) x1)
    | TyUid loc x1 -> f.tyUid loc x1
    | TyVrn loc x1 x2 ->
        f.tyVrn loc (vala_map (List.map (poly_variant f)) x1) x2
    | TyXtr loc x1 x2 -> f.tyXtr loc x1 (option_map (vala_map self) x2) ]
          and poly_variant f =
          fun
  [ PvTag loc x1 x2 x3 -> f.pvTag loc x1 x2 (vala_map (List.map (ctyp f)) x3)
  | PvInh loc x1 -> f.pvInh loc (ctyp f x1) ]
and patt f =
  self where rec self =
    fun
    [ PaAcc loc x1 x2 -> f.paAcc loc (self x1) (self x2)
    | PaAli loc x1 x2 -> f.paAli loc (self x1) (self x2)
    | PaAnt loc x1 ->
        let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
        patt new_floc sh x1
    | PaAny loc -> f.paAny loc
    | PaApp loc x1 x2 -> f.paApp loc (self x1) (self x2)
    | PaArr loc x1 -> f.paArr loc (vala_map (List.map self) x1)
    | PaChr loc x1 -> f.paChr loc x1
    | PaFlo loc x1 -> f.paFlo loc x1
    | PaInt loc x1 x2 -> f.paInt loc x1 x2
    | PaLab loc x1 ->
        f.paLab loc
          (vala_map
             (List.map
                (fun (x1, x2) -> (self x1, vala_map (option_map self) x2)))
             x1)
    | PaLaz loc x1 -> f.paLaz loc (self x1)
    | PaLid loc x1 -> f.paLid loc x1
    | PaNty loc x1 -> f.paNty loc x1
    | PaOlb loc x1 x2 ->
        f.paOlb loc (self x1) (vala_map (option_map (expr f)) x2)
    | PaOrp loc x1 x2 -> f.paOrp loc (self x1) (self x2)
    | PaRec loc x1 ->
        f.paRec loc
          (vala_map (List.map (fun (x1, x2) -> (self x1, self x2))) x1)
    | PaRng loc x1 x2 -> f.paRng loc (self x1) (self x2)
    | PaStr loc x1 -> f.paStr loc x1
    | PaTup loc x1 -> f.paTup loc (vala_map (List.map self) x1)
    | PaTyc loc x1 x2 -> f.paTyc loc (self x1) (ctyp f x2)
    | PaTyp loc x1 -> f.paTyp loc x1
    | PaUid loc x1 -> f.paUid loc x1
    | PaUnp loc x1 x2 -> f.paUnp loc x1 (option_map (module_type f) x2)
    | PaVrn loc x1 -> f.paVrn loc x1
    | PaXtr loc x1 x2 -> f.paXtr loc x1 (option_map (vala_map self) x2) ]
          and expr f =
          self where rec self =
    fun
    [ ExAcc loc x1 x2 -> f.exAcc loc (self x1) (self x2)
    | ExAnt loc x1 ->
        let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
        expr new_floc sh x1
    | ExApp loc x1 x2 -> f.exApp loc (self x1) (self x2)
    | ExAre loc x1 x2 -> f.exAre loc (self x1) (self x2)
    | ExArr loc x1 -> f.exArr loc (vala_map (List.map self) x1)
    | ExAsr loc x1 -> f.exAsr loc (self x1)
    | ExAss loc x1 x2 -> f.exAss loc (self x1) (self x2)
    | ExBae loc x1 x2 -> f.exBae loc (self x1) (vala_map (List.map self) x2)
    | ExChr loc x1 -> f.exChr loc x1
    | ExCoe loc x1 x2 x3 ->
        f.exCoe loc (self x1) (option_map (ctyp f) x2) (ctyp f x3)
    | ExFlo loc x1 -> f.exFlo loc x1
    | ExFor loc x1 x2 x3 x4 x5 ->
        f.exFor loc x1 (self x2) (self x3) x4 (vala_map (List.map self) x5)
    | ExFun loc x1 ->
        f.exFun loc
          (vala_map
             (List.map
                (fun (x1, x2, x3) ->
                   (patt f x1, vala_map (option_map self) x2, self x3)))
             x1)
    | ExIfe loc x1 x2 x3 -> f.exIfe loc (self x1) (self x2) (self x3)
    | ExInt loc x1 x2 -> f.exInt loc x1 x2
    | ExLab loc x1 ->
        f.exLab loc
          (vala_map
             (List.map
                (fun (x1, x2) -> (patt f x1, vala_map (option_map self) x2)))
             x1)
    | ExLaz loc x1 -> f.exLaz loc (self x1)
    | ExLet loc x1 x2 x3 ->
        f.exLet loc x1
          (vala_map (List.map (fun (x1, x2) -> (patt f x1, self x2))) x2)
          (self x3)
    | ExLid loc x1 -> f.exLid loc x1
    | ExLmd loc x1 x2 x3 -> f.exLmd loc x1 (module_expr f x2) (self x3)
    | ExMat loc x1 x2 ->
        f.exMat loc (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) ->
                   (patt f x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExNew loc x1 -> f.exNew loc x1
    | ExObj loc x1 x2 ->
        f.exObj loc (vala_map (option_map (patt f)) x1)
          (vala_map (List.map (class_str_item f)) x2)
    | ExOlb loc x1 x2 ->
        f.exOlb loc (patt f x1) (vala_map (option_map self) x2)
    | ExOvr loc x1 ->
        f.exOvr loc (vala_map (List.map (fun (x1, x2) -> (x1, self x2))) x1)
    | ExPck loc x1 x2 ->
        f.exPck loc (module_expr f x1) (option_map (module_type f) x2)
    | ExRec loc x1 x2 ->
        f.exRec loc
          (vala_map (List.map (fun (x1, x2) -> (patt f x1, self x2))) x1)
          (option_map self x2)
    | ExSeq loc x1 -> f.exSeq loc (vala_map (List.map self) x1)
    | ExSnd loc x1 x2 -> f.exSnd loc (self x1) x2
    | ExSte loc x1 x2 -> f.exSte loc (self x1) (self x2)
    | ExStr loc x1 -> f.exStr loc x1
    | ExTry loc x1 x2 ->
        f.exTry loc (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) ->
                   (patt f x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExTup loc x1 -> f.exTup loc (vala_map (List.map self) x1)
    | ExTyc loc x1 x2 -> f.exTyc loc (self x1) (ctyp f x2)
    | ExUid loc x1 -> f.exUid loc x1
    | ExVrn loc x1 -> f.exVrn loc x1
    | ExWhi loc x1 x2 -> f.exWhi loc (self x1) (vala_map (List.map self) x2)
    | ExXtr loc x1 x2 -> f.exXtr loc x1 (option_map (vala_map self) x2) ]
          and module_type f =
          self where rec self =
    fun
    [ MtAcc loc x1 x2 -> f.mtAcc loc (self x1) (self x2)
    | MtApp loc x1 x2 -> f.mtApp loc (self x1) (self x2)
    | MtFun loc x1 x2 x3 -> f.mtFun loc x1 (self x2) (self x3)
    | MtLid loc x1 -> f.mtLid loc x1
    | MtQuo loc x1 -> f.mtQuo loc x1
    | MtSig loc x1 -> f.mtSig loc (vala_map (List.map (sig_item f)) x1)
    | MtTyo loc x1 -> f.mtTyo loc (module_expr f x1)
    | MtUid loc x1 -> f.mtUid loc x1
    | MtWit loc x1 x2 ->
        f.mtWit loc (self x1) (vala_map (List.map (with_constr f)) x2)
    | MtXtr loc x1 x2 -> f.mtXtr loc x1 (option_map (vala_map self) x2) ]
          and sig_item f =
          self where rec self =
    fun
    [ SgCls loc x1 ->
        f.sgCls loc
          (vala_map (List.map (class_infos_map floc (class_type f))) x1)
    | SgClt loc x1 ->
        f.sgClt loc
          (vala_map (List.map (class_infos_map floc (class_type f))) x1)
    | SgDcl loc x1 -> f.sgDcl loc (vala_map (List.map self) x1)
    | SgDir loc x1 x2 -> f.sgDir loc x1 (vala_map (option_map (expr f)) x2)
    | SgExc loc x1 x2 -> f.sgExc loc x1 (vala_map (List.map (ctyp f)) x2)
    | SgExt loc x1 x2 x3 -> f.sgExt loc x1 (ctyp f x2) x3
    | SgInc loc x1 -> f.sgInc loc (module_type f x1)
    | SgMod loc x1 x2 ->
        f.sgMod loc x1
          (vala_map (List.map (fun (x1, x2) -> (x1, module_type f x2))) x2)
    | SgMty loc x1 x2 -> f.sgMty loc x1 (module_type f x2)
    | SgOpn loc x1 -> f.sgOpn loc x1
    | SgTyp loc x1 -> f.sgTyp loc (vala_map (List.map (type_decl f)) x1)
    | SgUse loc x1 x2 ->
        f.sgUse loc x1
          (vala_map (List.map (fun (x1, loc) -> (self x1, floc loc))) x2)
    | SgVal loc x1 x2 -> f.sgVal loc x1 (ctyp f x2)
    | SgXtr loc x1 x2 -> f.sgXtr loc x1 (option_map (vala_map self) x2) ]
          and with_constr f =
          fun
  [ WcMod loc x1 x2 -> f.wcMod loc x1 (module_expr f x2)
  | WcMos loc x1 x2 -> f.wcMos loc x1 (module_expr f x2)
  | WcTyp loc x1 x2 x3 x4 -> f.wcTyp loc x1 x2 x3 (ctyp f x4)
  | WcTys loc x1 x2 x3 -> f.wcTys loc x1 x2 (ctyp f x3) ]
and module_expr f =
  self where rec self =
    fun
    [ MeAcc loc x1 x2 -> f.meAcc loc (self x1) (self x2)
    | MeApp loc x1 x2 -> f.meApp loc (self x1) (self x2)
    | MeFun loc x1 x2 x3 -> f.meFun loc x1 (module_type f x2) (self x3)
    | MeStr loc x1 -> f.meStr loc (vala_map (List.map (str_item f)) x1)
    | MeTyc loc x1 x2 -> f.meTyc loc (self x1) (module_type f x2)
    | MeUid loc x1 -> f.meUid loc x1
    | MeUnp loc x1 x2 ->
        f.meUnp loc (expr f x1) (option_map (module_type f) x2)
    | MeXtr loc x1 x2 -> f.meXtr loc x1 (option_map (vala_map self) x2) ]
          and str_item f =
          self where rec self =
    fun
    [ StCls loc x1 ->
        f.stCls loc
          (vala_map (List.map (class_infos_map floc (class_expr f))) x1)
    | StClt loc x1 ->
        f.stClt loc
          (vala_map (List.map (class_infos_map floc (class_type f))) x1)
    | StDcl loc x1 -> f.stDcl loc (vala_map (List.map self) x1)
    | StDir loc x1 x2 -> f.stDir loc x1 (vala_map (option_map (expr f)) x2)
    | StExc loc x1 x2 x3 ->
        f.stExc loc x1 (vala_map (List.map (ctyp f)) x2) x3
    | StExp loc x1 -> f.stExp loc (expr f x1)
    | StExt loc x1 x2 x3 -> f.stExt loc x1 (ctyp f x2) x3
    | StInc loc x1 -> f.stInc loc (module_expr f x1)
    | StMod loc x1 x2 ->
        f.stMod loc x1
          (vala_map (List.map (fun (x1, x2) -> (x1, module_expr f x2))) x2)
    | StMty loc x1 x2 -> f.stMty loc x1 (module_type f x2)
    | StOpn loc x1 -> f.stOpn loc x1
    | StTyp loc x1 -> f.stTyp loc (vala_map (List.map (type_decl f)) x1)
    | StUse loc x1 x2 ->
        f.stUse loc x1
          (vala_map (List.map (fun (x1, loc) -> (self x1, floc loc))) x2)
    | StVal loc x1 x2 ->
        f.stVal loc x1
          (vala_map (List.map (fun (x1, x2) -> (patt f x1, expr f x2))) x2)
    | StXtr loc x1 x2 -> f.stXtr loc x1 (option_map (vala_map self) x2) ]
          and type_decl f x =
          {tdNam = vala_map (fun (loc, x1) -> (floc loc, x1)) x.tdNam;
   tdPrm = x.tdPrm; tdPrv = x.tdPrv; tdDef = ctyp f x.tdDef;
   tdCon =
     vala_map (List.map (fun (x1, x2) -> (ctyp f x1, ctyp f x2))) x.tdCon}
and class_type f =
  self where rec self =
    fun
    [ CtAcc loc x1 x2 -> f.ctAcc loc (self x1) (self x2)
    | CtApp loc x1 x2 -> f.ctApp loc (self x1) (self x2)
    | CtCon loc x1 x2 ->
        f.ctCon loc (self x1) (vala_map (List.map (ctyp f)) x2)
    | CtFun loc x1 x2 -> f.ctFun loc (ctyp f x1) (self x2)
    | CtIde loc x1 -> f.ctIde loc x1
    | CtSig loc x1 x2 ->
        f.ctSig loc (vala_map (option_map (ctyp f)) x1)
          (vala_map (List.map (class_sig_item f)) x2)
    | CtXtr loc x1 x2 -> f.ctXtr loc x1 (option_map (vala_map self) x2) ]
          and class_sig_item f =
          self where rec self =
    fun
    [ CgCtr loc x1 x2 -> f.cgCtr loc (ctyp f x1) (ctyp f x2)
    | CgDcl loc x1 -> f.cgDcl loc (vala_map (List.map self) x1)
    | CgInh loc x1 -> f.cgInh loc (class_type f x1)
    | CgMth loc x1 x2 x3 -> f.cgMth loc x1 x2 (ctyp f x3)
    | CgVal loc x1 x2 x3 -> f.cgVal loc x1 x2 (ctyp f x3)
    | CgVir loc x1 x2 x3 -> f.cgVir loc x1 x2 (ctyp f x3) ]
and class_expr f =
  self where rec self =
    fun
    [ CeApp loc x1 x2 -> f.ceApp loc (self x1) (expr f x2)
    | CeCon loc x1 x2 -> f.ceCon loc x1 (vala_map (List.map (ctyp f)) x2)
    | CeFun loc x1 x2 -> f.ceFun loc (patt f x1) (self x2)
    | CeLet loc x1 x2 x3 ->
        f.ceLet loc x1
          (vala_map (List.map (fun (x1, x2) -> (patt f x1, expr f x2))) x2)
          (self x3)
    | CeStr loc x1 x2 ->
        f.ceStr loc (vala_map (option_map (patt f)) x1)
          (vala_map (List.map (class_str_item f)) x2)
    | CeTyc loc x1 x2 -> f.ceTyc loc (self x1) (class_type f x2)
    | CeXtr loc x1 x2 -> f.ceXtr loc x1 (option_map (vala_map self) x2) ]
          and class_str_item f =
          self where rec self =
    fun
    [ CrCtr loc x1 x2 -> f.crCtr loc (ctyp f x1) (ctyp f x2)
    | CrDcl loc x1 -> f.crDcl loc (vala_map (List.map self) x1)
    | CrInh loc x1 x2 -> f.crInh loc (class_expr f x1) x2
    | CrIni loc x1 -> f.crIni loc (expr f x1)
    | CrMth loc x1 x2 x3 x4 x5 ->
        f.crMth loc x1 x2 x3 (vala_map (option_map (ctyp f)) x4) (expr f x5)
    | CrVal loc x1 x2 x3 x4 -> f.crVal loc x1 x2 x3 (expr f x4)
    | CrVav loc x1 x2 x3 -> f.crVav loc x1 x2 (ctyp f x3)
    | CrVir loc x1 x2 x3 -> f.crVir loc x1 x2 (ctyp f x3) ]
;

