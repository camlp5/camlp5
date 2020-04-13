(* camlp5r *)
(* pa_passthru.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";
#load "pa_extfun.cmo";

open Asttools;
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

value class_infos_map arg ~{attributes} f x =
  {ciLoc = x.ciLoc; ciVir = x.ciVir;
   ciPrm =
     let (x1, x2) = x.ciPrm in
     (x1, x2);
   ciNam = x.ciNam; ciExp = f x.ciExp; ciAttributes = attributes arg x.ciAttributes }
;

module rec EF : sig
  type extension_point 'a = Extfun.t 'a (Ctxt.t -> 'a) ;
  type t = {
    ctyp : extension_point ctyp ;
    generic_constructor : extension_point generic_constructor ;
    patt : extension_point patt ;
    expr : extension_point expr ;
    module_type : extension_point module_type ;
    sig_item : extension_point sig_item ;
    with_constr : extension_point with_constr ;
    longid : extension_point longid ;
    module_expr : extension_point module_expr ;
    str_item : extension_point str_item ;
    type_decl : extension_point type_decl ;
    type_extension : extension_point type_extension ;
    extension_constructor : extension_point extension_constructor ;
    class_type : extension_point class_type ;
    class_sig_item : extension_point class_sig_item ;
    class_expr : extension_point class_expr ;
    class_str_item : extension_point class_str_item ;
    attribute_body : extension_point attribute_body 
  } ;
  value mk : unit -> t ;
end = struct
  type extension_point 'a = Extfun.t 'a (Ctxt.t -> 'a) ;
  type t = {
    ctyp : extension_point ctyp ;
    generic_constructor : extension_point generic_constructor ;
    patt : extension_point patt ;
    expr : extension_point expr ;
    module_type : extension_point module_type ;
    sig_item : extension_point sig_item ;
    with_constr : extension_point with_constr ;
    longid : extension_point longid ;
    module_expr : extension_point module_expr ;
    str_item : extension_point str_item ;
    type_decl : extension_point type_decl ;
    type_extension : extension_point type_extension ;
    extension_constructor : extension_point extension_constructor ;
    class_type : extension_point class_type ;
    class_sig_item : extension_point class_sig_item ;
    class_expr : extension_point class_expr ;
    class_str_item : extension_point class_str_item ;
    attribute_body : extension_point attribute_body 
  } ;
  value mk () = {
    ctyp = Extfun.empty ;
    generic_constructor = Extfun.empty ;
    patt = Extfun.empty ;
    expr = Extfun.empty ;
    module_type = Extfun.empty ;
    sig_item = Extfun.empty ;
    with_constr = Extfun.empty ;
    longid = Extfun.empty ;
    module_expr = Extfun.empty ;
    str_item = Extfun.empty ;
    type_decl = Extfun.empty ;
    type_extension = Extfun.empty ;
    extension_constructor = Extfun.empty ;
    class_type = Extfun.empty ;
    class_sig_item = Extfun.empty ;
    class_expr = Extfun.empty ;
    class_str_item = Extfun.empty ;
    attribute_body = Extfun.empty 
  } ;
end

and Ctxt : sig
  type t = {
    module_path : string; 
    with_path : bool ;
    options : list (string * expr) ;
    ef : EF.t } ;
  value mk : EF.t -> Ploc.t -> t ;
  value append_module : t -> string -> t ;
  value set_module_path : t -> string -> t ;
  value add_options : t -> list (string * expr) -> t ;
  value option : t -> string -> expr ;
end = struct
  type t = {
    module_path : string;
    with_path : bool ;
    options : list (string * expr) ;
    ef : EF.t } ;
value mk ef loc =
  let fname = Ploc.file_name loc in
  let path = String.split_on_char '/' fname in
  let (last, _) = Asttools.sep_last path in
  let base = match String.split_on_char '.' last with [
    [base :: _] -> base | _ -> assert False ] in
  let modname = String.capitalize_ascii base in
  { module_path = modname ; with_path = True ; options = [] ; ef = ef  }
;
value append_module ctxt s =
  { (ctxt) with module_path = Printf.sprintf "%s.%s" ctxt.module_path s }
;
value set_module_path ctxt s =
  { (ctxt) with module_path = s } ;

value add_options ctxt l = { (ctxt) with options = l @ ctxt.options } ;

value option ctxt name =
  match List.assoc name ctxt.options with [
    e -> e
  | exception Not_found ->
    failwith (Printf.sprintf "Pa_deriving_show.Ctxt.option: option %s not found" name)
  ]
;
end ;

value ef = ref (EF.mk ()) ;

value rec ctyp (arg : Ctxt.t)  x =
  match Extfun.apply arg.Ctxt.ef.EF.ctyp x arg with [
    x -> x
  | exception Extfun.Failure -> ctyp0 arg x
  ]
and ctyp0 arg =
  let rec self x = ctyp arg x
  and self0 =
    fun
    [ TyAtt loc ct attr ->
       TyAtt loc (self ct) (attribute_body arg attr)
    | TyAcc loc x1 x2 ->
        TyAcc loc (longid arg x1) x2
    | TyAli loc x1 x2 →
        TyAli loc (self x1) (self x2)
    | TyAny loc →
        TyAny loc
    | TyApp loc x1 x2 →
        TyApp loc (self x1) (self x2)
    | TyArr loc x1 x2 →
        TyArr loc (self x1) (self x2)
    | TyCls loc x1 →
        TyCls loc (vala_map (longid_lident arg) x1)
    | TyLab loc x1 x2 →
        TyLab loc x1 (self x2)
    | TyLid loc x1 →
        TyLid loc x1
    | TyMan loc x1 x2 x3 →
        TyMan loc (self x1) x2 (self x3)
    | TyObj loc x1 x2 →
        TyObj loc (vala_map (List.map (fun (x1, x2, x3) → (x1, self x2, attributes arg x3))) x1) x2
    | TyOlb loc x1 x2 →
        TyOlb loc x1 (self x2)
    | TyOpn loc ->
       TyOpn loc
    | TyPck loc x1 →
        TyPck loc (module_type arg x1)
    | TyPol loc x1 x2 →
        TyPol loc x1 (self x2)
    | TyPot loc x1 x2 →
        TyPot loc x1 (self x2)
    | TyQuo loc x1 →
        TyQuo loc x1
    | TyRec loc x1 →
        TyRec loc
          (vala_map
             (List.map (fun (loc, x1, x2, x3, x4) → (loc, x1, x2, self x3, attributes arg x4)))
             x1)
    | TySum loc x1 →
        TySum loc
          (vala_map
             (List.map
                (generic_constructor arg))
             x1)
    | TyTup loc x1 →
        TyTup loc (vala_map (List.map self) x1)
      | TyVrn loc x1 x2 →
        TyVrn loc (vala_map (List.map (poly_variant arg)) x1) x2
    | TyXtr loc x1 x2 →
        TyXtr loc x1 (option_map (vala_map self) x2)
    | TyExten loc exten ->
        TyExten loc (attribute_body arg exten)
    ] in
  self0

and generic_constructor arg x =
  match Extfun.apply arg.Ctxt.ef.EF.generic_constructor x arg with [
    x -> x
  | exception Extfun.Failure -> generic_constructor0 arg x
  ]
and generic_constructor0 arg = fun (loc, x1, x2, x3, x4) ->
    (loc, x1, vala_map (List.map (ctyp arg)) x2,
     option_map (ctyp arg) x3, attributes arg x4)
and poly_variant arg =
  fun
  [ PvTag loc x1 x2 x3 x4 →
      PvTag loc x1 x2 (vala_map (List.map (ctyp arg)) x3) (attributes arg x4)
  | PvInh loc x1 →
      PvInh loc (ctyp arg x1) ]
and patt arg x =
  match Extfun.apply arg.Ctxt.ef.EF.patt x arg with [
    x -> x
  | exception Extfun.Failure -> patt0 arg x
  ]
and patt0 arg =
  let rec self x = patt arg x
  and self0 =
    fun
    [ PaAtt loc p attr ->
       PaAtt loc (self p) (attribute_body arg attr)
    | PaPfx loc li p ->
       PaPfx loc (longid arg li) (self p)
    | PaLong loc li ->
       PaLong loc (longid arg li)
    | PaAli loc x1 x2 →
        PaAli loc (self x1) (self x2)
    | PaAnt loc x1 → assert False
    | PaAny loc →
        PaAny loc
    | PaApp loc x1 x2 →
        PaApp loc (self x1) (self x2)
    | PaArr loc x1 →
        PaArr loc (vala_map (List.map self) x1)
    | PaChr loc x1 →
        PaChr loc x1
    | PaExc loc x1 →
        PaExc loc (self x1)
    | PaFlo loc x1 →
        PaFlo loc x1
    | PaInt loc x1 x2 →
        PaInt loc x1 x2
    | PaLab loc x1 →
        PaLab loc
          (vala_map
             (List.map
                (fun (x1, x2) → (self x1, vala_map (option_map self) x2)))
             x1)
    | PaLaz loc x1 →
        PaLaz loc (self x1)
    | PaLid loc x1 →
        PaLid loc x1
    | PaNty loc x1 →
        PaNty loc x1
    | PaOlb loc x1 x2 →
        PaOlb loc (self x1) (vala_map (option_map (expr arg)) x2)
    | PaOrp loc x1 x2 →
        PaOrp loc (self x1) (self x2)
    | PaRec loc x1 →
        PaRec loc (vala_map (List.map (fun (x1, x2) → (self x1, self x2))) x1)
    | PaRng loc x1 x2 →
        PaRng loc (self x1) (self x2)
    | PaStr loc x1 →
        PaStr loc x1
    | PaTup loc x1 →
        PaTup loc (vala_map (List.map self) x1)
    | PaTyc loc x1 x2 →
        PaTyc loc (self x1) (ctyp arg x2)
    | PaTyp loc x1 →
        PaTyp loc (vala_map (longid_lident arg) x1)
    | PaUnp loc x1 x2 →
        PaUnp loc x1 (option_map (module_type arg) x2)
    | PaVrn loc x1 →
        PaVrn loc x1
    | PaXtr loc x1 x2 →
        PaXtr loc x1 (option_map (vala_map self) x2)
    | PaExten loc exten ->
        PaExten loc (attribute_body arg exten)
    ] in
  self0
and expr arg x =
  match Extfun.apply arg.Ctxt.ef.EF.expr x arg with [
    x -> x
  | exception Extfun.Failure -> expr0 arg x
  ]
and expr0 arg =
  let rec self x = expr arg x
  and self0 =
    fun
    [ ExAtt loc e attr ->
       ExAtt loc (self e) (attribute_body arg attr)
    | ExAcc loc x1 x2 →
        ExAcc loc (self x1) (self x2)
    | ExAnt loc x1 → assert False
    | ExApp loc x1 x2 →
        ExApp loc (self x1) (self x2)
    | ExAre loc x1 x2 x3 →
        ExAre loc x1 (self x2) (vala_map (List.map self) x3)
    | ExArr loc x1 →
        ExArr loc (vala_map (List.map self) x1)
    | ExAsr loc x1 →
        ExAsr loc (self x1)
    | ExAss loc x1 x2 →
        ExAss loc (self x1) (self x2)
    | ExBae loc x1 x2 x3 →
        ExBae loc x1 (self x2) (vala_map (List.map self) x3)
    | ExChr loc x1 →
        ExChr loc x1
    | ExCoe loc x1 x2 x3 →
        ExCoe loc (self x1) (option_map (ctyp arg) x2) (ctyp arg x3)
    | ExFlo loc x1 →
        ExFlo loc x1
    | ExFor loc x1 x2 x3 x4 x5 →
        ExFor loc (patt arg x1) (self x2) (self x3) x4 (vala_map (List.map self) x5)
    | ExFun loc x1 →
        ExFun loc
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt arg x1, vala_map (option_map self) x2, self x3)))
             x1)
    | ExIfe loc x1 x2 x3 →
        ExIfe loc (self x1) (self x2) (self x3)
    | ExInt loc x1 x2 →
        ExInt loc x1 x2
    | ExLab loc x1 →
        ExLab loc
          (vala_map
             (List.map
                (fun (x1, x2) →
                   (patt arg x1, vala_map (option_map self) x2)))
             x1)
    | ExLaz loc x1 →
        ExLaz loc (self x1)
    | ExLet loc x1 x2 x3 →
        ExLet loc x1
          (vala_map (List.map (fun (x1, x2, x3) → (patt arg x1, self x2, attributes arg x3))) x2)
          (self x3)
    | ExLEx loc x1 x2 x3 x4 ->
        ExLEx loc x1 (vala_map (List.map (ctyp arg)) x2) (self x3) (attributes arg x4)
    | ExLid loc x1 →
        ExLid loc x1
    | ExLmd loc x1 x2 x3 →
        ExLmd loc x1 (module_expr arg x2) (self x3)
    | ExLop loc b x1 x2 →
        ExLop loc b (module_expr arg x1) (self x2)
    | ExMat loc x1 x2 →
        ExMat loc (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt arg x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExNew loc x1 →
        ExNew loc (vala_map (longid_lident arg) x1)
    | ExObj loc x1 x2 →
        ExObj loc (vala_map (option_map (patt arg)) x1)
          (vala_map (List.map (class_str_item arg)) x2)
    | ExOlb loc x1 x2 →
        ExOlb loc (patt arg x1) (vala_map (option_map self) x2)
    | ExOvr loc x1 →
        ExOvr loc (vala_map (List.map (fun (x1, x2) → (x1, self x2))) x1)
    | ExPck loc x1 x2 →
        ExPck loc (module_expr arg x1)
          (option_map (module_type arg) x2)
    | ExRec loc x1 x2 →
        ExRec loc
          (vala_map (List.map (fun (x1, x2) → (patt arg x1, self x2))) x1)
          (option_map self x2)
    | ExSeq loc x1 →
        ExSeq loc (vala_map (List.map self) x1)
    | ExSnd loc x1 x2 →
        ExSnd loc (self x1) x2
    | ExSte loc x1 x2 x3 →
        ExSte loc x1 (self x2) (vala_map (List.map self) x3)
    | ExStr loc x1 →
        ExStr loc x1
    | ExTry loc x1 x2 →
        ExTry loc (self x1)
          (vala_map
             (List.map
                (fun (x1, x2, x3) →
                   (patt arg x1, vala_map (option_map self) x2, self x3)))
             x2)
    | ExTup loc x1 →
        ExTup loc (vala_map (List.map self) x1)
    | ExTyc loc x1 x2 →
        ExTyc loc (self x1) (ctyp arg x2)
    | ExUid loc x1 →
        ExUid loc x1
    | ExVrn loc x1 →
        ExVrn loc x1
    | ExWhi loc x1 x2 →
        ExWhi loc (self x1) (vala_map (List.map self) x2)
    | ExXtr loc x1 x2 →
        ExXtr loc x1 (option_map (vala_map self) x2)
    | ExExten loc exten ->
        ExExten loc exten
    | ExUnr loc ->
        ExUnr loc
    ] in
  self0
and module_type arg x =
  match Extfun.apply arg.Ctxt.ef.EF.module_type x arg with [
    x -> x
  | exception Extfun.Failure -> module_type0 arg x
  ]
and module_type0 arg =
  let rec self x = module_type arg x
  and self0 =
    fun
    [ MtAtt loc e attr ->
       MtAtt loc (self e) (attribute_body arg attr)
    | MtLong loc x1 →
        MtLong loc (longid arg x1)
    | MtLongLid loc x1 x2 →
        MtLongLid loc (longid arg x1) x2
    | MtFun loc arg x3 →
        let arg = vala_map (option_map (fun (idopt, m) -> (idopt, self m))) arg in
        MtFun loc arg (self x3)
    | MtLid loc x1 →
        MtLid loc x1
    | MtQuo loc x1 →
        MtQuo loc x1
    | MtSig loc x1 →
        MtSig loc (vala_map (List.map (sig_item arg)) x1)
    | MtTyo loc x1 →
        MtTyo loc (module_expr arg x1)
    | MtWit loc x1 x2 →
        MtWit loc (self x1) (vala_map (List.map (with_constr arg)) x2)
    | MtXtr loc x1 x2 →
        MtXtr loc x1 (option_map (vala_map self) x2)
    | MtExten loc exten ->
        MtExten loc (attribute_body arg exten)
    ] in
    self0
and sig_item arg x =
  match Extfun.apply arg.Ctxt.ef.EF.sig_item x arg with [
    x -> x
  | exception Extfun.Failure -> sig_item0 arg x
  ]
and sig_item0 arg =
  let rec self x = sig_item arg x
  and self0 =
    fun
    [ SgCls loc x1 →
        SgCls loc
          (vala_map (List.map (class_infos_map arg ~{attributes=attributes}  (class_type arg))) x1)
    | SgClt loc x1 →
        SgClt loc
          (vala_map (List.map (class_infos_map arg ~{attributes=attributes} (class_type arg))) x1)
    | SgDcl loc x1 →
        SgDcl loc (vala_map (List.map self) x1)
    | SgDir loc x1 x2 →
        SgDir loc x1 (vala_map (option_map (expr arg)) x2)
    | SgExc loc x1 x2 →
        SgExc loc (generic_constructor arg x1) (attributes arg x2)
    | SgExt loc x1 x2 x3 x4 →
        SgExt loc x1 (ctyp arg x2) x3 (attributes arg x4)
    | SgInc loc x1 x2 →
        SgInc loc (module_type arg x1) (attributes arg x2)
    | SgMod loc x1 x2 →
        SgMod loc x1
          (vala_map (List.map (fun (x1, x2, x3) → (x1, module_type arg x2, attributes arg x3)))
             x2)
    | SgMty loc x1 x2 x3 →
        SgMty loc x1 (module_type arg x2) (attributes arg x3)
    | SgMtyAbs loc x1 x2 →
        SgMtyAbs loc x1  (attributes arg x2)
    | SgMtyAlias loc x1 x2 x3 →
        SgMtyAlias loc x1 (vala_map (longid arg) x2) (attributes arg x3)
    | SgModSubst loc x1 x2 x3 →
        SgModSubst loc x1 (longid arg x2) (attributes arg x3)
    | SgOpn loc x1 x2 →
        SgOpn loc (longid arg x1) (attributes arg x2)
    | SgTyp loc x1 x2 →
        SgTyp loc x1 (vala_map (List.map (type_decl arg)) x2)
    | SgTypExten loc x1 →
        SgTypExten loc (type_extension arg x1)
    | SgUse loc x1 x2 →
        SgUse loc x1
          (vala_map (List.map (fun (x1, loc) → (self x1, loc))) x2)
    | SgVal loc x1 x2 x3 →
        SgVal loc x1 (ctyp arg x2) (attributes arg x3)
    | SgXtr loc x1 x2 →
        SgXtr loc x1 (option_map (vala_map self) x2)
    | SgFlAtt loc a ->
        SgFlAtt loc (attribute_body arg a)
    | SgExten loc exten ->
        SgExten loc (attribute_body arg exten)
    ] in
  self0
and with_constr arg x =
  match Extfun.apply arg.Ctxt.ef.EF.with_constr x arg with [
    x -> x
  | exception Extfun.Failure -> with_constr0 arg x
  ]
and with_constr0 arg =
  fun
  [ WcMod loc x1 x2 →
      WcMod loc (vala_map (longid arg) x1) (module_expr arg x2)
  | WcMos loc x1 x2 →
      WcMos loc (vala_map (longid arg) x1) (module_expr arg x2)
  | WcTyp loc x1 x2 x3 x4 →
      WcTyp loc (vala_map (longid_lident arg) x1) x2 x3 (ctyp arg x4)
  | WcTys loc x1 x2 x3 →
      WcTys loc (vala_map (longid_lident arg) x1) x2 (ctyp arg x3) ]
and longid arg x =
  match Extfun.apply arg.Ctxt.ef.EF.longid x arg with [
    x -> x
  | exception Extfun.Failure -> longid0 arg x
  ]
and longid0 arg =
  let rec self x = longid arg x
  and self0 =
    fun
    [ LiAcc loc x1 x2 →
        LiAcc loc (self x1) x2
    | LiApp loc x1 x2 →
        LiApp loc (self x1) (self x2)
    | LiUid loc x1 →
        LiUid loc x1
    ] in
  self0
and module_expr arg x =
  match Extfun.apply arg.Ctxt.ef.EF.module_expr x arg with [
    x -> x
  | exception Extfun.Failure -> module_expr0 arg x
  ]
and module_expr0 arg =
  let rec self x = module_expr arg x
  and self0 =
    fun
    [ MeAtt loc e attr ->
       MeAtt loc (self e) (attribute_body arg attr)
    | MeAcc loc x1 x2 →
        MeAcc loc (self x1) (self x2)
    | MeApp loc x1 x2 →
        MeApp loc (self x1) (self x2)
    | MeFun loc farg x3 →
        let farg = vala_map (option_map (fun (idopt, m) -> (idopt, module_type arg m))) farg in
        MeFun loc farg (self x3)
    | MeStr loc x1 →
        MeStr loc (vala_map (List.map (str_item arg)) x1)
    | MeTyc loc x1 x2 →
        MeTyc loc (self x1) (module_type arg x2)
    | MeUid loc x1 →
        MeUid loc x1
    | MeUnp loc x1 x2 x3 →
        MeUnp loc (expr arg x1) (option_map (module_type arg) x2) (option_map (module_type arg) x3)
    | MeXtr loc x1 x2 →
        MeXtr loc x1 (option_map (vala_map self) x2)
    | MeExten loc exten ->
        MeExten loc (attribute_body arg exten)
    ] in
    self0
and str_item arg x =
  match Extfun.apply arg.Ctxt.ef.EF.str_item x arg with [
    x -> x
  | exception Extfun.Failure -> str_item0 arg x
  ]
and str_item0 arg =
  let rec self x = str_item arg x
  and self0 =
    fun
    [ StCls loc x1 →
        StCls loc
          (vala_map (List.map (class_infos_map arg ~{attributes=attributes} (class_expr arg))) x1)
    | StClt loc x1 →
        StClt loc
          (vala_map (List.map (class_infos_map arg ~{attributes=attributes} (class_type arg))) x1)
    | StDcl loc x1 →
        StDcl loc (vala_map (List.map self) x1)
    | StDir loc x1 x2 →
        StDir loc x1 (vala_map (option_map (expr arg)) x2)
    | StExc loc x1 x2 →
        StExc loc (vala_map (extension_constructor arg) x1) (attributes arg x2)
    | StExp loc x1 x2 →
        StExp loc (expr arg x1) (attributes arg x2)
    | StExt loc x1 x2 x3 x4 →
        StExt loc x1 (ctyp arg x2) x3 (attributes arg x4)
    | StInc loc x1 x2 →
        StInc loc (module_expr arg x1) (attributes arg x2)
    | StMod loc x1 x2 →
        StMod loc x1
          (vala_map (List.map (fun (x1, x2, x3) →
           let arg = match Pcaml.unvala x1  with [
             Some s -> Ctxt.append_module arg (Pcaml.unvala s)
           | None -> arg
           ] in
           (x1, module_expr arg x2, attributes arg x3)))
             x2)
    | StMty loc x1 x2 x3 →
        StMty loc x1 (module_type arg x2) (attributes arg x3)
    | StMtyAbs loc x1 x2 →
        StMtyAbs loc x1 (attributes arg x2)
    | StOpn loc x1 x2 x3 →
        StOpn loc x1 (module_expr arg x2) (attributes arg x3)
    | StTyp loc x1 x2 →
        StTyp loc x1 (vala_map (List.map (type_decl arg)) x2)
    | StTypExten loc x1 →
        StTypExten loc (type_extension arg x1)
    | StUse loc x1 x2 →
        StUse loc x1
          (vala_map (List.map (fun (x1, loc) → (self x1, loc))) x2)
    | StVal loc x1 x2 →
        StVal loc x1
          (vala_map
             (List.map (fun (x1, x2, x3) → (patt arg x1, expr arg x2, attributes arg x3)))
             x2)
    | StXtr loc x1 x2 →
        StXtr loc x1 (option_map (vala_map self) x2)
    | StFlAtt loc a ->
        StFlAtt loc (attribute_body arg a)
    | StExten loc exten ->
        StExten loc (attribute_body arg exten)
    ] in
  self0
and type_decl arg x =
  match Extfun.apply arg.Ctxt.ef.EF.type_decl x arg with [
    x -> x
  | exception Extfun.Failure -> type_decl0 arg x
  ]
and type_decl0 arg x =
  {tdIsDecl = x.tdIsDecl ;
   tdNam = vala_map (fun (loc, x1) → (loc, x1)) x.tdNam; tdPrm = x.tdPrm;
   tdPrv = x.tdPrv; tdDef = ctyp arg x.tdDef;
   tdCon =
     vala_map (List.map (fun (x1, x2) → (ctyp arg x1, ctyp arg x2)))
       x.tdCon;
   tdAttributes = attributes arg x.tdAttributes}
and type_extension arg x =
  match Extfun.apply arg.Ctxt.ef.EF.type_extension x arg with [
    x -> x
  | exception Extfun.Failure -> type_extension0 arg x
  ]
and type_extension0 arg x =
  {teNam = vala_map (longid_lident arg) x.teNam; tePrm = x.tePrm;
   tePrv = x.tePrv;
   teECs = vala_map (List.map (extension_constructor arg)) x.teECs ;
   teAttributes = attributes arg x.teAttributes}
and extension_constructor arg x =
  match Extfun.apply arg.Ctxt.ef.EF.extension_constructor x arg with [
    x -> x
  | exception Extfun.Failure -> extension_constructor0 arg x
  ]
and extension_constructor0 arg = fun [
    EcTuple x1 -> EcTuple (generic_constructor arg x1)
  | EcRebind x1 x2 x3 -> EcRebind x1 x2 (attributes arg x3)
]
and class_type arg x =
  match Extfun.apply arg.Ctxt.ef.EF.class_type x arg with [
    x -> x
  | exception Extfun.Failure -> class_type0 arg x
  ]
and class_type0 arg =
  let rec self x = class_type arg x
  and self0 =
    fun
    [ CtAtt loc e attr ->
        CtAtt loc (self e) (attribute_body arg attr)
    | CtLongLid loc x1 x2 →
        CtLongLid loc (longid arg x1) x2
    | CtLid loc x1 →
        CtLid loc x1
    | CtLop loc x1 x2 x3 →
        CtLop loc x1 (longid arg x2) (self x3)
    | CtCon loc x1 x2 →
        CtCon loc (self x1) (vala_map (List.map (ctyp arg)) x2)
    | CtFun loc x1 x2 →
        CtFun loc (ctyp arg x1) (self x2)
    | CtSig loc x1 x2 →
        CtSig loc (vala_map (option_map (ctyp arg)) x1)
          (vala_map (List.map (class_sig_item arg)) x2)
    | CtXtr loc x1 x2 →
        CtXtr loc x1 (option_map (vala_map self) x2)
    | CtExten loc exten ->
        CtExten loc (attribute_body arg exten)
    ] in
  self0
and class_sig_item arg x =
  match Extfun.apply arg.Ctxt.ef.EF.class_sig_item x arg with [
    x -> x
  | exception Extfun.Failure -> class_sig_item0 arg x
  ]
and class_sig_item0 arg =
  let rec self x = class_sig_item arg x
  and self0 =
    fun
    [ CgCtr loc x1 x2 x3 →
        CgCtr loc (ctyp arg x1) (ctyp arg x2) (attributes arg x3)
    | CgDcl loc x1 →
        CgDcl loc (vala_map (List.map self) x1)
    | CgInh loc x1 x2 →
        CgInh loc (class_type arg x1) (attributes arg x2)
    | CgMth loc x1 x2 x3 x4 →
        CgMth loc x1 x2 (ctyp arg x3) (attributes arg x4)
    | CgVal loc x1 x2 x3 x4 x5 →
        CgVal loc x1 x2 x3 (ctyp arg x4) (attributes arg x5)
    | CgVir loc x1 x2 x3 x4 →
        CgVir loc x1 x2 (ctyp arg x3) (attributes arg x4)
    | CgFlAtt loc a ->
        CgFlAtt loc (attribute_body arg a)
    | CgExten loc exten ->
        CgExten loc (attribute_body arg exten)
    ] in
  self0
and class_expr arg x =
  match Extfun.apply arg.Ctxt.ef.EF.class_expr x arg with [
    x -> x
  | exception Extfun.Failure -> class_expr0 arg x
  ]
and class_expr0 arg =
  let rec self x = class_expr arg x
  and self0 =
    fun
    [ CeAtt loc e attr ->
       CeAtt loc (self e) (attribute_body arg attr)
    | CeApp loc x1 x2 →
        CeApp loc (self x1) (expr arg x2)
    | CeCon loc x1 x2 →
        CeCon loc (vala_map (longid_lident arg) x1) (vala_map (List.map (ctyp arg)) x2)
    | CeFun loc x1 x2 →
        CeFun loc (patt arg x1) (self x2)
    | CeLet loc x1 x2 x3 →
        CeLet loc x1
          (vala_map
             (List.map (fun (x1, x2, x3) → (patt arg x1, expr arg x2, attributes arg x3)))
             x2)
          (self x3)
    | CeLop loc x1 x2 x3 →
        CeLop loc x1 (longid arg x2) (self x3)
    | CeStr loc x1 x2 →
        CeStr loc (vala_map (option_map (patt arg)) x1)
          (vala_map (List.map (class_str_item arg)) x2)
    | CeTyc loc x1 x2 →
        CeTyc loc (self x1) (class_type arg x2)
    | CeXtr loc x1 x2 →
        CeXtr loc x1 (option_map (vala_map self) x2)
    | CeExten loc exten ->
        CeExten loc (attribute_body arg exten)
    ] in
  self0
and class_str_item arg x =
  match Extfun.apply arg.Ctxt.ef.EF.class_str_item x arg with [
    x -> x
  | exception Extfun.Failure -> class_str_item0 arg x
  ]
and class_str_item0 arg =
  let rec self x = class_str_item arg x
  and self0 =
    fun
    [ CrCtr loc x1 x2 x3 →
        CrCtr loc (ctyp arg x1) (ctyp arg x2) (attributes arg x3)
    | CrDcl loc x1 →
        CrDcl loc (vala_map (List.map self) x1)
    | CrInh loc ovf x1 x2 x3 →
        CrInh loc ovf (class_expr arg x1) x2 (attributes arg x3)
    | CrIni loc x1 x2 →
        CrIni loc (expr arg x1) (attributes arg x2)
    | CrMth loc x1 x2 x3 x4 x5 x6 →
        CrMth loc x1 x2 x3 (vala_map (option_map (ctyp arg)) x4)
          (expr arg x5) (attributes arg x6)
    | CrVal loc x1 x2 x3 x4 x5 →
        CrVal loc x1 x2 x3 (expr arg x4) (attributes arg x5)
    | CrVav loc x1 x2 x3 x4 →
        CrVav loc x1 x2 (ctyp arg x3) (attributes arg x4)
    | CrVir loc x1 x2 x3 x4 →
        CrVir loc x1 x2 (ctyp arg x3) (attributes arg x4)
    | CrFlAtt loc a -> 
        CrFlAtt loc (attribute_body arg a)
    | CrExten loc exten -> 
        CrExten loc (attribute_body arg exten)
    ] in
  self0
and longid_lident arg (x1, x2) =
    (option_map (longid arg) x1, x2)
and attribute_body arg x =
  match Extfun.apply arg.Ctxt.ef.EF.attribute_body x arg with [
    x -> x
  | exception Extfun.Failure -> attribute_body0 arg x
  ]
and attribute_body0 arg x1 =
    vala_map (fun (s, p) ->
        let p = match p with [
          StAttr loc x1 ->
            StAttr loc (vala_map (List.map (str_item arg)) x1)
        | SiAttr loc x1 ->
            SiAttr loc (vala_map (List.map (sig_item arg)) x1)
        | TyAttr loc x1 ->
            TyAttr loc (vala_map (ctyp arg) x1)
        | PaAttr loc x1 x2 ->
            PaAttr loc (vala_map (patt arg) x1) (option_map (vala_map (expr arg)) x2)
        ] in
        (s, p)) x1
and attributes_no_anti arg x1 = List.map (attribute_body arg) x1
and attributes arg x1 = vala_map (attributes_no_anti arg) x1
;

value passthru pa_before arg = do {
  let rv = pa_before arg in
  let (l, status) = rv in
  assert (l <> []) ;
  let (_, loc) = List.hd l in
  let ctxt = Ctxt.mk ef.val loc in
  (List.map (fun (si, loc) -> (str_item ctxt si, loc)) l, status)
}
;
Pcaml.parse_implem.val := passthru Pcaml.parse_implem.val;
