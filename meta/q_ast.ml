(* camlp5r *)
(* q_ast.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Q_ast_base ;

module Meta_make (C : MetaSig) =
  struct
    module C = C ;
    open MLast;
    value variance (var, inj) =
      C.tuple [C.option C.bool var; C.bool inj] ;
    value type_var (s, tv) =
      C.tuple [C.vala (C.option C.string) s; variance tv]
    ;
    value record_label lab =
      let loc = Ploc.dummy in
      <:patt< MLast . $lid:lab$ >>
    ;
    value class_infos f ci =
      C.record
        [(record_label "ciLoc", C.loc_v ());
         (record_label "ciVir", C.vala C.bool ci.ciVir);
         (record_label "ciPrm",
          C.tuple [C.loc_v (); C.vala (C.list type_var) (snd ci.ciPrm)]);
         (record_label "ciNam", C.vala C.string ci.ciNam);
         (record_label "ciExp", f ci.ciExp)]
    ;
    value rec ctyp =
      fun
      [ TyAtt _ ct att -> C.node "TyAtt" [ctyp ct; attribute att]
      | TyAcc _ m1 t2 → C.node "TyAcc" [longid m1; C.vala C.string t2]
      | TyAli _ t1 t2 → C.node "TyAli" [ctyp t1; ctyp t2]
      | TyAny _ → C.node "TyAny" []
      | TyApp _ t1 t2 → C.node "TyApp" [ctyp t1; ctyp t2]
      | TyArr _ t1 t2 → C.node "TyArr" [ctyp t1; ctyp t2]
      | TyCls _ cli → C.node "TyCls" [C.vala longid_lident cli]
      | TyLab _ s t → C.node "TyLab" [C.vala C.string s; ctyp t]
      | TyLid _ s → C.node "TyLid" [C.vala C.string s]
      | TyMan _ t1 b t2 → C.node "TyMan" [ctyp t1; C.vala C.bool b; ctyp t2]
      | TyObj _ lst b →
          C.node "TyObj"
            [C.vala (C.list (fun (s, t, attrs) → 
                              let attrs = conv_attributes attrs in
                              C.tuple [C.option C.string s; ctyp t; attrs])) lst;
             C.vala C.bool b]
      | TyOlb _ s t → C.node "TyOlb" [C.vala C.string s; ctyp t]
      | TyOpn _ -> C.node "TyOpn" []
      | TyPck _ mt → C.node "TyPck" [module_type mt]
      | TyPol _ ls t → C.node "TyPol" [C.vala (C.list C.string) ls; ctyp t]
      | TyPot _ ls t → C.node "TyPot" [C.vala (C.list C.string) ls; ctyp t]
      | TyQuo _ s → C.node "TyQuo" [C.vala C.string s]
      | TyRec _ llsbt →
          C.node "TyRec"
            [C.vala
               (C.list
                  (fun (_, s, b, t, attrs) →
                     let attrs = conv_attributes attrs in
                     C.tuple [C.loc_v (); C.string s; C.bool b; ctyp t; attrs]))
               llsbt]
      | TySum _ llsltot →
          C.node "TySum"
            [C.vala
               (C.list
                  generic_constructor)
               llsltot]
      | TyTup _ lt → C.node "TyTup" [C.vala (C.list ctyp) lt]
      | TyVrn _ lpv ools →
          C.node "TyVrn"
            [C.vala (C.list poly_variant) lpv;
             C.option (C.option (C.vala (C.list C.string))) ools]
      | TyXtr loc s _ → C.xtr loc s
      | TyExten loc exten ->
          let exten = conv_extension exten in
          C.node "TyExten" [exten]
      ]
    and longid_lident (lio, s) = C.tuple [C.option (C.vala longid) lio; C.vala C.string s]
    and conv_attributes attrs =
      C.vala (C.list attribute) attrs
    and conv_extension e = attribute e
    and attribute a = C.vala attribute_body a
    and attribute_body (locs, p) =
      let locs = C.vala (fun (_, s) -> C.tuple [C.loc_v (); C.string s]) locs in
      C.tuple [locs; conv_payload p]
    and conv_payload = fun [
      StAttr _ lsi -> C.node "StAttr" [C.vala (C.list str_item) lsi]
    | SiAttr _ lsi -> C.node "SiAttr" [C.vala (C.list sig_item) lsi]
    | TyAttr _ t -> C.node "TyAttr" [C.vala ctyp t]
    | PaAttr _ p eo -> C.node "PaAttr" [C.vala patt p; C.option (C.vala expr) eo]
    ]
    and generic_constructor = fun (_, s, ls, lt, ot, attrs) →
      let attrs = conv_attributes attrs in
        C.tuple
          [C.loc_v (); C.vala C.string s; C.vala (C.list C.string) ls;
           C.vala (C.list ctyp) lt; C.vala (C.option ctyp) ot; attrs]
    and poly_variant =
      fun
      [ PvTag _ s b lt attrs →
          let attrs = conv_attributes attrs in
          C.node "PvTag"
            [C.vala C.string s; C.vala C.bool b; C.vala (C.list ctyp) lt; attrs]
      | PvInh _ t → C.node "PvInh" [ctyp t] ]
    and patt =
      fun
      [ PaAtt _ e att -> C.node "PaAtt" [patt e; attribute att]
      | PaPfx _ li p -> C.node "PaPfx" [longid li; patt p]
      | PaLong _ li loc_ids -> C.node "PaLong" [
                                    longid li ;
                                    C.vala (C.list (fun (_, s) -> C.tuple [C.loc_v(); C.string s])) loc_ids
                                  ]
      | PaAli _ p1 p2 → C.node "PaAli" [patt p1; patt p2]
      | PaAnt _ p → C.node "PaAnt" [patt p]
      | PaAny _ → C.node "PaAny" []
      | PaApp _ p1 p2 → C.node "PaApp" [patt p1; patt p2]
      | PaArr _ lp → C.node "PaArr" [C.vala (C.list patt) lp]
      | PaChr _ s → C.node "PaChr" [C.vala C.string s]
      | PaExc _ p → C.node "PaExc" [patt p]
      | PaFlo _ s → C.node "PaFlo" [C.vala C.string s]
      | PaInt _ s1 s2 → C.node "PaInt" [C.vala C.string s1; C.string s2]
      | PaLab _ lpop →
          C.node "PaLab"
            [C.vala
               (C.list
                  (fun (p, op) → C.tuple [patt p; C.vala (C.option patt) op]))
               lpop]
      | PaLaz _ p → C.node "PaLaz" [patt p]
      | PaLid _ s → C.node "PaLid" [C.vala C.string s]
      | PaNty _ s → C.node "PaNty" [C.vala C.string s]
      | PaOlb _ p oe → C.node "PaOlb" [patt p; C.vala (C.option expr) oe]
      | PaOrp _ p1 p2 → C.node "PaOrp" [patt p1; patt p2]
      | PaRec _ lpp →
          C.node "PaRec"
            [C.vala (C.list (fun (p1, p2) → C.tuple [patt p1; patt p2])) lpp]
      | PaRng _ p1 p2 → C.node "PaRng" [patt p1; patt p2]
      | PaStr _ s → C.node "PaStr" [C.vala C.string s]
      | PaTup _ lp → C.node "PaTup" [C.vala (C.list patt) lp]
      | PaTyc _ p t → C.node "PaTyc" [patt p; ctyp t]
      | PaTyp _ lili → C.node "PaTyp" [C.vala longid_lident lili]
      | PaUnp _ s omt →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          C.node "PaUnp" [C.vala c_vala_opt s; C.option module_type omt]
      | PaVrn _ s → C.node "PaVrn" [C.vala C.string s]
      | 
          PaXtr loc s _ → C.xtr_or_anti loc (fun r → C.node "PaAnt" [r]) s
      | PaExten loc exten ->
          let exten = conv_extension exten in
          C.node "PaExten" [exten]
      ]
    and expr =
      fun
      [ ExAtt _ e att -> C.node "ExAtt" [expr e; attribute att]
      | ExLong _ x1 -> C.node "ExLong" [longid x1]
      | ExOpen _ x1 x2 -> C.node "ExOpen" [longid x1; expr x2]
      | ExFle _ x1 x2 -> C.node "ExFle" [expr x1; C.vala longid_lident x2]
      | ExAnt _ e → C.node "ExAnt" [expr e]
      | ExApp _ e1 e2 → C.node "ExApp" [expr e1; expr e2]
      | ExAre _ s e1 e2 → C.node "ExAre" [C.vala C.string s; expr e1; C.vala (C.list expr) e2]
      | ExArr _ le → C.node "ExArr" [C.vala (C.list expr) le]
      | ExAsr _ e → C.node "ExAsr" [expr e]
      | ExAss _ e1 e2 → C.node "ExAss" [expr e1; expr e2]
      | ExBae _ s e le → C.node "ExBae" [C.vala C.string s; expr e; C.vala (C.list expr) le]
      | ExChr _ s → C.node "ExChr" [C.vala C.string s]
      | ExCoe _ e ot t → C.node "ExCoe" [expr e; C.option ctyp ot; ctyp t]
      | ExFlo _ s → C.node "ExFlo" [C.vala C.string s]
      | ExFor _ s e1 e2 b le →
          C.node "ExFor"
            [patt s; expr e1; expr e2; C.vala C.bool b;
             C.vala (C.list expr) le]
      | ExFun _ lpoee →
          C.node "ExFun"
            [C.vala
               (C.list
                  (fun (p, oe, e) →
                     C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
               lpoee]
      | ExIfe _ e1 e2 e3 → C.node "ExIfe" [expr e1; expr e2; expr e3]
      | ExInt _ s1 s2 → C.node "ExInt" [C.vala C.string s1; C.string s2]
      | ExLab _ lpoe →
          C.node "ExLab"
            [C.vala
               (C.list
                  (fun (p, oe) → C.tuple [patt p; C.vala (C.option expr) oe]))
               lpoe]
      | ExLaz _ e → C.node "ExLaz" [expr e]
      | ExLet _ b lpe e →
          C.node "ExLet"
            [C.vala C.bool b;
             C.vala (C.list (fun (p, e, attrs) →
               let attrs = conv_attributes attrs in
               C.tuple [patt p; expr e; attrs])) lpe;
             expr e]
      | ExLEx _ id lt e attrs ->
          let attrs = conv_attributes attrs in
          C.node "ExLEx"
            [C.vala C.string id; C.vala (C.list ctyp) lt; expr e; attrs]
      | ExLid _ s → C.node "ExLid" [C.vala C.string s]
      | ExLmd _ s me e →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          C.node "ExLmd" [C.vala c_vala_opt s; module_expr me; expr e]
      | ExLop _ b me e → C.node "ExLop" [C.vala C.bool b; module_expr me; expr e]
      | ExMat _ e lpoee →
          C.node "ExMat"
            [expr e;
             C.vala
               (C.list
                  (fun (p, oe, e) →
                     C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
               lpoee]
      | ExNew _ cli → C.node "ExNew" [C.vala longid_lident cli]
      | ExObj _ op lcsi →
          C.node "ExObj"
            [C.vala (C.option patt) op; C.vala (C.list class_str_item) lcsi]
      | ExOlb _ p oe → C.node "ExOlb" [patt p; C.vala (C.option expr) oe]
      | ExOvr _ lse →
          C.node "ExOvr"
            [C.vala (C.list (fun (s, e) → C.tuple [C.string s; expr e])) lse]
      | ExPck _ me omt →
          C.node "ExPck" [module_expr me; C.option module_type omt]
      | ExRec _ lpe oe →
          C.node "ExRec"
            [C.vala (C.list (fun (p, e) → C.tuple [patt p; expr e])) lpe;
             C.option expr oe]
      | ExSeq _ le → C.node "ExSeq" [C.vala (C.list expr) le]
      | ExSnd _ e s → C.node "ExSnd" [expr e; C.vala C.string s]
      | ExSte _ s e1 e2 → C.node "ExSte" [C.vala C.string s; expr e1; C.vala (C.list expr) e2]
      | ExStr _ s → C.node "ExStr" [C.vala C.string s]
      | ExTry _ e lpoee →
          C.node "ExTry"
            [expr e;
             C.vala
               (C.list
                  (fun (p, oe, e) →
                     C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
               lpoee]
      | ExTup _ le → C.node "ExTup" [C.vala (C.list expr) le]
      | ExTyc _ e t → C.node "ExTyc" [expr e; ctyp t]
      | ExVrn _ s → C.node "ExVrn" [C.vala C.string s]
      | ExWhi _ e le → C.node "ExWhi" [expr e; C.vala (C.list expr) le]
      | 
          ExXtr loc s _ → C.xtr_or_anti loc (fun r → C.node "ExAnt" [r]) s
      | ExExten loc exten ->
          let exten = conv_extension exten in
          C.node "ExExten" [exten]
      | ExUnr loc -> C.node "ExUnr" []
      ]
    and module_type =
      fun
      [ MtAtt _ e att -> C.node "MtAtt" [module_type e; attribute att]
      | MtLong _ mt1 → C.node "MtLong" [longid mt1]
      | MtLongLid _ mt1 lid → C.node "MtLongLid" [longid mt1; C.vala C.string lid]
      | MtLid _ s → C.node "MtLid" [C.vala C.string s]
      | MtFun _ arg mt2 →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          let c_tuple (sopt, mt) =
            C.tuple [C.vala c_vala_opt sopt; module_type mt] in
          let c_arg arg = C.option c_tuple arg in
            C.node "MtFun" [C.vala c_arg arg; module_type mt2]
      | MtQuo _ s → C.node "MtQuo" [C.vala C.string s]
      | MtSig _ lsi → C.node "MtSig" [C.vala (C.list sig_item) lsi]
      | MtTyo _ me → C.node "MtTyo" [module_expr me]
      | MtWit _ mt lwc →
          C.node "MtWit" [module_type mt; C.vala (C.list with_constr) lwc]
      | 
          MtXtr loc s _ → C.xtr loc s
      | MtExten loc exten ->
          let exten = conv_extension exten in
          C.node "MtExten" [exten]
      ]
    and sig_item =
      fun
      [ SgCls _ lcict →
          C.node "SgCls" [C.vala (C.list (class_infos class_type)) lcict]
      | SgClt _ lcict →
          C.node "SgClt" [C.vala (C.list (class_infos class_type)) lcict]
      | SgDcl _ lsi → C.node "SgDcl" [C.vala (C.list sig_item) lsi]
      | SgDir _ s oe →
          C.node "SgDir" [C.vala C.string s; C.vala (C.option expr) oe]
      | SgExc _ gc item_attrs →
          let item_attrs = conv_attributes item_attrs in
          C.node "SgExc" [generic_constructor gc; item_attrs]
      | SgExt _ s ltv t ls attrs →
          let attrs = conv_attributes attrs in
          C.node "SgExt"
            [C.vala C.string s; C.vala (C.list C.string) ltv; ctyp t; C.vala (C.list C.string) ls; attrs]
      | SgInc _ mt attrs →
          let attrs = conv_attributes attrs in
          C.node "SgInc" [module_type mt; attrs]
      | SgMod _ b lsmt →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          C.node "SgMod"
            [C.vala C.bool b;
             C.vala
               (C.list
                  (fun (sopt, mt, attrs) →
                     let attrs = conv_attributes attrs in
                     C.tuple [C.vala c_vala_opt sopt; module_type mt; attrs]))
               lsmt]
      | SgMty _ s mt attrs →
           let attrs = conv_attributes attrs in
           C.node "SgMty" [C.vala C.string s; module_type mt; attrs]
      | SgMtySubst _ s mt attrs →
           let attrs = conv_attributes attrs in
           C.node "SgMtySubst" [C.vala C.string s; module_type mt; attrs]
      | SgMtyAlias _ s ls attrs →
           let attrs = conv_attributes attrs in
           C.node "SgMtyAlias" [C.vala C.string s; C.vala longid ls; attrs]
      | SgModSubst _ s li attrs ->
           let attrs = conv_attributes attrs in
           C.node "SgModSubst" [C.vala C.string s; longid li; attrs]
      | SgOpn _ li attrs →
          let attrs = conv_attributes attrs in
           C.node "SgOpn" [longid li; attrs]
      | SgTyp _ b ltd → C.node "SgTyp" [C.vala C.bool b; C.vala (C.list type_decl) ltd]
      | SgTypExten _ te ->
          C.node "SgTypExten" [type_extension te]
      | SgUse _ s lsil →
          C.node "SgUse"
            [C.vala C.string s;
             C.vala (C.list (fun (si, _) → C.tuple [sig_item si; C.loc_v ()]))
               lsil]
      | SgVal _ s t attrs →
          let attrs = conv_attributes attrs in
          C.node "SgVal" [C.vala C.string s; ctyp t; attrs]
      | SgXtr loc s _ → C.xtr loc s
      | SgFlAtt loc attr ->
          let attr = attribute attr in
          C.node "SgFlAtt" [attr]
      | SgExten loc exten attrs ->
          let exten = conv_extension exten in
          C.node "SgExten" [exten; conv_attributes attrs]
      ]
    and with_constr =
      fun
      [ WcMod _ ls me →
          C.node "WcMod" [C.vala longid ls; module_expr me]
      | WcMos _ ls me →
          C.node "WcMos" [C.vala longid ls; module_expr me]
      | WcMty _ ls mt -> 
         C.node "WcMty" [C.vala longid ls; module_type mt]
      | WcMts _ ls mt -> 
         C.node "WcMts" [C.vala longid ls; module_type mt]
      | WcTyp _ ls ltv b t →
          C.node "WcTyp"
            [C.vala longid_lident ls; C.vala (C.list type_var) ltv;
             C.vala C.bool b; ctyp t]
      | WcTys _ ls ltv t →
          C.node "WcTys"
            [C.vala longid_lident ls; C.vala (C.list type_var) ltv;
             ctyp t] ]
    and longid =
      fun
      [ LiAcc _ me1 s → C.node "LiAcc" [longid me1; C.vala C.string s]
      | LiApp _ me1 me2 → C.node "LiApp" [longid me1; longid me2]
      | LiUid _ s → C.node "LiUid" [C.vala C.string s]
      | LiXtr loc s _ → C.xtr_typed "longid" loc s
      ]
    and module_expr =
      fun
      [ MeAtt _ e att -> C.node "MeAtt" [module_expr e; attribute att]
      | MeAcc _ me1 me2 → C.node "MeAcc" [module_expr me1; module_expr me2]
      | MeApp _ me1 me2 → C.node "MeApp" [module_expr me1; module_expr me2]
      | MeFun _ arg me →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          let c_tuple (sopt, mt) =
            C.tuple [C.vala c_vala_opt sopt; module_type mt] in
          let c_arg arg = C.option c_tuple arg in
          C.node "MeFun" [C.vala c_arg arg; module_expr me]
      | MeStr _ lsi → C.node "MeStr" [C.vala (C.list str_item) lsi]
      | MeTyc _ me mt → C.node "MeTyc" [module_expr me; module_type mt]
      | MeUid _ s → C.node "MeUid" [C.vala C.string s]
      | MeUnp _ e omt1 omt2 → C.node "MeUnp" [expr e; C.option module_type omt1; C.option module_type omt2]
      | MeXtr loc s _ → C.xtr loc s
      | MeExten loc exten ->
          let exten = conv_extension exten in
          C.node "MeExten" [exten]
      ]
    and str_item =
      fun
      [ StCls _ lcice →
          C.node "StCls" [C.vala (C.list (class_infos class_expr)) lcice]
      | StClt _ lcict →
          C.node "StClt" [C.vala (C.list (class_infos class_type)) lcict]
      | StDcl _ lsi → C.node "StDcl" [C.vala (C.list str_item) lsi]
      | StDir _ s oe →
          C.node "StDir" [C.vala C.string s; C.vala (C.option expr) oe]
      | StExc _ extc attrs ->
          let attrs = conv_attributes attrs in
          C.node "StExc" [C.vala extension_constructor extc; attrs] 
      | StExp _ e attrs →
          let attrs = conv_attributes attrs in
          C.node "StExp" [expr e; attrs]
      | StExt _ s ltv t ls attrs →
          let attrs = conv_attributes attrs in
          C.node "StExt"
            [C.vala C.string s; C.vala (C.list C.string) ltv; ctyp t; C.vala (C.list C.string) ls; attrs]
      | StInc _ me attrs → 
          let attrs = conv_attributes attrs in
          C.node "StInc" [module_expr me; attrs]
      | StMod _ b lsme →
          let c_vala x = C.vala C.string x in
          let c_vala_opt sopt = C.option c_vala sopt in
          C.node "StMod"
            [C.vala C.bool b;
             C.vala
               (C.list
                  (fun (sopt, me, attrs) → 
                    let attrs = conv_attributes attrs in
                    C.tuple [C.vala c_vala_opt sopt; module_expr me; attrs]))
               lsme]
      | StMty _ s mt attrs →
           let attrs = conv_attributes attrs in
           C.node "StMty" [C.vala C.string s; module_type mt; attrs]
      | StOpn _ b1 me attrs →
           let attrs = conv_attributes attrs in
           C.node "StOpn" [C.vala C.bool b1; module_expr me; attrs]
      | StTyp _ b ltd →
          C.node "StTyp" [C.vala C.bool b; C.vala (C.list type_decl) ltd]
      | StTypExten _ te ->
          C.node "StTypExten" [type_extension te]
      | StUse _ s lsil →
          C.node "StUse"
            [C.vala C.string s;
             C.vala (C.list (fun (si, _) → C.tuple [str_item si; C.loc_v ()]))
               lsil]
      | StVal _ b lpe →
          C.node "StVal"
            [C.vala C.bool b;
             C.vala (C.list (fun (p, e, attrs) →
               let attrs = conv_attributes attrs in
               C.tuple [patt p; expr e; attrs])) lpe]
      | StXtr loc s _ → C.xtr loc s
      | StFlAtt loc attr ->
          let attr = attribute attr in
          C.node "StFlAtt" [attr]
      | StExten loc exten attrs ->
          let exten = conv_extension exten in
          C.node "StExten" [exten; conv_attributes attrs]
      ]
    and type_decl x =
      let attrs = conv_attributes x.tdAttributes in
      C.record
        [
         (record_label "tdIsDecl", C.vala C.bool x.tdIsDecl);
          (record_label "tdNam",
           C.vala (fun (_, s) → C.tuple [C.loc_v (); C.vala C.string s])
             x.tdNam);
          (record_label "tdPrm", C.vala (C.list type_var) x.tdPrm);
          (record_label "tdPrv", C.vala C.bool x.tdPrv);
          (record_label "tdDef", ctyp x.tdDef);
          (record_label "tdCon",
           C.vala (C.list (fun (t1, t2) → C.tuple [ctyp t1; ctyp t2]))
             x.tdCon);
          (record_label "tdAttributes", attrs)
        ]
    and extension_constructor = fun [
      EcTuple loc gc ->
        C.node "EcTuple" [generic_constructor gc]
    | EcRebind loc s li attrs ->
        let attrs = conv_attributes attrs in
        C.node "EcRebind" [C.vala C.string s; C.vala longid li; attrs]
    ]
    and type_extension x =
      let attrs = conv_attributes x.teAttributes in
      let ecs = C.vala (C.list extension_constructor) x.teECs in
      C.record
        [(record_label "teNam", C.vala longid_lident x.teNam);
         (record_label "tePrm", C.vala (C.list type_var) x.tePrm);
         (record_label "tePrv", C.vala C.bool x.tePrv);
         (record_label "teECs", ecs);
         (record_label "teAttributes", attrs)]
    and class_type =
      fun
      [ CtAtt _ e att -> C.node "CtAtt" [class_type e; attribute att]
      | CtLongLid _ mt1 lid → C.node "CtLongLid" [longid mt1; C.vala C.string lid]
      | CtLid _ s → C.node "CtLid" [C.vala C.string s]
      | CtLop _ ovf me e →
          C.node "CtLop" [C.vala C.bool ovf ; longid me; class_type e]
      | CtCon _ ct lt →
          C.node "CtCon" [class_type ct; C.vala (C.list ctyp) lt]
      | CtFun _ t ct → C.node "CtFun" [ctyp t; class_type ct]
      | CtSig _ ot lcsi →
          C.node "CtSig"
            [C.vala (C.option ctyp) ot; C.vala (C.list class_sig_item) lcsi]
      | 
          CtXtr loc s _ → C.xtr loc s
      | CtExten loc exten ->
          let exten = conv_extension exten in
          C.node "CtExten" [exten]
      ]
    and class_sig_item =
      fun
      [ CgCtr _ t1 t2 attrs →
          let attrs = conv_attributes attrs in
          C.node "CgCtr" [ctyp t1; ctyp t2; attrs]
      | CgDcl _ lcsi → C.node "CgDcl" [C.vala (C.list class_sig_item) lcsi]
      | CgInh _ ct attrs → 
          let attrs = conv_attributes attrs in
          C.node "CgInh" [class_type ct; attrs]
      | CgMth _ b s t attrs →
          let attrs = conv_attributes attrs in
          C.node "CgMth" [C.vala C.bool b; C.vala C.string s; ctyp t; attrs]
      | CgVal _ mf vf s t attrs →
          let attrs = conv_attributes attrs in
          C.node "CgVal" [C.vala C.bool mf; C.vala C.bool vf; C.vala C.string s; ctyp t; attrs]
      | CgVir _ b s t attrs →
          let attrs = conv_attributes attrs in
          C.node "CgVir" [C.vala C.bool b; C.vala C.string s; ctyp t; attrs]
      | CgFlAtt loc attr ->
          let attr = attribute attr in
          C.node "CgFlAtt" [attr]
      | CgExten loc exten ->
          let exten = conv_extension exten in
          C.node "CgExten" [exten]
      ]
    and class_expr =
      fun
      [ CeAtt _ e att -> C.node "CeAtt" [class_expr e; attribute att]
      | CeApp _ ce e → C.node "CeApp" [class_expr ce; expr e]
      | CeCon _ cli lt →
          C.node "CeCon"
            [C.vala longid_lident cli; C.vala (C.list ctyp) lt]
      | CeFun _ p ce → C.node "CeFun" [patt p; class_expr ce]
      | CeLet _ b lpe ce →
          C.node "CeLet"
            [C.vala C.bool b;
             C.vala (C.list (fun (p, e, attrs) →
               let attrs = conv_attributes attrs in
               C.tuple [patt p; expr e; attrs])) lpe;
             class_expr ce]
      | CeLop _ ovf me e →
          C.node "CeLop" [C.vala C.bool ovf ; longid me; class_expr e]
      | CeStr _ op lcsi →
          C.node "CeStr"
            [C.vala (C.option patt) op; C.vala (C.list class_str_item) lcsi]
      | CeTyc _ ce ct → C.node "CeTyc" [class_expr ce; class_type ct]
      | 
          CeXtr loc s _ → C.xtr loc s
      | CeExten loc exten ->
          let exten = conv_extension exten in
          C.node "CeExten" [exten]
      ]
    and class_str_item =
      fun
      [ CrCtr _ t1 t2 attrs →
        let attrs = conv_attributes attrs in
        C.node "CrCtr" [ctyp t1; ctyp t2; attrs]
      | CrDcl _ lcsi → C.node "CrDcl" [C.vala (C.list class_str_item) lcsi]
      | CrInh loc b1 ce os attrs →
          let attrs = conv_attributes attrs in
          C.node "CrInh" [C.vala C.bool b1; class_expr ce; C.vala (C.option C.string) os; attrs]
      | CrIni _ e attrs →
        let attrs = conv_attributes attrs in
        C.node "CrIni" [expr e; attrs]
      | CrMth _ b1 b2 s ot e attrs →
          let attrs = conv_attributes attrs in
          C.node "CrMth"
            [C.vala C.bool b1; C.vala C.bool b2; C.vala C.string s;
             C.vala (C.option ctyp) ot; expr e; attrs]
      | CrVal _ b1 b2 s e attrs →
          let attrs = conv_attributes attrs in
          C.node "CrVal"
            [C.vala C.bool b1; C.vala C.bool b2; C.vala C.string s; expr e; attrs]
      | CrVav _ b s t attrs →
          let attrs = conv_attributes attrs in
          C.node "CrVav" [C.vala C.bool b; C.vala C.string s; ctyp t; attrs]
      | CrVir _ b s t attrs →
          let attrs = conv_attributes attrs in
          C.node "CrVir" [C.vala C.bool b; C.vala C.string s; ctyp t; attrs]
      | CrFlAtt loc attr ->
          let attr = attribute attr in
          C.node "CrFlAtt" [attr]
      | CrExten loc exten ->
          let exten = conv_extension exten in
          C.node "CrExten" [exten]
      ]
    ;
  end
;

module Meta_E = Meta_make(E_MetaSig) ;
module Meta_P = Meta_make(P_MetaSig) ;

value attribute_body_eoi = Grammar.Entry.create Pcaml.gram "attribute_body_eoi";
value class_expr_eoi = Grammar.Entry.create Pcaml.gram "class_expr";
value class_sig_item_eoi = Grammar.Entry.create Pcaml.gram "class_sig_item";
value class_str_item_eoi = Grammar.Entry.create Pcaml.gram "class_str_item";
value class_type_eoi = Grammar.Entry.create Pcaml.gram "class_type";
value ctyp_eoi = Grammar.Entry.create Pcaml.gram "type";
value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value extended_longident_eoi = Grammar.Entry.create Pcaml.gram "extended_longident_eoi";
value extension_constructor_eoi = Grammar.Entry.create Pcaml.gram "extension_constructor_eoi";
value constructor_eoi = Grammar.Entry.create Pcaml.gram "constructor_eoi";
value longident_eoi = Grammar.Entry.create Pcaml.gram "longident_eoi";
value module_expr_eoi = Grammar.Entry.create Pcaml.gram "module_expr";
value module_type_eoi = Grammar.Entry.create Pcaml.gram "module_type";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value poly_variant_eoi = Grammar.Entry.create Pcaml.gram "poly_variant";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
value str_item_eoi = Grammar.Entry.create Pcaml.gram "str_item";
value type_decl_eoi = Grammar.Entry.create Pcaml.gram "type_declaration";
value type_extension_eoi = Grammar.Entry.create Pcaml.gram "type_extension_eoi";
value with_constr_eoi = Grammar.Entry.create Pcaml.gram "with_constr";

EXTEND
  attribute_body_eoi: [ [ x = Pcaml.attribute_body; EOI -> x ] ];
  class_expr_eoi: [ [ x = Pcaml.class_expr ; EOI -> x ] ];
  class_sig_item_eoi: [ [ x = Pcaml.class_sig_item; EOI -> x ] ];
  class_str_item_eoi: [ [ x = Pcaml.class_str_item; EOI -> x ] ];
  class_type_eoi: [ [ x = Pcaml.class_type; EOI -> x ] ];
  ctyp_eoi: [ [ x = Pcaml.ctyp; EOI -> x ] ];
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  extended_longident_eoi: [ [ x = Pcaml.extended_longident; EOI -> x ] ];
  extension_constructor_eoi: [ [ x = Pcaml.extension_constructor; EOI -> x ] ];
  constructor_eoi: [ [ x = Pcaml.constructor_declaration; EOI -> x ] ];
  longident_eoi: [ [ x = Pcaml.longident; EOI -> x ] ];
  module_expr_eoi: [ [ x = Pcaml.module_expr; EOI -> x ] ];
  module_type_eoi: [ [ x = Pcaml.module_type; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  poly_variant_eoi: [ [ x = Pcaml.poly_variant; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
  str_item_eoi: [ [ x = Pcaml.str_item ; EOI -> x ] ];
  type_decl_eoi: [ [ x = Pcaml.type_decl; EOI -> x ] ];
  type_extension_eoi: [ [ x = Pcaml.type_extension; EOI -> x ] ];
  with_constr_eoi: [ [ x = Pcaml.with_constr; EOI -> x ] ];
END;

IFDEF STRICT THEN
  EXTEND
    Pcaml.class_expr_simple: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.CeXtr loc s None ] ]
    ;
    Pcaml.class_type: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.CtXtr loc s None ] ]
    ;
    Pcaml.ctyp: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.TyXtr loc s None ] ]
    ;
    Pcaml.longident: LAST
      [ [ s = ANTIQUOT_LOC "longid" -> MLast.LiXtr loc s None ] ]
    ;
    Pcaml.extended_longident: LAST
      [ [ s = ANTIQUOT_LOC "longid" -> MLast.LiXtr loc s None ] ]
    ;
    Pcaml.expr: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.ExXtr loc s None
        | s = ANTIQUOT_LOC "anti" -> MLast.ExXtr loc s None
        | s = ANTIQUOT_LOC "exp" -> MLast.ExXtr loc s None
        ] ]
    ;
    Pcaml.ipatt: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.PaXtr loc s None ] ]
    ;
    Pcaml.module_expr: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.MeXtr loc s None ] ]
    ;
    Pcaml.module_type: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.MtXtr loc s None ] ]
    ;
    Pcaml.patt: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.PaXtr loc s None
        | s = ANTIQUOT_LOC "anti" -> MLast.PaXtr loc s None ] ]
    ;
    Pcaml.sig_item: FIRST
      [ [ s = ANTIQUOT_LOC -> MLast.SgXtr loc s None ] ]
    ;
    Pcaml.str_item: FIRST
      [ [ s = ANTIQUOT_LOC -> MLast.StXtr loc s None
        | s = ANTIQUOT_LOC "stri" ->
          let s = replace_antiloc_kind ~{newkind=""} s in
          MLast.StXtr loc s None
        ] ]
    ;
  END;
END;

value check_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in
    String.sub s (i + 1) len
  with
  [ Not_found | Failure _ -> raise Stream.Failure ]
;

let lex = Grammar.glexer Pcaml.gram in
let tok_match = lex.Plexing.tok_match in
lex.Plexing.tok_match :=
  fun
  [("ANTIQUOT_LOC", p_prm) ->
      if p_prm <> "" && (p_prm.[0] = '~' || p_prm.[0] = '?') then
        let p_prm0 = p_prm.[0] in
        if p_prm.[String.length p_prm - 1] = ':' then
          let p_prm = String.sub p_prm 1 (String.length p_prm - 2) in
          fun
          [ ("ANTIQUOT_LOC", prm) ->
              if prm <> "" && prm.[0] = p_prm0 then
                if prm.[String.length prm - 1] = ':' then
                  let prm = String.sub prm 1 (String.length prm - 2) in
                  let kind = check_anti_loc prm in
                  if kind = p_prm || kind = anti_anti p_prm then prm
                  else raise Stream.Failure
                else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
        else
          let p_prm = String.sub p_prm 1 (String.length p_prm - 1) in
          fun
          [ ("ANTIQUOT_LOC", prm) ->
              if prm <> "" && prm.[0] = p_prm0 then
                if prm.[String.length prm - 1] = ':' then
                  raise Stream.Failure
                else
                  let prm = String.sub prm 1 (String.length prm - 1) in
                  let kind = check_anti_loc prm in
                  if kind = p_prm || kind = anti_anti p_prm then prm
                  else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
      else
        fun
        [ ("ANTIQUOT_LOC", prm) ->
            if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
              raise Stream.Failure
            else
              let kind = check_anti_loc prm in
              if kind = p_prm then prm
              else raise Stream.Failure
        | _ -> raise Stream.Failure ]
  | ("V", p_prm) ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = p_prm || kind = anti_anti p_prm then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V CHAR", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "chr" || kind = anti_anti "chr" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLAG", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "flag" || kind = anti_anti "flag" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLOAT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "flo" || kind = anti_anti "flo" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int" || kind = anti_anti "int" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_l", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int32" || kind = anti_anti "int32" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_L", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int64" || kind = anti_anti "int64" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_n", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "nativeint" || kind = anti_anti "nativeint" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "lid" || kind = anti_anti "lid" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIST", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "list" || kind = anti_anti "list" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V OPT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "opt" || kind = anti_anti "opt" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V QUESTIONIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '?' then
            if prm.[String.length prm - 1] = ':' then
              raise Stream.Failure
            else
              let prm = String.sub prm 1 (String.length prm - 1) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V QUESTIONIDENTCOLON", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '?' then
            if prm.[String.length prm - 1] = ':' then
              let prm = String.sub prm 1 (String.length prm - 2) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
            else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V STRING", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "str" || kind = anti_anti "str" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V TILDEIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '~' then
            if prm.[String.length prm - 1] = ':' then raise Stream.Failure
            else
              let prm = String.sub prm 1 (String.length prm - 1) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V TILDEIDENTCOLON", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '~' then
            if prm.[String.length prm - 1] = ':' then
              let prm = String.sub prm 1 (String.length prm - 2) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
            else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V UIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "uid" || kind = anti_anti "uid" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | tok -> tok_match tok ]
;

(* reinit the entry functions to take the new tok_match into account *)
Grammar.iter_entry Grammar.reinit_entry_functions
  (Grammar.Entry.obj Pcaml.expr);

value separate_locate s =
  let len = String.length s in
  if len > 0 && s.[0] = '@' then (String.sub s 1 (len - 1), True)
  else (s, False)
;

value apply_entry e me mp =
  let f s =
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse e) (Stream.of_string s)
  in
  let expr s =
    let (s, locate) = separate_locate s in
    me (f s)
  in
  let patt s =
    let (s, locate) = separate_locate s in
    let ast = mp (f s) in
    if locate then
      let (p, pl) =
        loop [] ast where rec loop pl =
          fun
          [ <:patt:< $p1$ $p2$ >> -> loop [(p2, loc) :: pl] p1
          | p -> (p, pl) ]
      in
      match (p,pl) with
      [ (_, [(<:patt< _ >>, loc) :: pl]) ->
          List.fold_left (fun p1 (p2, loc) -> <:patt< $p1$ $p2$ >>)
            <:patt< $p$ $lid:Ploc.name.val$ >> pl
      | (<:patt:< ( $list:pl$ ) >>, []) ->
        let pl = match pl with [
          [ <:patt< _ >> :: pl ] -> [ <:patt< $lid:Ploc.name.val$ >> :: pl ]
        | _ -> pl
        ] in
        <:patt< ( $list:pl$ ) >>
      | _ -> ast ]
    else ast
  in
  Quotation.ExAst (expr, patt)
;

List.iter
  (fun (q, f) -> Quotation.add q f)
  [
    ("attribute_body", apply_entry attribute_body_eoi Meta_E.attribute_body Meta_P.attribute_body);
    ("class_expr", apply_entry class_expr_eoi Meta_E.class_expr Meta_P.class_expr);
    ("class_sig_item", apply_entry class_sig_item_eoi Meta_E.class_sig_item Meta_P.class_sig_item);
    ("class_str_item", apply_entry class_str_item_eoi Meta_E.class_str_item Meta_P.class_str_item);
    ("class_type", apply_entry class_type_eoi Meta_E.class_type Meta_P.class_type);
    ("ctyp", apply_entry ctyp_eoi Meta_E.ctyp Meta_P.ctyp);
    ("expr", apply_entry expr_eoi Meta_E.expr Meta_P.expr);
    ("extended_longident", apply_entry extended_longident_eoi Meta_E.longid Meta_P.longid);
    ("extension_constructor", apply_entry extension_constructor_eoi Meta_E.extension_constructor Meta_P.extension_constructor);
    ("constructor", apply_entry constructor_eoi Meta_E.generic_constructor Meta_P.generic_constructor);
    ("longident", apply_entry longident_eoi Meta_E.longid Meta_P.longid);
    ("module_expr", apply_entry module_expr_eoi Meta_E.module_expr Meta_P.module_expr);
    ("module_type", apply_entry module_type_eoi Meta_E.module_type Meta_P.module_type);
    ("patt", apply_entry patt_eoi Meta_E.patt Meta_P.patt);
    ("poly_variant", apply_entry poly_variant_eoi Meta_E.poly_variant Meta_P.poly_variant);
    ("sig_item", apply_entry sig_item_eoi Meta_E.sig_item Meta_P.sig_item);
    ("str_item", apply_entry str_item_eoi Meta_E.str_item Meta_P.str_item);
    ("type_decl", apply_entry type_decl_eoi Meta_E.type_decl Meta_P.type_decl);
    ("type_extension", apply_entry type_extension_eoi Meta_E.type_extension Meta_P.type_extension);
    ("with_constr", apply_entry with_constr_eoi Meta_E.with_constr Meta_P.with_constr)
  ]
;

do {
  let expr_eoi = Grammar.Entry.create Pcaml.gram "expr_eoi" in
  EXTEND
    expr_eoi:
      [ [ a = ANTIQUOT_LOC; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then
              let a =
                let i = String.index a ':' in
                let i = String.index_from a (i + 1) ':' in
                let a = String.sub a (i + 1) (String.length a - i - 1) in
                Grammar.Entry.parse Pcaml.expr_eoi (Stream.of_string a)
              in
              <:expr< Ploc.VaAnt $anti:a$ >>
            else <:expr< failwith "antiquot" >>
        | e = Pcaml.expr; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then <:expr< Ploc.VaVal $anti:e$ >>
            else <:expr< $anti:e$ >> ] ]
    ;
  END;
  let expr s =
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse expr_eoi) (Stream.of_string s)
  in
  let patt_eoi = Grammar.Entry.create Pcaml.gram "patt_eoi" in
  EXTEND
    patt_eoi:
      [ [ a = ANTIQUOT_LOC; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then
              let a =
                let i = String.index a ':' in
                let i = String.index_from a (i + 1) ':' in
                let a = String.sub a (i + 1) (String.length a - i - 1) in
                Grammar.Entry.parse Pcaml.patt_eoi (Stream.of_string a)
              in
              <:patt< Ploc.VaAnt $anti:a$ >>
            else <:patt< _ >>
        | e = Pcaml.patt; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then <:patt< Ploc.VaVal $anti:e$ >>
            else <:patt< $anti:e$ >> ] ]
    ;
  END;
  let patt s =
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse patt_eoi) (Stream.of_string s)
  in
  Quotation.add "vala" (Quotation.ExAst (expr, patt));
};
