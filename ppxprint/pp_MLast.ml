(* camlp5r *)
module Ploc =
  struct
    include Ploc;
    value pp ppf x = Format.fprintf ppf "<loc>";
    type vala α =
      Ploc.vala α ==
        [ VaAnt of string
        | VaVal of α ][@@"deriving_inline" show;]
    ;
    value rec pp_vala : ! α . Fmt.t α → Fmt.t (vala α) =
      fun (type a) (tp_0 : Fmt.t a) (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ VaAnt v0 →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[<2>Pp_MLast.Ploc.VaAnt@ %a)@]"
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
                 v0
           | VaVal v0 →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[<2>Pp_MLast.Ploc.VaVal@ %a)@]" tp_0 v0 ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_vala : ! α . Fmt.t α → vala α → Stdlib.String.t =
      fun (type a) (tp_0 : Fmt.t a) arg →
        Format.asprintf "%a" (pp_vala tp_0) arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
  end
;
type loc = Ploc.t[@@"deriving_inline" show;];
value rec pp_loc : Fmt.t loc =
  fun (ofmt : Format.formatter) arg → Ploc.pp ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_loc : loc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_loc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type type_var =
  (Ploc.vala (option string) * option bool)[@@"deriving_inline" show;]
;
value rec pp_type_var : Fmt.t type_var =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) (v0, v1) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "(@[%a,@ %a@])"
         (Ploc.pp_vala
            (fun ofmt →
               fun
               [ None →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   const string "None" ofmt ()
               | Some arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "(Some %a)"
                     (fun ofmt arg →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "%S" arg)
                     arg ]))
         v0
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" Fmt.bool arg ])
         v1)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_type_var : type_var → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_type_var arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type class_infos α =
  MLast.class_infos α ==
    { ciLoc : loc;
      ciVir : Ploc.vala bool;
      ciPrm : (loc * Ploc.vala (list type_var));
      ciNam : Ploc.vala string;
      ciExp : α;
      ciAttributes : attributes }
and longid =
  MLast.longid ==
    [ LiAcc of loc and longid and Ploc.vala string
    | LiApp of loc and longid and longid
    | LiUid of loc and Ploc.vala string ]
and ctyp =
  MLast.ctyp ==
    [ TyAcc of loc and longid and Ploc.vala string
    | TyAli of loc and ctyp and ctyp
    | TyAny of loc
    | TyApp of loc and ctyp and ctyp
    | TyArr of loc and ctyp and ctyp
    | TyCls of loc and Ploc.vala longid_lident
    | TyLab of loc and Ploc.vala string and ctyp
    | TyLid of loc and Ploc.vala string
    | TyMan of loc and ctyp and Ploc.vala bool and ctyp
    | TyObj of
        loc and Ploc.vala (list (option string * ctyp * attributes)) and
          Ploc.vala bool
    | TyOlb of loc and Ploc.vala string and ctyp
    | TyOpn of loc
    | TyPck of loc and module_type
    | TyPol of loc and Ploc.vala (list string) and ctyp
    | TyPot of loc and Ploc.vala (list string) and ctyp
    | TyQuo of loc and Ploc.vala string
    | TyRec of
        loc and Ploc.vala (list (loc * string * bool * ctyp * attributes))
    | TySum of loc and Ploc.vala (list generic_constructor)
    | TyTup of loc and Ploc.vala (list ctyp)
    | TyVrn of
        loc and Ploc.vala (list poly_variant) and
          option (option (Ploc.vala (list string)))
    | TyXtr of loc and string and option (Ploc.vala ctyp)
    | TyAtt of loc and ctyp and attribute
    | TyExten of loc and attribute ]
and poly_variant =
  MLast.poly_variant ==
    [ PvTag of
        loc and Ploc.vala string and Ploc.vala bool and
          Ploc.vala (list ctyp) and attributes
    | PvInh of loc and ctyp ]
and patt =
  MLast.patt ==
    [ PaPfx of loc and longid and patt
    | PaLong of loc and longid
    | PaAli of loc and patt and patt
    | PaAnt of loc and patt
    | PaAny of loc
    | PaApp of loc and patt and patt
    | PaArr of loc and Ploc.vala (list patt)
    | PaChr of loc and Ploc.vala string
    | PaExc of loc and patt
    | PaFlo of loc and Ploc.vala string
    | PaInt of loc and Ploc.vala string and string
    | PaLab of loc and Ploc.vala (list (patt * Ploc.vala (option patt)))
    | PaLaz of loc and patt
    | PaLid of loc and Ploc.vala string
    | PaNty of loc and Ploc.vala string
    | PaOlb of loc and patt and Ploc.vala (option expr)
    | PaOrp of loc and patt and patt
    | PaRec of loc and Ploc.vala (list (patt * patt))
    | PaRng of loc and patt and patt
    | PaStr of loc and Ploc.vala string
    | PaTup of loc and Ploc.vala (list patt)
    | PaTyc of loc and patt and ctyp
    | PaTyp of loc and Ploc.vala longid_lident
    | PaUnp of
        loc and Ploc.vala (option (Ploc.vala string)) and option module_type
    | PaVrn of loc and Ploc.vala string
    | PaXtr of loc and string and option (Ploc.vala patt)
    | PaAtt of loc and patt and attribute
    | PaExten of loc and attribute ]
and expr =
  MLast.expr ==
    [ ExAcc of loc and expr and expr
    | ExAnt of loc and expr
    | ExApp of loc and expr and expr
    | ExAre of loc and Ploc.vala string and expr and Ploc.vala (list expr)
    | ExArr of loc and Ploc.vala (list expr)
    | ExAsr of loc and expr
    | ExAss of loc and expr and expr
    | ExBae of loc and Ploc.vala string and expr and Ploc.vala (list expr)
    | ExChr of loc and Ploc.vala string
    | ExCoe of loc and expr and option ctyp and ctyp
    | ExFlo of loc and Ploc.vala string
    | ExFor of
        loc and patt and expr and expr and Ploc.vala bool and
          Ploc.vala (list expr)
    | ExFun of loc and Ploc.vala (list case_branch)
    | ExIfe of loc and expr and expr and expr
    | ExInt of loc and Ploc.vala string and string
    | ExLab of loc and Ploc.vala (list (patt * Ploc.vala (option expr)))
    | ExLaz of loc and expr
    | ExLet of
        loc and Ploc.vala bool and
          Ploc.vala (list (patt * expr * attributes)) and expr
    | ExLEx of
        loc and Ploc.vala string and Ploc.vala (list ctyp) and expr and
          attributes
    | ExLid of loc and Ploc.vala string
    | ExLmd of
        loc and Ploc.vala (option (Ploc.vala string)) and module_expr and expr
    | ExLop of loc and Ploc.vala bool and module_expr and expr
    | ExMat of loc and expr and Ploc.vala (list case_branch)
    | ExNew of loc and Ploc.vala longid_lident
    | ExObj of
        loc and Ploc.vala (option patt) and Ploc.vala (list class_str_item)
    | ExOlb of loc and patt and Ploc.vala (option expr)
    | ExOvr of loc and Ploc.vala (list (string * expr))
    | ExPck of loc and module_expr and option module_type
    | ExRec of loc and Ploc.vala (list (patt * expr)) and option expr
    | ExSeq of loc and Ploc.vala (list expr)
    | ExSnd of loc and expr and Ploc.vala string
    | ExSte of loc and Ploc.vala string and expr and Ploc.vala (list expr)
    | ExStr of loc and Ploc.vala string
    | ExTry of loc and expr and Ploc.vala (list case_branch)
    | ExTup of loc and Ploc.vala (list expr)
    | ExTyc of loc and expr and ctyp
    | ExUid of loc and Ploc.vala string
    | ExVrn of loc and Ploc.vala string
    | ExWhi of loc and expr and Ploc.vala (list expr)
    | ExXtr of loc and string and option (Ploc.vala expr)
    | ExAtt of loc and expr and attribute
    | ExExten of loc and attribute
    | ExUnr of loc ]
and case_branch = (patt * Ploc.vala (option expr) * expr)
and module_type =
  MLast.module_type ==
    [ MtLong of loc and longid
    | MtLongLid of loc and longid and Ploc.vala string
    | MtLid of loc and Ploc.vala string
    | MtFun of
        loc and
          Ploc.vala
            (option (Ploc.vala (option (Ploc.vala string)) * module_type)) and
          module_type
    | MtQuo of loc and Ploc.vala string
    | MtSig of loc and Ploc.vala (list sig_item)
    | MtTyo of loc and module_expr
    | MtWit of loc and module_type and Ploc.vala (list with_constr)
    | MtXtr of loc and string and option (Ploc.vala module_type)
    | MtAtt of loc and module_type and attribute
    | MtExten of loc and attribute ]
and functor_parameter =
  option (Ploc.vala (option (Ploc.vala string)) * module_type)
and sig_item =
  MLast.sig_item ==
    [ SgCls of loc and Ploc.vala (list (class_infos class_type))
    | SgClt of loc and Ploc.vala (list (class_infos class_type))
    | SgDcl of loc and Ploc.vala (list sig_item)
    | SgDir of loc and Ploc.vala string and Ploc.vala (option expr)
    | SgExc of loc and generic_constructor and attributes
    | SgExt of
        loc and Ploc.vala string and ctyp and Ploc.vala (list string) and
          attributes
    | SgInc of loc and module_type and attributes
    | SgMod of
        loc and Ploc.vala bool and
          Ploc.vala
            (list
               (Ploc.vala (option (Ploc.vala string)) * module_type *
                attributes))
    | SgMty of loc and Ploc.vala string and module_type and attributes
    | SgMtyAbs of loc and Ploc.vala string and attributes
    | SgMtyAlias of
        loc and Ploc.vala string and Ploc.vala longid and attributes
    | SgModSubst of loc and Ploc.vala string and longid and attributes
    | SgOpn of loc and longid and attributes
    | SgTyp of loc and Ploc.vala bool and Ploc.vala (list type_decl)
    | SgTypExten of loc and type_extension
    | SgUse of loc and Ploc.vala string and Ploc.vala (list (sig_item * loc))
    | SgVal of loc and Ploc.vala string and ctyp and attributes
    | SgXtr of loc and string and option (Ploc.vala sig_item)
    | SgFlAtt of loc and attribute
    | SgExten of loc and attribute and attributes ]
and with_constr =
  MLast.with_constr ==
    [ WcMod of loc and Ploc.vala longid and module_expr
    | WcMos of loc and Ploc.vala longid and module_expr
    | WcTyp of
        loc and Ploc.vala longid_lident and Ploc.vala (list type_var) and
          Ploc.vala bool and ctyp
    | WcTys of
        loc and Ploc.vala longid_lident and Ploc.vala (list type_var) and ctyp ]
and module_expr =
  MLast.module_expr ==
    [ MeAcc of loc and module_expr and module_expr
    | MeApp of loc and module_expr and module_expr
    | MeFun of
        loc and
          Ploc.vala
            (option (Ploc.vala (option (Ploc.vala string)) * module_type)) and
          module_expr
    | MeStr of loc and Ploc.vala (list str_item)
    | MeTyc of loc and module_expr and module_type
    | MeUid of loc and Ploc.vala string
    | MeUnp of loc and expr and option module_type and option module_type
    | MeXtr of loc and string and option (Ploc.vala module_expr)
    | MeAtt of loc and module_expr and attribute
    | MeExten of loc and attribute ]
and str_item =
  MLast.str_item ==
    [ StCls of loc and Ploc.vala (list (class_infos class_expr))
    | StClt of loc and Ploc.vala (list (class_infos class_type))
    | StDcl of loc and Ploc.vala (list str_item)
    | StDir of loc and Ploc.vala string and Ploc.vala (option expr)
    | StExc of loc and Ploc.vala extension_constructor and attributes
    | StExp of loc and expr and attributes
    | StExt of
        loc and Ploc.vala string and ctyp and Ploc.vala (list string) and
          attributes
    | StInc of loc and module_expr and attributes
    | StMod of
        loc and Ploc.vala bool and
          Ploc.vala
            (list
               (Ploc.vala (option (Ploc.vala string)) * module_expr *
                attributes))
    | StMty of loc and Ploc.vala string and module_type and attributes
    | StMtyAbs of loc and Ploc.vala string and attributes
    | StOpn of loc and Ploc.vala bool and module_expr and attributes
    | StTyp of loc and Ploc.vala bool and Ploc.vala (list type_decl)
    | StTypExten of loc and type_extension
    | StUse of loc and Ploc.vala string and Ploc.vala (list (str_item * loc))
    | StVal of
        loc and Ploc.vala bool and Ploc.vala (list (patt * expr * attributes))
    | StXtr of loc and string and option (Ploc.vala str_item)
    | StFlAtt of loc and attribute
    | StExten of loc and attribute and attributes ]
and type_decl =
  MLast.type_decl ==
    { tdIsDecl : bool;
      tdNam : Ploc.vala (loc * Ploc.vala string);
      tdPrm : Ploc.vala (list type_var);
      tdPrv : Ploc.vala bool;
      tdDef : ctyp;
      tdCon : Ploc.vala (list (ctyp * ctyp));
      tdAttributes : attributes }
and generic_constructor =
  (loc * Ploc.vala string * Ploc.vala (list ctyp) * option ctyp * attributes)
and extension_constructor =
  MLast.extension_constructor ==
    [ EcTuple of generic_constructor
    | EcRebind of Ploc.vala string and Ploc.vala longid and attributes ]
and type_extension =
  MLast.type_extension ==
    { teNam : Ploc.vala longid_lident;
      tePrm : Ploc.vala (list type_var);
      tePrv : Ploc.vala bool;
      teECs : Ploc.vala (list extension_constructor);
      teAttributes : attributes }
and class_type =
  MLast.class_type ==
    [ CtLongLid of loc and longid and Ploc.vala string
    | CtLid of loc and Ploc.vala string
    | CtLop of loc and Ploc.vala bool and longid and class_type
    | CtCon of loc and class_type and Ploc.vala (list ctyp)
    | CtFun of loc and ctyp and class_type
    | CtSig of
        loc and Ploc.vala (option ctyp) and Ploc.vala (list class_sig_item)
    | CtXtr of loc and string and option (Ploc.vala class_type)
    | CtAtt of loc and class_type and attribute
    | CtExten of loc and attribute ]
and class_sig_item =
  MLast.class_sig_item ==
    [ CgCtr of loc and ctyp and ctyp and attributes
    | CgDcl of loc and Ploc.vala (list class_sig_item)
    | CgInh of loc and class_type and attributes
    | CgMth of
        loc and Ploc.vala bool and Ploc.vala string and ctyp and attributes
    | CgVal of
        loc and Ploc.vala bool and Ploc.vala bool and Ploc.vala string and
          ctyp and attributes
    | CgVir of
        loc and Ploc.vala bool and Ploc.vala string and ctyp and attributes
    | CgFlAtt of loc and attribute
    | CgExten of loc and attribute ]
and class_expr =
  MLast.class_expr ==
    [ CeApp of loc and class_expr and expr
    | CeCon of loc and Ploc.vala longid_lident and Ploc.vala (list ctyp)
    | CeFun of loc and patt and class_expr
    | CeLet of
        loc and Ploc.vala bool and
          Ploc.vala (list (patt * expr * attributes)) and class_expr
    | CeLop of loc and Ploc.vala bool and longid and class_expr
    | CeStr of
        loc and Ploc.vala (option patt) and Ploc.vala (list class_str_item)
    | CeTyc of loc and class_expr and class_type
    | CeXtr of loc and string and option (Ploc.vala class_expr)
    | CeAtt of loc and class_expr and attribute
    | CeExten of loc and attribute ]
and class_str_item =
  MLast.class_str_item ==
    [ CrCtr of loc and ctyp and ctyp and attributes
    | CrDcl of loc and Ploc.vala (list class_str_item)
    | CrInh of
        loc and Ploc.vala bool and class_expr and
          Ploc.vala (option string) and attributes
    | CrIni of loc and expr and attributes
    | CrMth of
        loc and Ploc.vala bool and Ploc.vala bool and Ploc.vala string and
          Ploc.vala (option ctyp) and expr and attributes
    | CrVal of
        loc and Ploc.vala bool and Ploc.vala bool and Ploc.vala string and
          expr and attributes
    | CrVav of
        loc and Ploc.vala bool and Ploc.vala string and ctyp and attributes
    | CrVir of
        loc and Ploc.vala bool and Ploc.vala string and ctyp and attributes
    | CrFlAtt of loc and attribute
    | CrExten of loc and attribute ]
and longid_lident = (option longid * Ploc.vala string)
and payload =
  MLast.payload ==
    [ StAttr of loc and Ploc.vala (list str_item)
    | SiAttr of loc and Ploc.vala (list sig_item)
    | TyAttr of loc and Ploc.vala ctyp
    | PaAttr of loc and Ploc.vala patt and option (Ploc.vala expr) ]
and attribute_body = (Ploc.vala (loc * string) * payload)
and attribute = Ploc.vala attribute_body
and attributes_no_anti = list attribute
and attributes = Ploc.vala attributes_no_anti[@@"deriving_inline" show;];
value rec pp_class_infos : ! α . Fmt.t α → Fmt.t (class_infos α) =
  fun (type a) (tp_0 : Fmt.t a) (ofmt : Format.formatter) arg →
    (fun ofmt
         ({ciLoc = v_ciLoc; ciVir = v_ciVir; ciPrm = v_ciPrm; ciNam = v_ciNam;
           ciExp = v_ciExp; ciAttributes = v_ciAttributes} :
          class_infos a) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Pp_MLast.ciLoc =@ %a@];@ @[ciVir =@ %a@];@ @[ciPrm =@ %a@];@ @[ciNam =@ %a@];@ @[ciExp =@ %a@];@ @[ciAttributes =@ %a@] }@]"
         pp_loc v_ciLoc (Ploc.pp_vala Fmt.bool) v_ciVir
         (fun (ofmt : Format.formatter) (v0, v1) →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "(@[%a,@ %a@])" pp_loc v0
              (Ploc.pp_vala
                 (fun (ofmt : Format.formatter) arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_type_var)
                      arg))
              v1)
         v_ciPrm
         (Ploc.pp_vala
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_ciNam tp_0 v_ciExp pp_attributes v_ciAttributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_infos : ! α . Fmt.t α → class_infos α → Stdlib.String.t =
  fun (type a) (tp_0 : Fmt.t a) arg →
    Format.asprintf "%a" (pp_class_infos tp_0) arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_longid : Fmt.t longid =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ LiAcc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.LiAcc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_longid v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2
       | LiApp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.LiApp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_longid v1 pp_longid v2
       | LiUid v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.LiUid@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_longid : longid → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_longid arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_ctyp : Fmt.t ctyp =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ TyAcc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyAcc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_longid v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2
       | TyAli v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyAli@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_ctyp v1 pp_ctyp v2
       | TyAny v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyAny@ %a)@]" pp_loc v0
       | TyApp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyApp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_ctyp v1 pp_ctyp v2
       | TyArr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyArr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_ctyp v1 pp_ctyp v2
       | TyCls v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyCls@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_longid_lident) v1
       | TyLab v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyLab@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_ctyp v2
       | TyLid v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyLid@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | TyMan v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyMan@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             pp_ctyp v1 (Ploc.pp_vala Fmt.bool) v2 pp_ctyp v3
       | TyObj v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyObj@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1, v2) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a,@ %a@])"
                             (fun ofmt →
                                fun
                                [ None →
                                    let open Ppxprint_runtime.Runtime.Fmt in
                                    const string "None" ofmt ()
                                | Some arg →
                                    let open Ppxprint_runtime.Runtime.Fmt in
                                    pf ofmt "(Some %a)"
                                      (fun ofmt arg →
                                         let open Ppxprint_runtime.Runtime.Fmt
                                         in
                                         pf ofmt "%S" arg)
                                      arg ])
                             v0 pp_ctyp v1 pp_attributes v2))
                     arg))
             v1 (Ploc.pp_vala Fmt.bool) v2
       | TyOlb v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyOlb@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_ctyp v2
       | TyOpn v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyOpn@ %a)@]" pp_loc v0
       | TyPck v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyPck@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_module_type v1
       | TyPol v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyPol@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun ofmt arg →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "%S" arg))
                     arg))
             v1 pp_ctyp v2
       | TyPot v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyPot@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun ofmt arg →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "%S" arg))
                     arg))
             v1 pp_ctyp v2
       | TyQuo v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyQuo@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | TyRec v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyRec@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1, v2, v3, v4) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a,@ %a,@ %a,@ %a@])" pp_loc v0
                             (fun ofmt arg →
                                let open Ppxprint_runtime.Runtime.Fmt in
                                pf ofmt "%S" arg)
                             v1 Fmt.bool v2 pp_ctyp v3 pp_attributes v4))
                     arg))
             v1
       | TySum v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TySum@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} pp_generic_constructor) arg))
             v1
       | TyTup v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyTup@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_ctyp) arg))
             v1
       | TyVrn v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyVrn@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} pp_poly_variant) arg))
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (fun ofmt →
                         fun
                         [ None →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             const string "None" ofmt ()
                         | Some arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "(Some %a)"
                               (Ploc.pp_vala
                                  (fun (ofmt : Format.formatter) arg →
                                     let open Ppxprint_runtime.Runtime.Fmt in
                                     pf ofmt "@[<2>[%a@,]@]"
                                       (list ~{sep = semi}
                                          (fun ofmt arg →
                                             let open Ppxprint_runtime.Runtime.Fmt
                                             in
                                             pf ofmt "%S" arg))
                                       arg))
                               arg ])
                      arg ])
             v2
       | TyXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_ctyp) arg ])
             v2
       | TyAtt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyAtt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_ctyp v1 pp_attribute v2
       | TyExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_ctyp : ctyp → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_ctyp arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_poly_variant : Fmt.t poly_variant =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ PvTag v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PvTag@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 (Ploc.pp_vala Fmt.bool) v2
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_ctyp) arg))
             v3 pp_attributes v4
       | PvInh v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PvInh@ (@,%a,@ %a@,))@]" pp_loc v0 pp_ctyp
             v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_poly_variant : poly_variant → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_poly_variant arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_patt : Fmt.t patt =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ PaPfx v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaPfx@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_longid v1 pp_patt v2
       | PaLong v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaLong@ (@,%a,@ %a@,))@]" pp_loc v0 pp_longid
             v1
       | PaAli v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaAli@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1 pp_patt v2
       | PaAnt v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaAnt@ (@,%a,@ %a@,))@]" pp_loc v0 pp_patt v1
       | PaAny v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaAny@ %a)@]" pp_loc v0
       | PaApp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaApp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1 pp_patt v2
       | PaArr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaArr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_patt) arg))
             v1
       | PaChr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaChr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | PaExc v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaExc@ (@,%a,@ %a@,))@]" pp_loc v0 pp_patt v1
       | PaFlo v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaFlo@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | PaInt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaInt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v2
       | PaLab v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaLab@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a@])" pp_patt v0
                             (Ploc.pp_vala
                                (fun ofmt →
                                   fun
                                   [ None →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       const string "None" ofmt ()
                                   | Some arg →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       pf ofmt "(Some %a)" pp_patt arg ]))
                             v1))
                     arg))
             v1
       | PaLaz v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaLaz@ (@,%a,@ %a@,))@]" pp_loc v0 pp_patt v1
       | PaLid v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaLid@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | PaNty v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaNty@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | PaOlb v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaOlb@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)" pp_expr arg ]))
             v2
       | PaOrp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaOrp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1 pp_patt v2
       | PaRec v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaRec@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a@])" pp_patt v0 pp_patt v1))
                     arg))
             v1
       | PaRng v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaRng@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1 pp_patt v2
       | PaStr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaStr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | PaTup v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaTup@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_patt) arg))
             v1
       | PaTyc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaTyc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1 pp_ctyp v2
       | PaTyp v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaTyp@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_longid_lident) v1
       | PaUnp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaUnp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)"
                         (Ploc.pp_vala
                            (fun ofmt arg →
                               let open Ppxprint_runtime.Runtime.Fmt in
                               pf ofmt "%S" arg))
                         arg ]))
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_module_type arg ])
             v2
       | PaVrn v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaVrn@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | PaXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_patt) arg ])
             v2
       | PaAtt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaAtt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1 pp_attribute v2
       | PaExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_patt : patt → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_patt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_expr : Fmt.t expr =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ ExAcc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExAcc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1 pp_expr v2
       | ExAnt v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExAnt@ (@,%a,@ %a@,))@]" pp_loc v0 pp_expr v1
       | ExApp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExApp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1 pp_expr v2
       | ExAre v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExAre@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_expr v2
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expr) arg))
             v3
       | ExArr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExArr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expr) arg))
             v1
       | ExAsr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExAsr@ (@,%a,@ %a@,))@]" pp_loc v0 pp_expr v1
       | ExAss v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExAss@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1 pp_expr v2
       | ExBae v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExBae@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_expr v2
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expr) arg))
             v3
       | ExChr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExChr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | ExCoe v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExCoe@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_ctyp arg ])
             v2 pp_ctyp v3
       | ExFlo v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExFlo@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | ExFor v0 v1 v2 v3 v4 v5 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExFor@ (@,%a,@ %a,@ %a,@ %a,@ %a,@ %a@,))@]"
             pp_loc v0 pp_patt v1 pp_expr v2 pp_expr v3
             (Ploc.pp_vala Fmt.bool) v4
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expr) arg))
             v5
       | ExFun v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExFun@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_case_branch)
                     arg))
             v1
       | ExIfe v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExIfe@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1 pp_expr v2 pp_expr v3
       | ExInt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExInt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v2
       | ExLab v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExLab@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a@])" pp_patt v0
                             (Ploc.pp_vala
                                (fun ofmt →
                                   fun
                                   [ None →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       const string "None" ofmt ()
                                   | Some arg →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       pf ofmt "(Some %a)" pp_expr arg ]))
                             v1))
                     arg))
             v1
       | ExLaz v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExLaz@ (@,%a,@ %a@,))@]" pp_loc v0 pp_expr v1
       | ExLet v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExLet@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1, v2) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a,@ %a@])" pp_patt v0 pp_expr v1
                             pp_attributes v2))
                     arg))
             v2 pp_expr v3
       | ExLEx v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExLEx@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_ctyp) arg))
             v2 pp_expr v3 pp_attributes v4
       | ExLid v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExLid@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | ExLmd v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExLmd@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)"
                         (Ploc.pp_vala
                            (fun ofmt arg →
                               let open Ppxprint_runtime.Runtime.Fmt in
                               pf ofmt "%S" arg))
                         arg ]))
             v1 pp_module_expr v2 pp_expr v3
       | ExLop v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExLop@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1 pp_module_expr v2 pp_expr v3
       | ExMat v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExMat@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_case_branch)
                     arg))
             v2
       | ExNew v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExNew@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_longid_lident) v1
       | ExObj v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExObj@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)" pp_patt arg ]))
             v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} pp_class_str_item) arg))
             v2
       | ExOlb v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExOlb@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)" pp_expr arg ]))
             v2
       | ExOvr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExOvr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a@])"
                             (fun ofmt arg →
                                let open Ppxprint_runtime.Runtime.Fmt in
                                pf ofmt "%S" arg)
                             v0 pp_expr v1))
                     arg))
             v1
       | ExPck v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExPck@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_expr v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_module_type arg ])
             v2
       | ExRec v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExRec@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a@])" pp_patt v0 pp_expr v1))
                     arg))
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_expr arg ])
             v2
       | ExSeq v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExSeq@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expr) arg))
             v1
       | ExSnd v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExSnd@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2
       | ExSte v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExSte@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_expr v2
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expr) arg))
             v3
       | ExStr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExStr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | ExTry v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExTry@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_case_branch)
                     arg))
             v2
       | ExTup v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExTup@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expr) arg))
             v1
       | ExTyc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExTyc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1 pp_ctyp v2
       | ExUid v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExUid@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | ExVrn v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExVrn@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | ExWhi v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExWhi@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expr) arg))
             v2
       | ExXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_expr) arg ])
             v2
       | ExAtt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExAtt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1 pp_attribute v2
       | ExExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1
       | ExUnr v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.ExUnr@ %a)@]" pp_loc v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_expr : expr → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_expr arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_case_branch : Fmt.t case_branch =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) (v0, v1, v2) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "(@[%a,@ %a,@ %a@])" pp_patt v0
         (Ploc.pp_vala
            (fun ofmt →
               fun
               [ None →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   const string "None" ofmt ()
               | Some arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "(Some %a)" pp_expr arg ]))
         v1 pp_expr v2)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_case_branch : case_branch → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_case_branch arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_type : Fmt.t module_type =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ MtLong v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtLong@ (@,%a,@ %a@,))@]" pp_loc v0 pp_longid
             v1
       | MtLongLid v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtLongLid@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_longid v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2
       | MtLid v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtLid@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | MtFun v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtFun@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)"
                         (fun (ofmt : Format.formatter) (v0, v1) →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            pf ofmt "(@[%a,@ %a@])"
                              (Ploc.pp_vala
                                 (fun ofmt →
                                    fun
                                    [ None →
                                        let open Ppxprint_runtime.Runtime.Fmt
                                        in
                                        const string "None" ofmt ()
                                    | Some arg →
                                        let open Ppxprint_runtime.Runtime.Fmt
                                        in
                                        pf ofmt "(Some %a)"
                                          (Ploc.pp_vala
                                             (fun ofmt arg →
                                                let open Ppxprint_runtime.Runtime.Fmt
                                                in
                                                pf ofmt "%S" arg))
                                          arg ]))
                              v0 pp_module_type v1)
                         arg ]))
             v1 pp_module_type v2
       | MtQuo v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtQuo@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | MtSig v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtSig@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_sig_item)
                     arg))
             v1
       | MtTyo v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtTyo@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_module_expr v1
       | MtWit v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtWit@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_type v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_with_constr)
                     arg))
             v2
       | MtXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_module_type) arg ])
             v2
       | MtAtt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtAtt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_type v1 pp_attribute v2
       | MtExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MtExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_type : module_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_functor_parameter : Fmt.t functor_parameter =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ None →
           let open Ppxprint_runtime.Runtime.Fmt in
           const string "None" ofmt ()
       | Some arg →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(Some %a)"
             (fun (ofmt : Format.formatter) (v0, v1) →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(@[%a,@ %a@])"
                  (Ploc.pp_vala
                     (fun ofmt →
                        fun
                        [ None →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            const string "None" ofmt ()
                        | Some arg →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            pf ofmt "(Some %a)"
                              (Ploc.pp_vala
                                 (fun ofmt arg →
                                    let open Ppxprint_runtime.Runtime.Fmt in
                                    pf ofmt "%S" arg))
                              arg ]))
                  v0 pp_module_type v1)
             arg ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_functor_parameter : functor_parameter → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_functor_parameter arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_sig_item : Fmt.t sig_item =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ SgCls v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgCls@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} (pp_class_infos pp_class_type)) arg))
             v1
       | SgClt v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgClt@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} (pp_class_infos pp_class_type)) arg))
             v1
       | SgDcl v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgDcl@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_sig_item)
                     arg))
             v1
       | SgDir v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgDir@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)" pp_expr arg ]))
             v2
       | SgExc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgExc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_generic_constructor v1 pp_attributes v2
       | SgExt v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgExt@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_ctyp v2
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun ofmt arg →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "%S" arg))
                     arg))
             v3 pp_attributes v4
       | SgInc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgInc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_type v1 pp_attributes v2
       | SgMod v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgMod@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1, v2) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a,@ %a@])"
                             (Ploc.pp_vala
                                (fun ofmt →
                                   fun
                                   [ None →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       const string "None" ofmt ()
                                   | Some arg →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       pf ofmt "(Some %a)"
                                         (Ploc.pp_vala
                                            (fun ofmt arg →
                                               let open Ppxprint_runtime.Runtime.Fmt
                                               in
                                               pf ofmt "%S" arg))
                                         arg ]))
                             v0 pp_module_type v1 pp_attributes v2))
                     arg))
             v2
       | SgMty v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgMty@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_module_type v2 pp_attributes v3
       | SgMtyAbs v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgMtyAbs@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_attributes v2
       | SgMtyAlias v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgMtyAlias@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 (Ploc.pp_vala pp_longid) v2 pp_attributes v3
       | SgModSubst v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgModSubst@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_longid v2 pp_attributes v3
       | SgOpn v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgOpn@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_longid v1 pp_attributes v2
       | SgTyp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgTyp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_type_decl)
                     arg))
             v2
       | SgTypExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgTypExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_type_extension v1
       | SgUse v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgUse@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a@])" pp_sig_item v0 pp_loc v1))
                     arg))
             v2
       | SgVal v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgVal@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_ctyp v2 pp_attributes v3
       | SgXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_sig_item) arg ])
             v2
       | SgFlAtt v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgFlAtt@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1
       | SgExten v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SgExten@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 pp_attributes v2 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_sig_item : sig_item → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_sig_item arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_with_constr : Fmt.t with_constr =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ WcMod v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.WcMod@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_longid) v1 pp_module_expr v2
       | WcMos v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.WcMos@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_longid) v1 pp_module_expr v2
       | WcTyp v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.WcTyp@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0 (Ploc.pp_vala pp_longid_lident) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_type_var)
                     arg))
             v2 (Ploc.pp_vala Fmt.bool) v3 pp_ctyp v4
       | WcTys v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.WcTys@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_longid_lident) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_type_var)
                     arg))
             v2 pp_ctyp v3 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_with_constr : with_constr → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_with_constr arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_expr : Fmt.t module_expr =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ MeAcc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeAcc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_expr v1 pp_module_expr v2
       | MeApp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeApp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_expr v1 pp_module_expr v2
       | MeFun v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeFun@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)"
                         (fun (ofmt : Format.formatter) (v0, v1) →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            pf ofmt "(@[%a,@ %a@])"
                              (Ploc.pp_vala
                                 (fun ofmt →
                                    fun
                                    [ None →
                                        let open Ppxprint_runtime.Runtime.Fmt
                                        in
                                        const string "None" ofmt ()
                                    | Some arg →
                                        let open Ppxprint_runtime.Runtime.Fmt
                                        in
                                        pf ofmt "(Some %a)"
                                          (Ploc.pp_vala
                                             (fun ofmt arg →
                                                let open Ppxprint_runtime.Runtime.Fmt
                                                in
                                                pf ofmt "%S" arg))
                                          arg ]))
                              v0 pp_module_type v1)
                         arg ]))
             v1 pp_module_expr v2
       | MeStr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeStr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_str_item)
                     arg))
             v1
       | MeTyc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeTyc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_expr v1 pp_module_type v2
       | MeUid v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeUid@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | MeUnp v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeUnp@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_module_type arg ])
             v2
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_module_type arg ])
             v3
       | MeXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_module_expr) arg ])
             v2
       | MeAtt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeAtt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_expr v1 pp_attribute v2
       | MeExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.MeExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_expr : module_expr → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_expr arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_str_item : Fmt.t str_item =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ StCls v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StCls@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} (pp_class_infos pp_class_expr)) arg))
             v1
       | StClt v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StClt@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} (pp_class_infos pp_class_type)) arg))
             v1
       | StDcl v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StDcl@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_str_item)
                     arg))
             v1
       | StDir v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StDir@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)" pp_expr arg ]))
             v2
       | StExc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StExc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_extension_constructor) v1 pp_attributes v2
       | StExp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StExp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1 pp_attributes v2
       | StExt v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StExt@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_ctyp v2
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun ofmt arg →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "%S" arg))
                     arg))
             v3 pp_attributes v4
       | StInc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StInc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_module_expr v1 pp_attributes v2
       | StMod v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StMod@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1, v2) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a,@ %a@])"
                             (Ploc.pp_vala
                                (fun ofmt →
                                   fun
                                   [ None →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       const string "None" ofmt ()
                                   | Some arg →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       pf ofmt "(Some %a)"
                                         (Ploc.pp_vala
                                            (fun ofmt arg →
                                               let open Ppxprint_runtime.Runtime.Fmt
                                               in
                                               pf ofmt "%S" arg))
                                         arg ]))
                             v0 pp_module_expr v1 pp_attributes v2))
                     arg))
             v2
       | StMty v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StMty@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_module_type v2 pp_attributes v3
       | StMtyAbs v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StMtyAbs@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1 pp_attributes v2
       | StOpn v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StOpn@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1 pp_module_expr v2 pp_attributes v3
       | StTyp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StTyp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_type_decl)
                     arg))
             v2
       | StTypExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StTypExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_type_extension v1
       | StUse v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StUse@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a@])" pp_str_item v0 pp_loc v1))
                     arg))
             v2
       | StVal v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StVal@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1, v2) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a,@ %a@])" pp_patt v0 pp_expr v1
                             pp_attributes v2))
                     arg))
             v2
       | StXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_str_item) arg ])
             v2
       | StFlAtt v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StFlAtt@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1
       | StExten v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StExten@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 pp_attributes v2 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_str_item : str_item → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_str_item arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_type_decl : Fmt.t type_decl =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({tdIsDecl = v_tdIsDecl; tdNam = v_tdNam; tdPrm = v_tdPrm;
           tdPrv = v_tdPrv; tdDef = v_tdDef; tdCon = v_tdCon;
           tdAttributes = v_tdAttributes} :
          type_decl) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[MLast.tdIsDecl =@ %a@];@ @[tdNam =@ %a@];@ @[tdPrm =@ %a@];@ @[tdPrv =@ %a@];@ @[tdDef =@ %a@];@ @[tdCon =@ %a@];@ @[tdAttributes =@ %a@] }@]"
         Fmt.bool v_tdIsDecl
         (Ploc.pp_vala
            (fun (ofmt : Format.formatter) (v0, v1) →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[%a,@ %a@])" pp_loc v0
                 (Ploc.pp_vala
                    (fun ofmt arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "%S" arg))
                 v1))
         v_tdNam
         (Ploc.pp_vala
            (fun (ofmt : Format.formatter) arg →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_type_var) arg))
         v_tdPrm (Ploc.pp_vala Fmt.bool) v_tdPrv pp_ctyp v_tdDef
         (Ploc.pp_vala
            (fun (ofmt : Format.formatter) arg →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>[%a@,]@]"
                 (list ~{sep = semi}
                    (fun (ofmt : Format.formatter) (v0, v1) →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(@[%a,@ %a@])" pp_ctyp v0 pp_ctyp v1))
                 arg))
         v_tdCon pp_attributes v_tdAttributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_type_decl : type_decl → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_type_decl arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_generic_constructor : Fmt.t generic_constructor =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) (v0, v1, v2, v3, v4) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "(@[%a,@ %a,@ %a,@ %a,@ %a@])" pp_loc v0
         (Ploc.pp_vala
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v1
         (Ploc.pp_vala
            (fun (ofmt : Format.formatter) arg →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_ctyp) arg))
         v2
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" pp_ctyp arg ])
         v3 pp_attributes v4)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_generic_constructor : generic_constructor → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_generic_constructor arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_extension_constructor : Fmt.t extension_constructor =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ EcTuple v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.EcTuple@ %a)@]" pp_generic_constructor v0
       | EcRebind v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.EcRebind@ (@,%a,@ %a,@ %a@,))@]"
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v0 (Ploc.pp_vala pp_longid) v1 pp_attributes v2 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_extension_constructor : extension_constructor → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_extension_constructor arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_type_extension : Fmt.t type_extension =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({teNam = v_teNam; tePrm = v_tePrm; tePrv = v_tePrv; teECs = v_teECs;
           teAttributes = v_teAttributes} :
          type_extension) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[MLast.teNam =@ %a@];@ @[tePrm =@ %a@];@ @[tePrv =@ %a@];@ @[teECs =@ %a@];@ @[teAttributes =@ %a@] }@]"
         (Ploc.pp_vala pp_longid_lident) v_teNam
         (Ploc.pp_vala
            (fun (ofmt : Format.formatter) arg →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_type_var) arg))
         v_tePrm (Ploc.pp_vala Fmt.bool) v_tePrv
         (Ploc.pp_vala
            (fun (ofmt : Format.formatter) arg →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>[%a@,]@]"
                 (list ~{sep = semi} pp_extension_constructor) arg))
         v_teECs pp_attributes v_teAttributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_type_extension : type_extension → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_type_extension arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_type : Fmt.t class_type =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ CtLongLid v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtLongLid@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_longid v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2
       | CtLid v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtLid@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | CtLop v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtLop@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1 pp_longid v2 pp_class_type v3
       | CtCon v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtCon@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_class_type v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_ctyp) arg))
             v2
       | CtFun v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtFun@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_ctyp v1 pp_class_type v2
       | CtSig v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtSig@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)" pp_ctyp arg ]))
             v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} pp_class_sig_item) arg))
             v2
       | CtXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_class_type) arg ])
             v2
       | CtAtt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtAtt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_class_type v1 pp_attribute v2
       | CtExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CtExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_type : class_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_sig_item : Fmt.t class_sig_item =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ CgCtr v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CgCtr@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             pp_ctyp v1 pp_ctyp v2 pp_attributes v3
       | CgDcl v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CgDcl@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} pp_class_sig_item) arg))
             v1
       | CgInh v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CgInh@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_class_type v1 pp_attributes v2
       | CgMth v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CgMth@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0 (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2 pp_ctyp v3 pp_attributes v4
       | CgVal v0 v1 v2 v3 v4 v5 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CgVal@ (@,%a,@ %a,@ %a,@ %a,@ %a,@ %a@,))@]"
             pp_loc v0 (Ploc.pp_vala Fmt.bool) v1 (Ploc.pp_vala Fmt.bool) v2
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v3 pp_ctyp v4 pp_attributes v5
       | CgVir v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CgVir@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0 (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2 pp_ctyp v3 pp_attributes v4
       | CgFlAtt v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CgFlAtt@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1
       | CgExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CgExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_sig_item : class_sig_item → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_sig_item arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_expr : Fmt.t class_expr =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ CeApp v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeApp@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_class_expr v1 pp_expr v2
       | CeCon v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeCon@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_longid_lident) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_ctyp) arg))
             v2
       | CeFun v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeFun@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_patt v1 pp_class_expr v2
       | CeLet v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeLet@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi}
                        (fun (ofmt : Format.formatter) (v0, v1, v2) →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "(@[%a,@ %a,@ %a@])" pp_patt v0 pp_expr v1
                             pp_attributes v2))
                     arg))
             v2 pp_class_expr v3
       | CeLop v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeLop@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala Fmt.bool) v1 pp_longid v2 pp_class_expr v3
       | CeStr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeStr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)" pp_patt arg ]))
             v1
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} pp_class_str_item) arg))
             v2
       | CeTyc v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeTyc@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_class_expr v1 pp_class_type v2
       | CeXtr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeXtr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_class_expr) arg ])
             v2
       | CeAtt v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeAtt@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_class_expr v1 pp_attribute v2
       | CeExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CeExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_expr : class_expr → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_expr arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_str_item : Fmt.t class_str_item =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ CrCtr v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrCtr@ (@,%a,@ %a,@ %a,@ %a@,))@]" pp_loc v0
             pp_ctyp v1 pp_ctyp v2 pp_attributes v3
       | CrDcl v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrDcl@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]"
                     (list ~{sep = semi} pp_class_str_item) arg))
             v1
       | CrInh v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrInh@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0 (Ploc.pp_vala Fmt.bool) v1 pp_class_expr v2
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)"
                         (fun ofmt arg →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            pf ofmt "%S" arg)
                         arg ]))
             v3 pp_attributes v4
       | CrIni v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrIni@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             pp_expr v1 pp_attributes v2
       | CrMth v0 v1 v2 v3 v4 v5 v6 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "(@[<2>MLast.CrMth@ (@,%a,@ %a,@ %a,@ %a,@ %a,@ %a,@ %a@,))@]"
             pp_loc v0 (Ploc.pp_vala Fmt.bool) v1 (Ploc.pp_vala Fmt.bool) v2
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v3
             (Ploc.pp_vala
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)" pp_ctyp arg ]))
             v4 pp_expr v5 pp_attributes v6
       | CrVal v0 v1 v2 v3 v4 v5 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrVal@ (@,%a,@ %a,@ %a,@ %a,@ %a,@ %a@,))@]"
             pp_loc v0 (Ploc.pp_vala Fmt.bool) v1 (Ploc.pp_vala Fmt.bool) v2
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v3 pp_expr v4 pp_attributes v5
       | CrVav v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrVav@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0 (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2 pp_ctyp v3 pp_attributes v4
       | CrVir v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrVir@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]" pp_loc
             v0 (Ploc.pp_vala Fmt.bool) v1
             (Ploc.pp_vala
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v2 pp_ctyp v3 pp_attributes v4
       | CrFlAtt v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrFlAtt@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1
       | CrExten v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.CrExten@ (@,%a,@ %a@,))@]" pp_loc v0
             pp_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_str_item : class_str_item → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_str_item arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_longid_lident : Fmt.t longid_lident =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) (v0, v1) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "(@[%a,@ %a@])"
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" pp_longid arg ])
         v0
         (Ploc.pp_vala
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v1)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_longid_lident : longid_lident → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_longid_lident arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_payload : Fmt.t payload =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ StAttr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.StAttr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_str_item)
                     arg))
             v1
       | SiAttr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.SiAttr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala
                (fun (ofmt : Format.formatter) arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_sig_item)
                     arg))
             v1
       | TyAttr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.TyAttr@ (@,%a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_ctyp) v1
       | PaAttr v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>MLast.PaAttr@ (@,%a,@ %a,@ %a@,))@]" pp_loc v0
             (Ploc.pp_vala pp_patt) v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" (Ploc.pp_vala pp_expr) arg ])
             v2 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_payload : payload → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_payload arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_attribute_body : Fmt.t attribute_body =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) (v0, v1) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "(@[%a,@ %a@])"
         (Ploc.pp_vala
            (fun (ofmt : Format.formatter) (v0, v1) →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[%a,@ %a@])" pp_loc v0
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
                 v1))
         v0 pp_payload v1)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_attribute_body : attribute_body → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_attribute_body arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_attribute : Fmt.t attribute =
  fun (ofmt : Format.formatter) arg → Ploc.pp_vala pp_attribute_body ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_attribute : attribute → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_attribute arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_attributes_no_anti : Fmt.t attributes_no_anti =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) arg →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_attribute) arg)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_attributes_no_anti : attributes_no_anti → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_attributes_no_anti arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_attributes : Fmt.t attributes =
  fun (ofmt : Format.formatter) arg →
    Ploc.pp_vala pp_attributes_no_anti ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_attributes : attributes → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_attributes arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
