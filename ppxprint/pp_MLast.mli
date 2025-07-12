(* camlp5r *)
module Gen :
  sig
    module Ploc :
      sig
        include module type of Ploc with type t = Ploc.t;
        value pp : Format.formatter → t → unit;
        type vala α =
          Ploc.vala α ==
            [ VaAnt of string
            | VaVal of α ][@@"deriving_inline" show;]
        ;
        value pp_vala : Fmt.t α → Fmt.t (vala α);
        value show_vala : Fmt.t α → vala α → Stdlib.String.t;
        [@@@"end"];
        value pp_loc_verbose : ref bool;
      end
    ;
    type loc = Ploc.t[@@"deriving_inline" show;];
    value pp_loc : Fmt.t loc;
    value show_loc : loc → Stdlib.String.t;
    [@@@"end"];
    type type_var =
      (Ploc.vala (option string) * (option bool * bool))[@@"deriving_inline" show;]
    ;
    value pp_type_var : Fmt.t type_var;
    value show_type_var : type_var → Stdlib.String.t;
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
        | LiUid of loc and Ploc.vala string
        | LiXtr of loc and string and option (Ploc.vala longid) ]
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
        | TyExten of loc and attribute
        | TyOpen of loc and longid and ctyp ]
    and poly_variant =
      MLast.poly_variant ==
        [ PvTag of
            loc and Ploc.vala string and Ploc.vala bool and
              Ploc.vala (list ctyp) and attributes
        | PvInh of loc and ctyp ]
    and patt =
      MLast.patt ==
        [ PaPfx of loc and longid and patt
        | PaLong of loc and longid and Ploc.vala (list (loc * string))
        | PaAli of loc and patt and patt
        | PaAnt of loc and patt
        | PaAny of loc
        | PaApp of loc and patt and patt
        | PaArr of loc and Ploc.vala (list patt)
        | PaChr of loc and Ploc.vala string
        | PaExc of loc and patt
        | PaEff of loc and patt and patt
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
            loc and Ploc.vala (option (Ploc.vala string)) and
              option module_type
        | PaVrn of loc and Ploc.vala string
        | PaXtr of loc and string and option (Ploc.vala patt)
        | PaAtt of loc and patt and attribute
        | PaExten of loc and attribute ]
    and expr =
      MLast.expr ==
        [ ExLong of loc and longid
        | ExOpen of loc and longid and expr
        | ExFle of loc and expr and Ploc.vala longid_lident
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
            loc and Ploc.vala (option (Ploc.vala string)) and module_expr and
              expr
        | ExLop of loc and Ploc.vala bool and module_expr and expr
        | ExMat of loc and expr and Ploc.vala (list case_branch)
        | ExNew of loc and Ploc.vala longid_lident
        | ExObj of
            loc and Ploc.vala (option patt) and
              Ploc.vala (list class_str_item)
        | ExOlb of loc and patt and Ploc.vala (option expr)
        | ExOvr of loc and Ploc.vala (list (string * expr))
        | ExPck of loc and module_expr and option module_type
        | ExRec of loc and Ploc.vala (list (patt * expr)) and option expr
        | ExSeq of loc and Ploc.vala (list expr)
        | ExSnd of loc and expr and Ploc.vala string
        | ExSte of loc and Ploc.vala string and expr and Ploc.vala (list expr)
        | ExStr of loc and Ploc.vala (loc * Ploc.vala string)
        | ExTry of loc and expr and Ploc.vala (list case_branch)
        | ExTup of loc and Ploc.vala (list expr)
        | ExTyc of loc and expr and ctyp
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
                (option
                   (Ploc.vala (option (Ploc.vala string)) * module_type)) and
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
            loc and Ploc.vala string and Ploc.vala (list string) and ctyp and
              Ploc.vala (list string) and attributes
        | SgInc of loc and module_type and attributes
        | SgMod of
            loc and Ploc.vala bool and
              Ploc.vala
                (list
                   (Ploc.vala (option (Ploc.vala string)) * module_type *
                    attributes))
        | SgMty of loc and Ploc.vala string and module_type and attributes
        | SgMtySubst of
            loc and Ploc.vala string and module_type and attributes
        | SgMtyAlias of
            loc and Ploc.vala string and Ploc.vala longid and attributes
        | SgModSubst of loc and Ploc.vala string and longid and attributes
        | SgOpn of loc and longid and attributes
        | SgTyp of loc and Ploc.vala bool and Ploc.vala (list type_decl)
        | SgTypExten of loc and type_extension
        | SgUse of
            loc and Ploc.vala string and Ploc.vala (list (sig_item * loc))
        | SgVal of loc and Ploc.vala string and ctyp and attributes
        | SgXtr of loc and string and option (Ploc.vala sig_item)
        | SgFlAtt of loc and attribute
        | SgExten of loc and attribute and attributes ]
    and with_constr =
      MLast.with_constr ==
        [ WcMod of loc and Ploc.vala longid and module_expr
        | WcMos of loc and Ploc.vala longid and module_expr
        | WcMty of loc and Ploc.vala longid and module_type
        | WcMts of loc and Ploc.vala longid and module_type
        | WcTyp of
            loc and Ploc.vala longid_lident and Ploc.vala (list type_var) and
              Ploc.vala bool and ctyp
        | WcTys of
            loc and Ploc.vala longid_lident and Ploc.vala (list type_var) and
              ctyp ]
    and module_expr =
      MLast.module_expr ==
        [ MeAcc of loc and module_expr and module_expr
        | MeApp of loc and module_expr and module_expr
        | MeFun of
            loc and
              Ploc.vala
                (option
                   (Ploc.vala (option (Ploc.vala string)) * module_type)) and
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
            loc and Ploc.vala string and Ploc.vala (list string) and ctyp and
              Ploc.vala (list string) and attributes
        | StInc of loc and module_expr and attributes
        | StMod of
            loc and Ploc.vala bool and
              Ploc.vala
                (list
                   (Ploc.vala (option (Ploc.vala string)) * module_expr *
                    attributes))
        | StMty of loc and Ploc.vala string and module_type and attributes
        | StOpn of loc and Ploc.vala bool and module_expr and attributes
        | StTyp of loc and Ploc.vala bool and Ploc.vala (list type_decl)
        | StTypExten of loc and type_extension
        | StUse of
            loc and Ploc.vala string and Ploc.vala (list (str_item * loc))
        | StVal of
            loc and Ploc.vala bool and
              Ploc.vala (list (patt * expr * attributes))
        | StXtr of loc and string and option (Ploc.vala str_item)
        | StFlAtt of loc and attribute
        | StExten of loc and attribute and attributes ]
    and type_decl =
      MLast.type_decl ==
        { tdIsDecl : Ploc.vala bool;
          tdNam : Ploc.vala (loc * Ploc.vala string);
          tdPrm : Ploc.vala (list type_var);
          tdPrv : Ploc.vala bool;
          tdDef : ctyp;
          tdCon : Ploc.vala (list (ctyp * ctyp));
          tdAttributes : attributes }
    and generic_constructor =
      (loc * Ploc.vala string * Ploc.vala (list string) *
       Ploc.vala (list ctyp) * Ploc.vala (option ctyp) * attributes)
    and extension_constructor =
      MLast.extension_constructor ==
        [ EcTuple of loc and generic_constructor
        | EcRebind of
            loc and Ploc.vala string and Ploc.vala longid and attributes ]
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
            loc and Ploc.vala (option ctyp) and
              Ploc.vala (list class_sig_item)
        | CtXtr of loc and string and option (Ploc.vala class_type)
        | CtAtt of loc and class_type and attribute
        | CtExten of loc and attribute ]
    and class_sig_item =
      MLast.class_sig_item ==
        [ CgCtr of loc and ctyp and ctyp and attributes
        | CgDcl of loc and Ploc.vala (list class_sig_item)
        | CgInh of loc and class_type and attributes
        | CgMth of
            loc and Ploc.vala bool and Ploc.vala string and ctyp and
              attributes
        | CgVal of
            loc and Ploc.vala bool and Ploc.vala bool and Ploc.vala string and
              ctyp and attributes
        | CgVir of
            loc and Ploc.vala bool and Ploc.vala string and ctyp and
              attributes
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
            loc and Ploc.vala (option patt) and
              Ploc.vala (list class_str_item)
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
            loc and Ploc.vala bool and Ploc.vala string and ctyp and
              attributes
        | CrVir of
            loc and Ploc.vala bool and Ploc.vala string and ctyp and
              attributes
        | CrFlAtt of loc and attribute
        | CrExten of loc and attribute ]
    and longid_lident = (option (Ploc.vala longid) * Ploc.vala string)
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
    value pp_class_infos : Fmt.t α → Fmt.t (class_infos α);
    value show_class_infos : Fmt.t α → class_infos α → Stdlib.String.t;
    value pp_longid : Fmt.t longid;
    value show_longid : longid → Stdlib.String.t;
    value pp_ctyp : Fmt.t ctyp;
    value show_ctyp : ctyp → Stdlib.String.t;
    value pp_poly_variant : Fmt.t poly_variant;
    value show_poly_variant : poly_variant → Stdlib.String.t;
    value pp_patt : Fmt.t patt;
    value show_patt : patt → Stdlib.String.t;
    value pp_expr : Fmt.t expr;
    value show_expr : expr → Stdlib.String.t;
    value pp_case_branch : Fmt.t case_branch;
    value show_case_branch : case_branch → Stdlib.String.t;
    value pp_module_type : Fmt.t module_type;
    value show_module_type : module_type → Stdlib.String.t;
    value pp_functor_parameter : Fmt.t functor_parameter;
    value show_functor_parameter : functor_parameter → Stdlib.String.t;
    value pp_sig_item : Fmt.t sig_item;
    value show_sig_item : sig_item → Stdlib.String.t;
    value pp_with_constr : Fmt.t with_constr;
    value show_with_constr : with_constr → Stdlib.String.t;
    value pp_module_expr : Fmt.t module_expr;
    value show_module_expr : module_expr → Stdlib.String.t;
    value pp_str_item : Fmt.t str_item;
    value show_str_item : str_item → Stdlib.String.t;
    value pp_type_decl : Fmt.t type_decl;
    value show_type_decl : type_decl → Stdlib.String.t;
    value pp_generic_constructor : Fmt.t generic_constructor;
    value show_generic_constructor : generic_constructor → Stdlib.String.t;
    value pp_extension_constructor : Fmt.t extension_constructor;
    value show_extension_constructor :
      extension_constructor → Stdlib.String.t;
    value pp_type_extension : Fmt.t type_extension;
    value show_type_extension : type_extension → Stdlib.String.t;
    value pp_class_type : Fmt.t class_type;
    value show_class_type : class_type → Stdlib.String.t;
    value pp_class_sig_item : Fmt.t class_sig_item;
    value show_class_sig_item : class_sig_item → Stdlib.String.t;
    value pp_class_expr : Fmt.t class_expr;
    value show_class_expr : class_expr → Stdlib.String.t;
    value pp_class_str_item : Fmt.t class_str_item;
    value show_class_str_item : class_str_item → Stdlib.String.t;
    value pp_longid_lident : Fmt.t longid_lident;
    value show_longid_lident : longid_lident → Stdlib.String.t;
    value pp_payload : Fmt.t payload;
    value show_payload : payload → Stdlib.String.t;
    value pp_attribute_body : Fmt.t attribute_body;
    value show_attribute_body : attribute_body → Stdlib.String.t;
    value pp_attribute : Fmt.t attribute;
    value show_attribute : attribute → Stdlib.String.t;
    value pp_attributes_no_anti : Fmt.t attributes_no_anti;
    value show_attributes_no_anti : attributes_no_anti → Stdlib.String.t;
    value pp_attributes : Fmt.t attributes;
    value show_attributes : attributes → Stdlib.String.t;
    [@@@"end"];
  end
;
