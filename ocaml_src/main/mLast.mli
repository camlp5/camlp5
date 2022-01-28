(* camlp5r *)
(* mLast.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)

(* Module [MLast]: abstract syntax tree.

   This is undocumented because the AST is not supposed to be used
   directly; the good usage is to use the quotations representing
   these values in concrete syntax (see the Camlp5 documentation).
   See also the file q_MLast.ml in Camlp5 sources. *)

type loc = Ploc.t;;

(* *)

type 'a v = 'a;;

type type_var = string option * (bool option * bool);;

type 'a class_infos =
  { ciLoc : loc;
    ciVir : bool;
    ciPrm : loc * type_var list;
    ciNam : string;
    ciExp : 'a;
    ciAttributes : attributes }
and longid =
    LiAcc of loc * longid * string
  | LiApp of loc * longid * longid
  | LiUid of loc * string
  | LiXtr of loc * string * longid option
and ctyp =
    TyAcc of loc * longid * string
  | TyAli of loc * ctyp * ctyp
  | TyAny of loc
  | TyApp of loc * ctyp * ctyp
  | TyArr of loc * ctyp * ctyp
  | TyCls of loc * longid_lident
  | TyLab of loc * string * ctyp
  | TyLid of loc * string
  | TyMan of loc * ctyp * bool * ctyp
  | TyObj of loc * (string option * ctyp * attributes) list * bool
  | TyOlb of loc * string * ctyp
  | TyOpn of loc
  | TyPck of loc * module_type
  | TyPol of loc * string list * ctyp
  | TyPot of loc * string list * ctyp
  | TyQuo of loc * string
  | TyRec of loc * (loc * string * bool * ctyp * attributes) list
  | TySum of loc * generic_constructor list
  | TyTup of loc * ctyp list
  | TyVrn of loc * poly_variant list * string list option option
  | TyXtr of loc * string * ctyp option
  | TyAtt of loc * ctyp * attribute
  | TyExten of loc * attribute
and poly_variant =
    PvTag of loc * string * bool * ctyp list * attributes
  | PvInh of loc * ctyp
and patt =
    PaPfx of loc * longid * patt
  | PaLong of loc * longid * (loc * string) list
  | PaAli of loc * patt * patt
  | PaAnt of loc * patt
  | PaAny of loc
  | PaApp of loc * patt * patt
  | PaArr of loc * patt list
  | PaChr of loc * string
  | PaExc of loc * patt
  | PaFlo of loc * string
  | PaInt of loc * string * string
  | PaLab of loc * (patt * patt option) list
  | PaLaz of loc * patt
  | PaLid of loc * string
  | PaNty of loc * string
  | PaOlb of loc * patt * expr option
  | PaOrp of loc * patt * patt
  | PaRec of loc * (patt * patt) list
  | PaRng of loc * patt * patt
  | PaStr of loc * string
  | PaTup of loc * patt list
  | PaTyc of loc * patt * ctyp
  | PaTyp of loc * longid_lident
  | PaUnp of loc * string option * module_type option
  | PaVrn of loc * string
  | PaXtr of loc * string * patt option
  | PaAtt of loc * patt * attribute
  | PaExten of loc * attribute
and expr =
    ExLong of loc * longid
  | ExOpen of loc * longid * expr
  | ExFle of loc * expr * longid_lident
  | ExAnt of loc * expr
  | ExApp of loc * expr * expr
  | ExAre of loc * string * expr * expr list
  | ExArr of loc * expr list
  | ExAsr of loc * expr
  | ExAss of loc * expr * expr
  | ExBae of loc * string * expr * expr list
  | ExChr of loc * string
  | ExCoe of loc * expr * ctyp option * ctyp
  | ExFlo of loc * string
  | ExFor of loc * patt * expr * expr * bool * expr list
  | ExFun of loc * case_branch list
  | ExIfe of loc * expr * expr * expr
  | ExInt of loc * string * string
  | ExLab of loc * (patt * expr option) list
  | ExLaz of loc * expr
  | ExLet of loc * bool * (patt * expr * attributes) list * expr
  | ExLEx of loc * string * ctyp list * expr * attributes
  | ExLid of loc * string
  | ExLmd of loc * string option * module_expr * expr
  | ExLop of loc * bool * module_expr * expr
  | ExMat of loc * expr * case_branch list
  | ExNew of loc * longid_lident
  | ExObj of loc * patt option * class_str_item list
  | ExOlb of loc * patt * expr option
  | ExOvr of loc * (string * expr) list
  | ExPck of loc * module_expr * module_type option
  | ExRec of loc * (patt * expr) list * expr option
  | ExSeq of loc * expr list
  | ExSnd of loc * expr * string
  | ExSte of loc * string * expr * expr list
  | ExStr of loc * string
  | ExTry of loc * expr * case_branch list
  | ExTup of loc * expr list
  | ExTyc of loc * expr * ctyp
  | ExVrn of loc * string
  | ExWhi of loc * expr * expr list
  | ExXtr of loc * string * expr option
  | ExAtt of loc * expr * attribute
  | ExExten of loc * attribute
  | ExUnr of loc
and case_branch = patt * expr option * expr
and module_type =
    MtLong of loc * longid
  | MtLongLid of loc * longid * string
  | MtLid of loc * string
  | MtFun of loc * (string option * module_type) option * module_type
  | MtQuo of loc * string
  | MtSig of loc * sig_item list
  | MtTyo of loc * module_expr
  | MtWit of loc * module_type * with_constr list
  | MtXtr of loc * string * module_type option
  | MtAtt of loc * module_type * attribute
  | MtExten of loc * attribute
and functor_parameter = (string option * module_type) option
and sig_item =
    SgCls of loc * class_type class_infos list
  | SgClt of loc * class_type class_infos list
  | SgDcl of loc * sig_item list
  | SgDir of loc * string * expr option
  | SgExc of loc * generic_constructor * attributes
  | SgExt of loc * string * string list * ctyp * string list * attributes
  | SgInc of loc * module_type * attributes
  | SgMod of loc * bool * (string option * module_type * attributes) list
  | SgMty of loc * string * module_type * attributes
  | SgMtySubst of loc * string * module_type * attributes
  | SgMtyAlias of loc * string * longid * attributes
  | SgModSubst of loc * string * longid * attributes
  | SgOpn of loc * longid * attributes
  | SgTyp of loc * bool * type_decl list
  | SgTypExten of loc * type_extension
  | SgUse of loc * string * (sig_item * loc) list
  | SgVal of loc * string * ctyp * attributes
  | SgXtr of loc * string * sig_item option
  | SgFlAtt of loc * attribute
  | SgExten of loc * attribute * attributes
and with_constr =
    WcMod of loc * longid * module_expr
  | WcMos of loc * longid * module_expr
  | WcMty of loc * longid * module_type
  | WcMts of loc * longid * module_type
  | WcTyp of loc * longid_lident * type_var list * bool * ctyp
  | WcTys of loc * longid_lident * type_var list * ctyp
and module_expr =
    MeAcc of loc * module_expr * module_expr
  | MeApp of loc * module_expr * module_expr
  | MeFun of loc * (string option * module_type) option * module_expr
  | MeStr of loc * str_item list
  | MeTyc of loc * module_expr * module_type
  | MeUid of loc * string
  | MeUnp of loc * expr * module_type option * module_type option
  | MeXtr of loc * string * module_expr option
  | MeAtt of loc * module_expr * attribute
  | MeExten of loc * attribute
and str_item =
    StCls of loc * class_expr class_infos list
  | StClt of loc * class_type class_infos list
  | StDcl of loc * str_item list
  | StDir of loc * string * expr option
  | StExc of loc * extension_constructor * attributes
  | StExp of loc * expr * attributes
  | StExt of loc * string * string list * ctyp * string list * attributes
  | StInc of loc * module_expr * attributes
  | StMod of loc * bool * (string option * module_expr * attributes) list
  | StMty of loc * string * module_type * attributes
  | StOpn of loc * bool * module_expr * attributes
  | StTyp of loc * bool * type_decl list
  | StTypExten of loc * type_extension
  | StUse of loc * string * (str_item * loc) list
  | StVal of loc * bool * (patt * expr * attributes) list
  | StXtr of loc * string * str_item option
  | StFlAtt of loc * attribute
  | StExten of loc * attribute * attributes
and type_decl =
  { tdIsDecl : bool;
    tdNam : loc * string;
    tdPrm : type_var list;
    tdPrv : bool;
    tdDef : ctyp;
    tdCon : (ctyp * ctyp) list;
    tdAttributes : attributes }
and generic_constructor =
  loc * string * string list * ctyp list * ctyp option * attributes
and extension_constructor =
    EcTuple of loc * generic_constructor
  | EcRebind of loc * string * longid * attributes
and type_extension =
  { teNam : longid_lident;
    tePrm : type_var list;
    tePrv : bool;
    teECs : extension_constructor list;
    teAttributes : attributes }
and class_type =
    CtLongLid of loc * longid * string
  | CtLid of loc * string
  | CtLop of loc * bool * longid * class_type
  | CtCon of loc * class_type * ctyp list
  | CtFun of loc * ctyp * class_type
  | CtSig of loc * ctyp option * class_sig_item list
  | CtXtr of loc * string * class_type option
  | CtAtt of loc * class_type * attribute
  | CtExten of loc * attribute
and class_sig_item =
    CgCtr of loc * ctyp * ctyp * attributes
  | CgDcl of loc * class_sig_item list
  | CgInh of loc * class_type * attributes
  | CgMth of loc * bool * string * ctyp * attributes
  | CgVal of loc * bool * bool * string * ctyp * attributes
  | CgVir of loc * bool * string * ctyp * attributes
  | CgFlAtt of loc * attribute
  | CgExten of loc * attribute
and class_expr =
    CeApp of loc * class_expr * expr
  | CeCon of loc * longid_lident * ctyp list
  | CeFun of loc * patt * class_expr
  | CeLet of loc * bool * (patt * expr * attributes) list * class_expr
  | CeLop of loc * bool * longid * class_expr
  | CeStr of loc * patt option * class_str_item list
  | CeTyc of loc * class_expr * class_type
  | CeXtr of loc * string * class_expr option
  | CeAtt of loc * class_expr * attribute
  | CeExten of loc * attribute
and class_str_item =
    CrCtr of loc * ctyp * ctyp * attributes
  | CrDcl of loc * class_str_item list
  | CrInh of loc * bool * class_expr * string option * attributes
  | CrIni of loc * expr * attributes
  | CrMth of loc * bool * bool * string * ctyp option * expr * attributes
  | CrVal of loc * bool * bool * string * expr * attributes
  | CrVav of loc * bool * string * ctyp * attributes
  | CrVir of loc * bool * string * ctyp * attributes
  | CrFlAtt of loc * attribute
  | CrExten of loc * attribute
and longid_lident = longid option * string
and payload =
    StAttr of loc * str_item list
  | SiAttr of loc * sig_item list
  | TyAttr of loc * ctyp
  | PaAttr of loc * patt * expr option
and attribute_body = (loc * string) * payload
and attribute = attribute_body
and attributes_no_anti = attribute list
and attributes = attributes_no_anti;;

external loc_of_longid : longid -> loc = "%field0";;
external loc_of_ctyp : ctyp -> loc = "%field0";;
external loc_of_patt : patt -> loc = "%field0";;
external loc_of_expr : expr -> loc = "%field0";;
external loc_of_module_type : module_type -> loc = "%field0";;
external loc_of_module_expr : module_expr -> loc = "%field0";;
external loc_of_sig_item : sig_item -> loc = "%field0";;
external loc_of_str_item : str_item -> loc = "%field0";;
external loc_of_with_constr : with_constr -> loc = "%field0";;
external loc_of_extension_constructor :
  extension_constructor -> loc = "%field0";;
external loc_of_constructor : generic_constructor -> loc = "%field0";;

external loc_of_class_type : class_type -> loc = "%field0";;
external loc_of_class_sig_item : class_sig_item -> loc = "%field0";;
external loc_of_class_expr : class_expr -> loc = "%field0";;
external loc_of_class_str_item : class_str_item -> loc = "%field0";;
