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

type type_var = string option * bool option;;

type 'a class_infos =
  { ciLoc : loc;
    ciVir : bool;
    ciPrm : loc * type_var list;
    ciNam : string;
    ciExp : 'a }
;;

type ctyp =
    TyAcc of loc * ctyp * ctyp
  | TyAli of loc * ctyp * ctyp
  | TyAny of loc
  | TyApp of loc * ctyp * ctyp
  | TyArr of loc * ctyp * ctyp
  | TyCls of loc * string list
  | TyLab of loc * string * ctyp
  | TyLid of loc * string
  | TyMan of loc * ctyp * bool * ctyp
  | TyObj of loc * (string * ctyp) list * bool
  | TyOlb of loc * string * ctyp
  | TyPck of loc * module_type
  | TyPol of loc * string list * ctyp
  | TyPot of loc * string list * ctyp
  | TyQuo of loc * string
  | TyRec of loc * (loc * string * bool * ctyp) list
  | TySum of loc * (loc * string * ctyp list * ctyp option) list
  | TyTup of loc * ctyp list
  | TyUid of loc * string
  | TyVrn of loc * poly_variant list * string list option option
  | TyXtr of loc * string * ctyp option
and poly_variant =
    PvTag of loc * string * bool * ctyp list
  | PvInh of loc * ctyp
and patt =
    PaAcc of loc * patt * patt
  | PaAli of loc * patt * patt
  | PaAnt of loc * patt
  | PaAny of loc
  | PaApp of loc * patt * patt
  | PaArr of loc * patt list
  | PaChr of loc * string
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
  | PaTyp of loc * string list
  | PaUid of loc * string
  | PaUnp of loc * string * module_type option
  | PaVrn of loc * string
  | PaXtr of loc * string * patt option
and expr =
    ExAcc of loc * expr * expr
  | ExAnt of loc * expr
  | ExApp of loc * expr * expr
  | ExAre of loc * expr * expr
  | ExArr of loc * expr list
  | ExAsr of loc * expr
  | ExAss of loc * expr * expr
  | ExBae of loc * expr * expr list
  | ExChr of loc * string
  | ExCoe of loc * expr * ctyp option * ctyp
  | ExFlo of loc * string
  | ExFor of loc * string * expr * expr * bool * expr list
  | ExFun of loc * (patt * expr option * expr) list
  | ExIfe of loc * expr * expr * expr
  | ExInt of loc * string * string
  | ExJdf of loc * joinclause list * expr
  | ExLab of loc * (patt * expr option) list
  | ExLaz of loc * expr
  | ExLet of loc * bool * (patt * expr) list * expr
  | ExLid of loc * string
  | ExLmd of loc * string * module_expr * expr
  | ExLop of loc * module_expr * expr
  | ExMat of loc * expr * (patt * expr option * expr) list
  | ExNew of loc * string list
  | ExObj of loc * patt option * class_str_item list
  | ExOlb of loc * patt * expr option
  | ExOvr of loc * (string * expr) list
  | ExPar of loc * expr * expr
  | ExPck of loc * module_expr * module_type option
  | ExRec of loc * (patt * expr) list * expr option
  | ExRpl of loc * expr option * (loc * string)
  | ExSeq of loc * expr list
  | ExSpw of loc * expr
  | ExSnd of loc * expr * string
  | ExSte of loc * expr * expr
  | ExStr of loc * string
  | ExTry of loc * expr * (patt * expr option * expr) list
  | ExTup of loc * expr list
  | ExTyc of loc * expr * ctyp
  | ExUid of loc * string
  | ExVrn of loc * string
  | ExWhi of loc * expr * expr list
  | ExXtr of loc * string * expr option
and module_type =
    MtAcc of loc * module_type * module_type
  | MtApp of loc * module_type * module_type
  | MtFun of loc * string * module_type * module_type
  | MtLid of loc * string
  | MtQuo of loc * string
  | MtSig of loc * sig_item list
  | MtTyo of loc * module_expr
  | MtUid of loc * string
  | MtWit of loc * module_type * with_constr list
  | MtXtr of loc * string * module_type option
and sig_item =
    SgCls of loc * class_type class_infos list
  | SgClt of loc * class_type class_infos list
  | SgDcl of loc * sig_item list
  | SgDir of loc * string * expr option
  | SgExc of loc * string * ctyp list
  | SgExt of loc * string * ctyp * string list
  | SgInc of loc * module_type
  | SgMod of loc * bool * (string * module_type) list
  | SgMty of loc * string * module_type
  | SgOpn of loc * string list
  | SgTyp of loc * type_decl list
  | SgUse of loc * string * (sig_item * loc) list
  | SgVal of loc * string * ctyp
  | SgXtr of loc * string * sig_item option
and with_constr =
    WcMod of loc * string list * module_expr
  | WcMos of loc * string list * module_expr
  | WcTyp of loc * string list * type_var list * bool * ctyp
  | WcTys of loc * string list * type_var list * ctyp
and module_expr =
    MeAcc of loc * module_expr * module_expr
  | MeApp of loc * module_expr * module_expr
  | MeFun of loc * string * module_type * module_expr
  | MeStr of loc * str_item list
  | MeTyc of loc * module_expr * module_type
  | MeUid of loc * string
  | MeUnp of loc * expr * module_type option
  | MeXtr of loc * string * module_expr option
and str_item =
    StCls of loc * class_expr class_infos list
  | StClt of loc * class_type class_infos list
  | StDcl of loc * str_item list
  | StDef of loc * joinclause list
  | StDir of loc * string * expr option
  | StExc of loc * string * ctyp list * string list
  | StExp of loc * expr
  | StExt of loc * string * ctyp * string list
  | StInc of loc * module_expr
  | StMod of loc * bool * (string * module_expr) list
  | StMty of loc * string * module_type
  | StOpn of loc * string list
  | StTyp of loc * bool * type_decl list
  | StUse of loc * string * (str_item * loc) list
  | StVal of loc * bool * (patt * expr) list
  | StXtr of loc * string * str_item option
and joinclause =
  { jcLoc : loc;
    jcVal : (loc * (loc * (loc * string) * patt option) list * expr) list }
and type_decl =
  { tdNam : loc * string;
    tdPrm : type_var list;
    tdPrv : bool;
    tdDef : ctyp;
    tdCon : (ctyp * ctyp) list }
and class_type =
    CtAcc of loc * class_type * class_type
  | CtApp of loc * class_type * class_type
  | CtCon of loc * class_type * ctyp list
  | CtFun of loc * ctyp * class_type
  | CtIde of loc * string
  | CtSig of loc * ctyp option * class_sig_item list
  | CtXtr of loc * string * class_type option
and class_sig_item =
    CgCtr of loc * ctyp * ctyp
  | CgDcl of loc * class_sig_item list
  | CgInh of loc * class_type
  | CgMth of loc * bool * string * ctyp
  | CgVal of loc * bool * string * ctyp
  | CgVir of loc * bool * string * ctyp
and class_expr =
    CeApp of loc * class_expr * expr
  | CeCon of loc * string list * ctyp list
  | CeFun of loc * patt * class_expr
  | CeLet of loc * bool * (patt * expr) list * class_expr
  | CeStr of loc * patt option * class_str_item list
  | CeTyc of loc * class_expr * class_type
  | CeXtr of loc * string * class_expr option
and class_str_item =
    CrCtr of loc * ctyp * ctyp
  | CrDcl of loc * class_str_item list
  | CrInh of loc * class_expr * string option
  | CrIni of loc * expr
  | CrMth of loc * bool * bool * string * ctyp option * expr
  | CrVal of loc * bool * bool * string * expr
  | CrVav of loc * bool * string * ctyp
  | CrVir of loc * bool * string * ctyp
;;

external loc_of_ctyp : ctyp -> loc = "%field0";;
external loc_of_patt : patt -> loc = "%field0";;
external loc_of_expr : expr -> loc = "%field0";;
external loc_of_module_type : module_type -> loc = "%field0";;
external loc_of_module_expr : module_expr -> loc = "%field0";;
external loc_of_sig_item : sig_item -> loc = "%field0";;
external loc_of_str_item : str_item -> loc = "%field0";;
external loc_of_with_constr : with_constr -> loc = "%field0";;

external loc_of_class_type : class_type -> loc = "%field0";;
external loc_of_class_sig_item : class_sig_item -> loc = "%field0";;
external loc_of_class_expr : class_expr -> loc = "%field0";;
external loc_of_class_str_item : class_str_item -> loc = "%field0";;
