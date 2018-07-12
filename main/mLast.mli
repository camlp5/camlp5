(* camlp5r *)
(* mLast.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";

(* Module [MLast]: abstract syntax tree.

   This is undocumented because the AST is not supposed to be used
   directly; the good usage is to use the quotations representing
   these values in concrete syntax (see the Camlp5 documentation).
   See also the file q_MLast.ml in Camlp5 sources. *)

type loc = Ploc.t;

IFNDEF STRICT THEN
  DEFINE_TYPE V t = t
ELSE
  DEFINE_TYPE V t = Ploc.vala t
END;

type v 'a = V 'a;

type type_var = (V (option string) * option bool);

type class_infos 'a =
  { ciLoc : loc;
    ciVir : V bool;
    ciPrm : (loc * V (list type_var));
    ciNam : V string;
    ciExp : 'a }
;

type ctyp =
  [ TyAcc of loc and ctyp and ctyp
  | TyAli of loc and ctyp and ctyp
  | TyAny of loc
  | TyApp of loc and ctyp and ctyp
  | TyArr of loc and ctyp and ctyp
  | TyCls of loc and V (list string)
  | TyLab of loc and V string and ctyp
  | TyLid of loc and V string
  | TyMan of loc and ctyp and V bool and ctyp
  | TyObj of loc and V (list (string * ctyp)) and V bool
  | TyOlb of loc and V string and ctyp
  | TyPck of loc and module_type
  | TyPol of loc and V (list string) and ctyp
  | TyPot of loc and V (list string) and ctyp
  | TyQuo of loc and V string
  | TyRec of loc and V (list (loc * string * bool * ctyp))
  | TySum of loc and V (list (loc * V string * V (list ctyp) * option ctyp))
  | TyTup of loc and V (list ctyp)
  | TyUid of loc and V string
  | TyVrn of loc and V (list poly_variant) and
      option (option (V (list string)))
  | TyXtr of loc and string and option (V ctyp) ]
and poly_variant =
  [ PvTag of loc and V string and V bool and V (list ctyp)
  | PvInh of loc and ctyp ]
and patt =
  [ PaAcc of loc and patt and patt
  | PaAli of loc and patt and patt
  | PaAnt of loc and patt
  | PaAny of loc
  | PaApp of loc and patt and patt
  | PaArr of loc and V (list patt)
  | PaChr of loc and V string
  | PaFlo of loc and V string
  | PaInt of loc and V string and string
  | PaLab of loc and V (list (patt * V (option patt)))
  | PaLaz of loc and patt
  | PaLid of loc and V string
  | PaNty of loc and V string
  | PaOlb of loc and patt and V (option expr)
  | PaOrp of loc and patt and patt
  | PaRec of loc and V (list (patt * patt))
  | PaRng of loc and patt and patt
  | PaStr of loc and V string
  | PaTup of loc and V (list patt)
  | PaTyc of loc and patt and ctyp
  | PaTyp of loc and V (list string)
  | PaUid of loc and V string
  | PaUnp of loc and V string and option module_type
  | PaVrn of loc and V string
  | PaXtr of loc and string and option (V patt) ]
and expr =
  [ ExAcc of loc and expr and expr
  | ExAnt of loc and expr
  | ExApp of loc and expr and expr
  | ExAre of loc and expr and expr
  | ExArr of loc and V (list expr)
  | ExAsr of loc and expr
  | ExAss of loc and expr and expr
  | ExBae of loc and expr and V (list expr)
  | ExChr of loc and V string
  | ExCoe of loc and expr and option ctyp and ctyp
  | ExFlo of loc and V string
  | ExFor of loc and V string and expr and expr and V bool and V (list expr)
  | ExFun of loc and V (list (patt * V (option expr) * expr))
  | ExIfe of loc and expr and expr and expr
  | ExInt of loc and V string and string
  | ExJdf of loc and V (list joinclause) and expr
  | ExLab of loc and V (list (patt * V (option expr)))
  | ExLaz of loc and expr
  | ExLet of loc and V bool and V (list (patt * expr)) and expr
  | ExLid of loc and V string
  | ExLmd of loc and V string and module_expr and expr
  | ExLop of loc and module_expr and expr
  | ExMat of loc and expr and V (list (patt * V (option expr) * expr))
  | ExNew of loc and V (list string)
  | ExObj of loc and V (option patt) and V (list class_str_item)
  | ExOlb of loc and patt and V (option expr)
  | ExOvr of loc and V (list (string * expr))
  | ExPar of loc and expr and expr
  | ExPck of loc and module_expr and option module_type
  | ExRec of loc and V (list (patt * expr)) and option expr
  | ExRpl of loc and V (option expr) and V (loc * V string)
  | ExSeq of loc and V (list expr)
  | ExSpw of loc and expr
  | ExSnd of loc and expr and V string
  | ExSte of loc and expr and expr
  | ExStr of loc and V string
  | ExTry of loc and expr and V (list (patt * V (option expr) * expr))
  | ExTup of loc and V (list expr)
  | ExTyc of loc and expr and ctyp
  | ExUid of loc and V string
  | ExVrn of loc and V string
  | ExWhi of loc and expr and V (list expr)
  | ExXtr of loc and string and option (V expr) ]
and module_type =
  [ MtAcc of loc and module_type and module_type
  | MtApp of loc and module_type and module_type
  | MtFun of loc and V string and module_type and module_type
  | MtLid of loc and V string
  | MtQuo of loc and V string
  | MtSig of loc and V (list sig_item)
  | MtTyo of loc and module_expr
  | MtUid of loc and V string
  | MtWit of loc and module_type and V (list with_constr)
  | MtXtr of loc and string and option (V module_type) ]
and sig_item =
  [ SgCls of loc and V (list (class_infos class_type))
  | SgClt of loc and V (list (class_infos class_type))
  | SgDcl of loc and V (list sig_item)
  | SgDir of loc and V string and V (option expr)
  | SgExc of loc and V string and V (list ctyp)
  | SgExt of loc and V string and ctyp and V (list string)
  | SgInc of loc and module_type
  | SgMod of loc and V bool and V (list (V string * module_type))
  | SgMty of loc and V string and module_type
  | SgOpn of loc and V (list string)
  | SgTyp of loc and V (list type_decl)
  | SgUse of loc and V string and V (list (sig_item * loc))
  | SgVal of loc and V string and ctyp
  | SgXtr of loc and string and option (V sig_item) ]
and with_constr =
  [ WcMod of loc and V (list string) and module_expr
  | WcMos of loc and V (list string) and module_expr
  | WcTyp of loc and V (list string) and V (list type_var) and V bool and ctyp
  | WcTys of loc and V (list string) and V (list type_var) and ctyp ]
and module_expr =
  [ MeAcc of loc and module_expr and module_expr
  | MeApp of loc and module_expr and module_expr
  | MeFun of loc and V string and module_type and module_expr
  | MeStr of loc and V (list str_item)
  | MeTyc of loc and module_expr and module_type
  | MeUid of loc and V string
  | MeUnp of loc and expr and option module_type
  | MeXtr of loc and string and option (V module_expr) ]
and str_item =
  [ StCls of loc and V (list (class_infos class_expr))
  | StClt of loc and V (list (class_infos class_type))
  | StDcl of loc and V (list str_item)
  | StDef of loc and V (list joinclause)
  | StDir of loc and V string and V (option expr)
  | StExc of loc and V string and V (list ctyp) and V (list string)
  | StExp of loc and expr
  | StExt of loc and V string and ctyp and V (list string)
  | StInc of loc and module_expr
  | StMod of loc and V bool and V (list (V string * module_expr))
  | StMty of loc and V string and module_type
  | StOpn of loc and V (list string)
  | StTyp of loc and V bool and V (list type_decl)
  | StUse of loc and V string and V (list (str_item * loc))
  | StVal of loc and V bool and V (list (patt * expr))
  | StXtr of loc and string and option (V str_item) ]
and joinclause =
  { jcLoc : loc;
    jcVal :
      V (list
           (loc * V (list (loc * (loc * V string) * V (option patt))) *
            expr)) }
and type_decl =
  { tdNam : V (loc * V string);
    tdPrm : V (list type_var);
    tdPrv : V bool;
    tdDef : ctyp;
    tdCon : V (list (ctyp * ctyp)) }
and class_type =
  [ CtAcc of loc and class_type and class_type
  | CtApp of loc and class_type and class_type
  | CtCon of loc and class_type and V (list ctyp)
  | CtFun of loc and ctyp and class_type
  | CtIde of loc and V string
  | CtSig of loc and V (option ctyp) and V (list class_sig_item)
  | CtXtr of loc and string and option (V class_type) ]
and class_sig_item =
  [ CgCtr of loc and ctyp and ctyp
  | CgDcl of loc and V (list class_sig_item)
  | CgInh of loc and class_type
  | CgMth of loc and V bool and V string and ctyp
  | CgVal of loc and V bool and V string and ctyp
  | CgVir of loc and V bool and V string and ctyp ]
and class_expr =
  [ CeApp of loc and class_expr and expr
  | CeCon of loc and V (list string) and V (list ctyp)
  | CeFun of loc and patt and class_expr
  | CeLet of loc and V bool and V (list (patt * expr)) and class_expr
  | CeStr of loc and V (option patt) and V (list class_str_item)
  | CeTyc of loc and class_expr and class_type
  | CeXtr of loc and string and option (V class_expr) ]
and class_str_item =
  [ CrCtr of loc and ctyp and ctyp
  | CrDcl of loc and V (list class_str_item)
  | CrInh of loc and class_expr and V (option string)
  | CrIni of loc and expr
  | CrMth of loc and V bool and V bool and V string and V (option ctyp) and
      expr
  | CrVal of loc and V bool and V bool and V string and expr
  | CrVav of loc and V bool and V string and ctyp
  | CrVir of loc and V bool and V string and ctyp ]
;

external loc_of_ctyp : ctyp -> loc = "%field0";
external loc_of_patt : patt -> loc = "%field0";
external loc_of_expr : expr -> loc = "%field0";
external loc_of_module_type : module_type -> loc = "%field0";
external loc_of_module_expr : module_expr -> loc = "%field0";
external loc_of_sig_item : sig_item -> loc = "%field0";
external loc_of_str_item : str_item -> loc = "%field0";
external loc_of_with_constr : with_constr -> loc = "%field0";

external loc_of_class_type : class_type -> loc = "%field0";
external loc_of_class_sig_item : class_sig_item -> loc = "%field0";
external loc_of_class_expr : class_expr -> loc = "%field0";
external loc_of_class_str_item : class_str_item -> loc = "%field0";
