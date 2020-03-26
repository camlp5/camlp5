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
    ciExp : 'a ;
    ciAttributes : attributes
  }

and longid =
  [ LiAcc of loc and longid and V string
  | LiApp of loc and longid and longid
  | LiUid of loc and V string
  ]
and ctyp =
  [ TyAcc of loc and longid and V string
  | TyAli of loc and ctyp and ctyp
  | TyAny of loc
  | TyApp of loc and ctyp and ctyp
  | TyArr of loc and ctyp and ctyp
  | TyCls of loc and V (list string)
  | TyLab of loc and V string and ctyp
  | TyLid of loc and V string
  | TyMan of loc and ctyp and V bool and ctyp
  | TyObj of loc and V (list (option string * ctyp * attributes)) and V bool
  | TyOlb of loc and V string and ctyp
  | TyOpn of loc
  | TyPck of loc and module_type
  | TyPol of loc and V (list string) and ctyp
  | TyPot of loc and V (list string) and ctyp
  | TyQuo of loc and V string
  | TyRec of loc and V (list (loc * string * bool * ctyp * attributes))
  | TySum of loc and V (list generic_constructor)
  | TyTup of loc and V (list ctyp)
  | TyVrn of loc and V (list poly_variant) and
      option (option (V (list string)))
  | TyXtr of loc and string and option (V ctyp)
  | TyAtt of loc and ctyp and attribute_body
  | TyExten of loc and attribute_body ]
and poly_variant =
  [ PvTag of loc and V string and V bool and V (list ctyp) and attributes
  | PvInh of loc and ctyp ]
and patt =
  [ PaAcc of loc and patt and patt
  | PaAli of loc and patt and patt
  | PaAnt of loc and patt
  | PaAny of loc
  | PaApp of loc and patt and patt
  | PaArr of loc and V (list patt)
  | PaChr of loc and V string
  | PaExc of loc and patt
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
  | PaUnp of loc and V (option (V string)) and option module_type
  | PaVrn of loc and V string
  | PaXtr of loc and string and option (V patt)
  | PaAtt of loc and patt and attribute_body
  | PaExten of loc and attribute_body ]
and expr =
  [ ExAcc of loc and expr and expr
  | ExAnt of loc and expr
  | ExApp of loc and expr and expr
  | ExAre of loc and V string and expr and V (list expr)
  | ExArr of loc and V (list expr)
  | ExAsr of loc and expr
  | ExAss of loc and expr and expr
  | ExBae of loc and V string and expr and V (list expr)
  | ExChr of loc and V string
  | ExCoe of loc and expr and option ctyp and ctyp
  | ExFlo of loc and V string
  | ExFor of loc and patt and expr and expr and V bool and V (list expr)
  | ExFun of loc and V (list (patt * V (option expr) * expr))
  | ExIfe of loc and expr and expr and expr
  | ExInt of loc and V string and string
  | ExLab of loc and V (list (patt * V (option expr)))
  | ExLaz of loc and expr
  | ExLet of loc and V bool and V (list (patt * expr * attributes)) and expr
  | ExLEx of loc and V string and V (list ctyp) and expr and attributes
  | ExLid of loc and V string
  | ExLmd of loc and V (option (V string)) and module_expr and expr
  | ExLop of loc and module_expr and expr
  | ExMat of loc and expr and V (list (patt * V (option expr) * expr))
  | ExNew of loc and V (list string)
  | ExObj of loc and V (option patt) and V (list class_str_item)
  | ExOlb of loc and patt and V (option expr)
  | ExOvr of loc and V (list (string * expr))
  | ExPck of loc and module_expr and option module_type
  | ExRec of loc and V (list (patt * expr)) and option expr
  | ExSeq of loc and V (list expr)
  | ExSnd of loc and expr and V string
  | ExSte of loc and V string and expr and V (list expr)
  | ExStr of loc and V string
  | ExTry of loc and expr and V (list (patt * V (option expr) * expr))
  | ExTup of loc and V (list expr)
  | ExTyc of loc and expr and ctyp
  | ExUid of loc and V string
  | ExVrn of loc and V string
  | ExWhi of loc and expr and V (list expr)
  | ExXtr of loc and string and option (V expr)
  | ExAtt of loc and expr and attribute_body
  | ExExten of loc and attribute_body
  | ExUnr of loc
  ]
and module_type =
  [ MtLong of loc and longid
  | MtLongLid of loc and longid and V string
  | MtLid of loc and V string
  | MtFun of loc and (V (option (V (option (V string)) * module_type))) and module_type
  | MtQuo of loc and V string
  | MtSig of loc and V (list sig_item)
  | MtTyo of loc and module_expr
  | MtWit of loc and module_type and V (list with_constr)
  | MtXtr of loc and string and option (V module_type)
  | MtAtt of loc and module_type and attribute_body
  | MtExten of loc and attribute_body ]
(* NOTE WELL that this type is here for documentation: the places in MtFun and MeFun
   where this type should appear ..... in those places, the type is substituted in
   directly, so that the automated test will work.  What a PITA.
   TODO: Chet, fix this (by fixing the automated test!)
*)
and functor_parameter = option (V (option (V string)) * module_type)
and sig_item =
  [ SgCls of loc and V (list (class_infos class_type))
  | SgClt of loc and V (list (class_infos class_type))
  | SgDcl of loc and V (list sig_item)
  | SgDir of loc and V string and V (option expr)
  | SgExc of loc and generic_constructor and attributes
  | SgExt of loc and V string and ctyp and V (list string) and attributes
  | SgInc of loc and module_type and attributes
  | SgMod of loc and V bool and V (list (V (option (V string)) * module_type * attributes))
  | SgMty of loc and V string and module_type and attributes
  | SgMtyAbs of loc and V string and attributes
  | SgMtyAlias of loc and V string and V (list string) and attributes
  | SgModSubst of loc and V string and longid and attributes
  | SgOpn of loc and longid and attributes
  | SgTyp of loc and V bool and V (list type_decl)
  | SgTypExten of loc and type_extension
  | SgUse of loc and V string and V (list (sig_item * loc))
  | SgVal of loc and V string and ctyp and attributes
  | SgXtr of loc and string and option (V sig_item)
  | SgFlAtt of loc and attribute_body
  | SgExten of loc and attribute_body ]
and with_constr =
  [ WcMod of loc and V (list string) and module_expr
  | WcMos of loc and V (list string) and module_expr
  | WcTyp of loc and V (list string) and V (list type_var) and V bool and ctyp
  | WcTys of loc and V (list string) and V (list type_var) and ctyp ]
and module_expr =
  [ MeAcc of loc and module_expr and module_expr
  | MeApp of loc and module_expr and module_expr
  | MeFun of loc and (V (option (V (option (V string)) * module_type))) and module_expr
  | MeStr of loc and V (list str_item)
  | MeTyc of loc and module_expr and module_type
  | MeUid of loc and V string
  | MeUnp of loc and expr and option module_type and option module_type
  | MeXtr of loc and string and option (V module_expr)
  | MeAtt of loc and module_expr and attribute_body
  | MeExten of loc and attribute_body ]
and str_item =
  [ StCls of loc and V (list (class_infos class_expr))
  | StClt of loc and V (list (class_infos class_type))
  | StDcl of loc and V (list str_item)
  | StDir of loc and V string and V (option expr)
  | StExc of loc and V extension_constructor and attributes
  | StExp of loc and expr and attributes
  | StExt of loc and V string and ctyp and V (list string) and attributes
  | StInc of loc and module_expr and attributes
  | StMod of loc and V bool and V (list (V (option (V string)) * module_expr * attributes))
  | StMty of loc and V string and module_type and attributes
  | StMtyAbs of loc and V string and attributes
  | StOpn of loc and V bool and module_expr and attributes
  | StTyp of loc and V bool and V (list type_decl)
  | StTypExten of loc and type_extension
  | StUse of loc and V string and V (list (str_item * loc))
  | StVal of loc and V bool and V (list (patt * expr * attributes))
  | StXtr of loc and string and option (V str_item)
  | StFlAtt of loc and attribute_body
  | StExten of loc and attribute_body ]
and type_decl =
  { tdIsDecl : bool ;
    tdNam : V (loc * V string);
    tdPrm : V (list type_var);
    tdPrv : V bool;
    tdDef : ctyp;
    tdCon : V (list (ctyp * ctyp));
    tdAttributes: attributes }
and generic_constructor = (loc * V string * V (list ctyp) * option ctyp * attributes)
and extension_constructor = [
    EcTuple of generic_constructor
  | EcRebind of V string and V (list string) and attributes
  ]
and type_extension =
  { teNam : V (loc * V (list string));
    tePrm : V (list type_var);
    tePrv : V bool;
    teECs : V (list extension_constructor) ;
    teAttributes: attributes }
and class_type =
  [ CtLong of loc and longid
  | CtLongLid of loc and longid and V string
  | CtLid of loc and V string
  | CtLop of loc and V bool and longid and class_type
  | CtCon of loc and class_type and V (list ctyp)
  | CtFun of loc and ctyp and class_type
  | CtSig of loc and V (option ctyp) and V (list class_sig_item)
  | CtXtr of loc and string and option (V class_type)
  | CtAtt of loc and class_type and attribute_body
  | CtExten of loc and attribute_body ]
and class_sig_item =
  [ CgCtr of loc and ctyp and ctyp and attributes
  | CgDcl of loc and V (list class_sig_item)
  | CgInh of loc and class_type and attributes
  | CgMth of loc and V bool and V string and ctyp and attributes
    (* first mutable, then virtual *)
  | CgVal of loc and V bool and V bool and V string and ctyp and attributes
  | CgVir of loc and V bool and V string and ctyp and attributes
  | CgFlAtt of loc and attribute_body
  | CgExten of loc and attribute_body ]
and class_expr =
  [ CeApp of loc and class_expr and expr
  | CeCon of loc and V (list string) and V (list ctyp)
  | CeFun of loc and patt and class_expr
  | CeLet of loc and V bool and V (list (patt * expr * attributes)) and class_expr
  | CeLop of loc and V bool and longid and class_expr
  | CeStr of loc and V (option patt) and V (list class_str_item)
  | CeTyc of loc and class_expr and class_type
  | CeXtr of loc and string and option (V class_expr)
  | CeAtt of loc and class_expr and attribute_body
  | CeExten of loc and attribute_body ]
and class_str_item =
  [ CrCtr of loc and ctyp and ctyp and attributes
  | CrDcl of loc and V (list class_str_item)
  | CrInh of loc and V bool and class_expr and V (option string) and attributes
  | CrIni of loc and expr and attributes
  | CrMth of loc and V bool and V bool and V string and V (option ctyp) and
      expr and attributes
  | CrVal of loc and V bool and V bool and V string and expr and attributes
  | CrVav of loc and V bool and V string and ctyp and attributes
  | CrVir of loc and V bool and V string and ctyp and attributes
  | CrFlAtt of loc and attribute_body
  | CrExten of loc and attribute_body ]

and payload = [
  StAttr of loc and V (list str_item)
| SiAttr of loc and V (list sig_item)
| TyAttr of loc and V ctyp
| PaAttr of loc and V patt and option (V expr)
]
and attribute_body = V (V string * payload)
and attributes_no_anti = list attribute_body
and attributes = V attributes_no_anti
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
