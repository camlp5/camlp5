(* camlp5r pa_macro.cmo *)
(* $Id: mLast.mli,v 1.52 2007/12/27 10:30:24 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2008 *)

(* Module [MLast]: abstract syntax tree.

   This is undocumented because the AST is not supposed to be used
   directly; the good usage is to use the quotations representing
   these values in concrete syntax (see the Camlp5 documentation).
   See also the file q_MLast.ml in Camlp5 sources. *)

type loc = Ploc.t;

IFNDEF STRICT THEN
  DEFINE V t = t
ELSE
  DEFINE V t = Ploc.vala t
END;

type v 'a = V 'a;

type ctyp =
  [ TyAcc of loc and ctyp and ctyp
  | TyAli of loc and ctyp and ctyp
  | TyAny of loc
  | TyApp of loc and ctyp and ctyp
  | TyArr of loc and ctyp and ctyp
  | TyCls of loc and V (list string)
  | TyLab of loc and V string and ctyp
  | TyLid of loc and V string
  | TyMan of loc and ctyp and ctyp
  | TyObj of loc and V (list (string * ctyp)) and V bool
  | TyOlb of loc and V string and ctyp
  | TyPol of loc and V (list string) and ctyp
  | TyQuo of loc and V string
  | TyRec of loc and V (list (loc * string * bool * ctyp))
  | TySum of loc and V (list (loc * V string * V (list ctyp)))
  | TyTup of loc and V (list ctyp)
  | TyUid of loc and V string
  | TyVrn of loc and V (list poly_variant) and
      option (option (V (list string)))
  | IFDEF STRICT THEN
      TyXtr of loc and string and option (V ctyp)
    END ]
and poly_variant =
  [ PvTag of V string and V bool and V (list ctyp)
  | PvInh of ctyp ]
;

type type_var = (V string * (bool * bool));

type class_infos 'a =
  { ciLoc : loc;
    ciVir : V bool;
    ciPrm : (loc * V (list type_var));
    ciNam : V string;
    ciExp : 'a }
;

type patt =
  [ PaAcc of loc and patt and patt
  | PaAli of loc and patt and patt
  | PaAnt of loc and patt
  | PaAny of loc
  | PaApp of loc and patt and patt
  | PaArr of loc and V (list patt)
  | PaChr of loc and V string
  | PaInt of loc and V string and string
  | PaFlo of loc and V string
  | PaLab of loc and V string and option patt
  | PaLid of loc and V string
  | PaOlb of loc and V string and option (patt * V (option expr))
  | PaOrp of loc and patt and patt
  | PaRng of loc and patt and patt
  | PaRec of loc and V (list (patt * patt))
  | PaStr of loc and V string
  | PaTup of loc and V (list patt)
  | PaTyc of loc and patt and ctyp
  | PaTyp of loc and V (list string)
  | PaUid of loc and V string
  | PaVrn of loc and V string
  | IFDEF STRICT THEN
      PaXtr of loc and string and option (V patt)
    END ]
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
  | ExLab of loc and V string and option expr
  | ExLaz of loc and expr
  | ExLet of loc and V bool and V (list (patt * expr)) and expr
  | ExLid of loc and V string
  | ExLmd of loc and V string and module_expr and expr
  | ExMat of loc and expr and V (list (patt * V (option expr) * expr))
  | ExNew of loc and V (list string)
  | ExObj of loc and V (option patt) and V (list class_str_item)
  | ExOlb of loc and V string and option expr
  | ExOvr of loc and V (list (string * expr))
  | ExRec of loc and V (list (patt * expr)) and option expr
  | ExSeq of loc and V (list expr)
  | ExSnd of loc and expr and V string
  | ExSte of loc and expr and expr
  | ExStr of loc and V string
  | ExTry of loc and expr and V (list (patt * V (option expr) * expr))
  | ExTup of loc and V (list expr)
  | ExTyc of loc and expr and ctyp
  | ExUid of loc and V string
  | ExVrn of loc and V string
  | ExWhi of loc and expr and V (list expr)
  | IFDEF STRICT THEN
      ExXtr of loc and string and option (V expr)
    END ]
and module_type =
  [ MtAcc of loc and module_type and module_type
  | MtApp of loc and module_type and module_type
  | MtFun of loc and V string and module_type and module_type
  | MtLid of loc and V string
  | MtQuo of loc and V string
  | MtSig of loc and V (list sig_item)
  | MtUid of loc and V string
  | MtWit of loc and module_type and V (list with_constr)
  | IFDEF STRICT THEN
      MtXtr of loc and string and option (V module_type)
    END ]
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
  | SgUse of loc and string and list (sig_item * loc)
  | SgVal of loc and V string and ctyp
  | IFDEF STRICT THEN
      SgXtr of loc and string and option (V sig_item)
    END ]
and with_constr =
  [ WcTyp of loc and V (list string) and V (list type_var) and V bool and ctyp
  | WcMod of loc and V (list string) and module_expr ]
and module_expr =
  [ MeAcc of loc and module_expr and module_expr
  | MeApp of loc and module_expr and module_expr
  | MeFun of loc and V string and module_type and module_expr
  | MeStr of loc and V (list str_item)
  | MeTyc of loc and module_expr and module_type
  | MeUid of loc and V string
  | IFDEF STRICT THEN
      MeXtr of loc and string and option (V module_expr)
    END ]
and str_item =
  [ StCls of loc and V (list (class_infos class_expr))
  | StClt of loc and V (list (class_infos class_type))
  | StDcl of loc and V (list str_item)
  | StDir of loc and V string and V (option expr)
  | StExc of loc and V string and V (list ctyp) and V (list string)
  | StExp of loc and expr
  | StExt of loc and V string and ctyp and V (list string)
  | StInc of loc and module_expr
  | StMod of loc and V bool and V (list (V string * module_expr))
  | StMty of loc and V string and module_type
  | StOpn of loc and V (list string)
  | StTyp of loc and V (list type_decl)
  | StUse of loc and string and list (str_item * loc)
  | StVal of loc and V bool and V (list (patt * expr))
  | IFDEF STRICT THEN
      StXtr of loc and string and option (V str_item)
    END ]
and type_decl =
  { tdNam : (loc * V string);
    tdPrm : V (list type_var);
    tdPrv : V bool;
    tdDef : ctyp;
    tdCon : V (list (ctyp * ctyp)) }
and class_type =
  [ CtCon of loc and V (list string) and V (list ctyp)
  | CtFun of loc and ctyp and class_type
  | CtSig of loc and V (option ctyp) and V (list class_sig_item)
  | IFDEF STRICT THEN
      CtXtr of loc and string and option (V class_type)
    END ]
and class_sig_item =
  [ CgCtr of loc and ctyp and ctyp
  | CgDcl of loc and V (list class_sig_item)
  | CgInh of loc and class_type
  | CgMth of loc and V string and V bool and ctyp
  | CgVal of loc and V string and V bool and ctyp
  | CgVir of loc and V string and V bool and ctyp ]
and class_expr =
  [ CeApp of loc and class_expr and expr
  | CeCon of loc and V (list string) and V (list ctyp)
  | CeFun of loc and patt and class_expr
  | CeLet of loc and V bool and V (list (patt * expr)) and class_expr
  | CeStr of loc and V (option patt) and V (list class_str_item)
  | CeTyc of loc and class_expr and class_type
  | IFDEF STRICT THEN
      CeXtr of loc and string and option (V class_expr)
    END ]
and class_str_item =
  [ CrCtr of loc and ctyp and ctyp
  | CrDcl of loc and V (list class_str_item)
  | CrInh of loc and class_expr and V (option string)
  | CrIni of loc and expr
  | CrMth of loc and V string and V bool and expr and V (option ctyp)
  | CrVal of loc and V string and V bool and expr
  | CrVir of loc and V string and V bool and ctyp ]
;

external loc_of_ctyp : ctyp -> loc = "%field0";
external loc_of_patt : patt -> loc = "%field0";
external loc_of_expr : expr -> loc = "%field0";
external loc_of_module_type : module_type -> loc = "%field0";
external loc_of_module_expr : module_expr -> loc = "%field0";
external loc_of_sig_item : sig_item -> loc = "%field0";
external loc_of_str_item : str_item -> loc = "%field0";

external loc_of_class_type : class_type -> loc = "%field0";
external loc_of_class_sig_item : class_sig_item -> loc = "%field0";
external loc_of_class_expr : class_expr -> loc = "%field0";
external loc_of_class_str_item : class_str_item -> loc = "%field0";
