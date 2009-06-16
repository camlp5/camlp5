(* camlp5r -I . q_MLast.cmo pa_extprint.cmo pa_pprintf.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007-2008 *)

(* heuristic to rebuild the pprintf statement from the AST *)

open Pcaml;

value is_pprintf fmt bef aft =
  match (bef, aft) with
  [ (<:expr< $lid:pc1$.Pprintf.bef >>, <:expr< $lid:pc2$.Pprintf.aft >>) ->
      pc1 = pc2 &&
      String.length fmt > 3 && fmt.[0] = '%' && fmt.[1] = 's' &&
      fmt.[String.length fmt-2] = '%' && fmt.[String.length fmt-1] = 's'
  | _ -> False ]
;

value pc_of =
  fun
  [ <:expr< $lid:pc$.Pprintf.$_$ >> -> pc
  | _ -> invalid_arg "pc_of" ]
;

EXTEND_PRINTER
  pr_expr: LEVEL "apply"
    [ [ <:expr< Pretty.sprintf $str:fmt$ $bef$ $e1$ $e2$ $aft$ >>
        when is_pprintf fmt bef aft ->
          let fmt = String.sub fmt 2 (String.length fmt - 4) in
          pprintf pc "@[<2>pprintf@ %s@ \"%s\"@ %p@ %p@]" (pc_of bef) fmt
            next e1 next e2
      | <:expr< Pretty.sprintf $str:fmt$ $bef$ $e$ $aft$ >>
        when is_pprintf fmt bef aft ->
          let fmt = String.sub fmt 2 (String.length fmt - 4) in
          pprintf pc "@[<2>pprintf@ %s@ \"%s\"@ %p@]" (pc_of bef) fmt next e
      | <:expr< Pretty.sprintf $str:fmt$ $bef$ $aft$ >>
        when is_pprintf fmt bef aft ->
          let fmt = String.sub fmt 2 (String.length fmt - 4) in
          pprintf pc "@[<2>pprintf@ %s@ \"%s\"@]" (pc_of bef) fmt
      | <:expr<
           $f$
             {($lid:pc1$) with
              Pprintf.bef =
                Pretty.sprintf $str:fmt$ $lid:pc2$.Pprintf.bef $e$}
             $a$
        >>
        when
          pc1 = pc2 &&
          String.length fmt > 1 && fmt.[0] = '%' && fmt.[1] = 's'
        ->
          let fmt = String.sub fmt 2 (String.length fmt - 2) ^ "%p" in
          pprintf pc "@[<2>pprintf@ %s@ \"%s\"@ %p@ %p@ %p@]" pc1 fmt
            next e next f next a
      | <:expr<
          $f$
            {($lid:pc1$) with
             Pprintf.aft = Pretty.sprintf $str:fmt$ $lid:pc2$.Pprintf.aft}
            $a$
        >>
        when
          pc1 = pc2 &&
          String.length fmt > 1 && fmt.[String.length fmt - 2] = '%' &&
          fmt.[String.length fmt - 1] = 's'
        ->
         let fmt = "%p" ^ String.sub fmt 0 (String.length fmt - 2) in
         pprintf pc "@[<2>pprintf@ %s@ \"%s\"@ %p@ %p@]" pc1 fmt
            next f next a ] ]
  ;
END;
