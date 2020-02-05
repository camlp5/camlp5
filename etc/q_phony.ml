(* camlp5r *)
(* q_phony.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "pa_extend.cmo";
#load "pa_extprint.cmo";
#load "q_MLast.cmo";
#load "pa_pprintf.cmo";

open Pcaml;

value t = ref "";

value make_quot name s =
if name = "" then "<<" ^ s ^ ">>"
else if String.length s > 0 && s.[0] = '@' then
   "<:" ^ name ^ ":<" ^ (String.sub s 1 (String.length s - 1)) ^ ">>"
else "<:" ^ name ^ "<" ^ s ^ ">>"
;

value expr_fun = fun s ->
        let t = make_quot t.val s
        in
        let loc = Ploc.dummy in
<:expr< $uid:t$ >> ;

value patt_fun = fun s ->
        let t = make_quot t.val s
        in
        let loc = Ploc.dummy in
        <:patt< $uid:t$ >> ;


Quotation.add ""
  (Quotation.ExAst
     (expr_fun,
      patt_fun))
;

Quotation.default.val := "";
Quotation.translate.val := fun s -> do { t.val := s; "" };

