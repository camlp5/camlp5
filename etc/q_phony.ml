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

Quotation.add ""
  (Quotation.ExAst
     (fun s ->
        let t =
          if t.val = "" then "<<" ^ s ^ ">>"
          else "<:" ^ t.val ^ "<" ^ s ^ ">>"
        in
        let loc = Ploc.dummy in
        <:expr< $uid:t$ >>,
      fun s ->
        let t =
          if t.val = "" then "<<" ^ s ^ ">>"
          else "<:" ^ t.val ^ "<" ^ s ^ ">>"
        in
        let loc = Ploc.dummy in
        <:patt< $uid:t$ >>))
;

Quotation.default.val := "";
Quotation.translate.val := fun s -> do { t.val := s; "" };

