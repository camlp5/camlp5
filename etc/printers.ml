(* camlp5r *)
(* printers.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Mlsyntax ;

module PrettyPrint (P : PRINTERS) = struct
value pp eprinter pps x =
  Fmt.(pf pps "%s" (Eprinter.apply eprinter Pprintf.empty_pc x)) ;

  value pp_attribute_body = pp P.pr_attribute_body ;
  value pp_expr = pp P.pr_expr ;
  value pp_patt = pp P.pr_patt ;
  value pp_ctyp = pp P.pr_ctyp ;
  value pp_str_item = pp P.pr_str_item ;
  value pp_sig_item = pp P.pr_sig_item ;
  value pp_longident = pp P.pr_longident ;
  value pp_module_expr = pp P.pr_module_expr ;
  value pp_module_type = pp P.pr_module_type ;
  value pp_class_sig_item = pp P.pr_class_sig_item ;
  value pp_class_str_item = pp P.pr_class_str_item ;
  value pp_class_type = pp P.pr_class_type ;
  value pp_class_expr = pp P.pr_class_expr ;
end;

module R = struct
  module Base = PrintBase(struct end) ;
  module R = Print_r.PP(Base) ;
  module Pretty = PrettyPrint(Base.Printers) ;
end ;

module RO = struct
  module Base = PrintBase(struct end) ;
  module R = Print_r.PP(Base) ;
  module RO = Print_ro.PP(Base) ;
  module Pretty = PrettyPrint(Base.Printers) ;
end ;

module RP = struct
  module Base = PrintBase(struct end) ;
  module R = Print_r.PP(Base) ;
  module RO = Print_ro.PP(Base) ;
  module RP = Print_rp.PP(Base) ;
  module Pretty = PrettyPrint(Base.Printers) ;
end ;

module O = struct
  module Base = PrintBase(struct end) ;
  module O = Print_o.PP(Base) ;
  module Pretty = PrettyPrint(Base.Printers) ;
end ;

module OP = struct
  module Base = PrintBase(struct end) ;
  module O = Print_o.PP(Base) ;
  module OP = Print_op.PP(Base) ;
  module Pretty = PrettyPrint(Base.Printers) ;
end ;
