(* camlp5r *)
(* printers.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

[@@@warnerror "-generative-application-expects-unit";] ;

open Mlsyntax ;

module PrettyPrint (P : PRINTERS) = struct
value pp eprinter pps x =
  Fmt.(pf pps "%s" (Eprinter.apply eprinter Pprintf.empty_pc x)) ;

value show eprinter x =
  Eprinter.apply eprinter Pprintf.empty_pc x ;

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

  value show_attribute_body = show P.pr_attribute_body ;
  value show_expr = show P.pr_expr ;
  value show_patt = show P.pr_patt ;
  value show_ctyp = show P.pr_ctyp ;
  value show_str_item = show P.pr_str_item ;
  value show_sig_item = show P.pr_sig_item ;
  value show_longident = show P.pr_longident ;
  value show_module_expr = show P.pr_module_expr ;
  value show_module_type = show P.pr_module_type ;
  value show_class_sig_item = show P.pr_class_sig_item ;
  value show_class_str_item = show P.pr_class_str_item ;
  value show_class_type = show P.pr_class_type ;
  value show_class_expr = show P.pr_class_expr ;

end;

module R = struct
  module Base = PrintBase(struct end) ;
  module R = Print_r.PP(Base) ;
  module Pretty = PrettyPrint(Base.Printers) ;
end ;

module RO = struct
  module Base = PrintBase(struct end) ;
  module R = Print_r.PP(Base) ;
  module RO = Print_ro.PP(Base)(R) ;
  module Pretty = PrettyPrint(Base.Printers) ;
end ;

module RP = struct
  module Base = PrintBase(struct end) ;
  module R = Print_r.PP(Base) ;
  module RO = Print_ro.PP(Base)(R) ;
  module RP = Print_rp.PP(Base)(R) ;
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
