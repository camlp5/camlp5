(* camlp5r *)
(* printers.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

[@@@warnerror "-generative-application-expects-unit";] ;

open Mlsyntax ;

module PrettyParse(P : PARSERS) = struct

module String = struct
value pa entry s =
  s |> Stream.of_string |> Grammar.Entry.parse entry ;

value attribute_body = pa P.attribute_body ;
value interf  = pa P.interf ;
value implem  = pa P.implem ;
value top_phrase  = pa P.top_phrase ;
value use_file  = pa P.use_file ;
value functor_parameter  = pa P.functor_parameter ;
value module_type  = pa P.module_type ;
value longident  = pa P.longident ;
value longident_lident  = pa P.longident_lident ;
value extended_longident  = pa P.extended_longident ;
value module_expr  = pa P.module_expr ;
value signature  = pa P.signature ;
value structure  = pa P.structure ;
value sig_item  = pa P.sig_item ;
value str_item  = pa P.str_item ;
value expr  = pa P.expr ;
value patt  = pa P.patt ;
value ipatt  = pa P.ipatt ;
value ctyp  = pa P.ctyp ;
value let_binding  = pa P.let_binding ;
value type_decl  = pa P.type_decl ;
value type_extension  = pa P.type_extension ;
value extension_constructor  = pa P.extension_constructor ;
value match_case  = pa P.match_case ;
value constructor_declaration  = pa P.constructor_declaration ;
value label_declaration  = pa P.label_declaration ;
value with_constr  = pa P.with_constr ;
value poly_variant  = pa P.poly_variant ;
value class_sig_item  = pa P.class_sig_item ;
value class_str_item  = pa P.class_str_item ;
value class_expr  = pa P.class_expr ;
value class_expr_simple  = pa P.class_expr_simple ;
value class_type  = pa P.class_type ;
value alg_attribute  = pa P.alg_attribute ;
value alg_attributes  = pa P.alg_attributes ;
value ext_attributes  = pa P.ext_attributes ;

value stream_expr  = pa P.stream_expr ;
value stream_parser  = pa P.stream_parser ;
value stream_match  = pa P.stream_match ;
end ;

module Stream = struct
value pa entry strm =
  Grammar.Entry.parse entry strm ;

value attribute_body = pa P.attribute_body ;
value interf  = pa P.interf ;
value implem  = pa P.implem ;
value top_phrase  = pa P.top_phrase ;
value use_file  = pa P.use_file ;
value functor_parameter  = pa P.functor_parameter ;
value module_type  = pa P.module_type ;
value longident  = pa P.longident ;
value longident_lident  = pa P.longident_lident ;
value extended_longident  = pa P.extended_longident ;
value module_expr  = pa P.module_expr ;
value signature  = pa P.signature ;
value structure  = pa P.structure ;
value sig_item  = pa P.sig_item ;
value str_item  = pa P.str_item ;
value expr  = pa P.expr ;
value patt  = pa P.patt ;
value ipatt  = pa P.ipatt ;
value ctyp  = pa P.ctyp ;
value let_binding  = pa P.let_binding ;
value type_decl  = pa P.type_decl ;
value type_extension  = pa P.type_extension ;
value extension_constructor  = pa P.extension_constructor ;
value match_case  = pa P.match_case ;
value constructor_declaration  = pa P.constructor_declaration ;
value label_declaration  = pa P.label_declaration ;
value with_constr  = pa P.with_constr ;
value poly_variant  = pa P.poly_variant ;
value class_sig_item  = pa P.class_sig_item ;
value class_str_item  = pa P.class_str_item ;
value class_expr  = pa P.class_expr ;
value class_expr_simple  = pa P.class_expr_simple ;
value class_type  = pa P.class_type ;
value alg_attribute  = pa P.alg_attribute ;
value alg_attributes  = pa P.alg_attributes ;
value ext_attributes  = pa P.ext_attributes ;

value stream_expr  = pa P.stream_expr ;
value stream_parser  = pa P.stream_parser ;
value stream_match  = pa P.stream_match ;
end ;

end ;

module R = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module R = Parse_r.PA(Base)(QH) ;
  module Pretty = PrettyParse(Base.Parsers) ;
end ;

module RP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module R = Parse_r.PA(Base)(QH) ;
  module RP = Parse_rp.PA(Base) ;
  module Pretty = PrettyParse(Base.Parsers) ;
end ;

module RP_Q = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module R = Parse_r.PA(Base)(QH) ;
  module RP = Parse_rp.PA(Base) ;
  module Q = Parse_q_MLast.PA(Base)(QH) ;
  module Pretty = PrettyParse(Base.Parsers) ;
end ;

module RP_PAQ = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module R = Parse_r.PA(Base)(QH) ;
  module RP = Parse_rp.PA(Base) ;
  module Q_ast_base = Parse_q_ast_base.PA(Base)(QH) ;
  module Q_ast = Parse_q_ast.PA(Base)(QH)(Q_ast_base) ;
  module Pretty = PrettyParse(Base.Parsers) ;
end ;

module O = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module O = Parse_o.PA(Base)(QH) ;
  module Pretty = PrettyParse(Base.Parsers) ;
end ;

module OP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module O = Parse_o.PA(Base)(QH) ;
  module OP = Parse_op.PA(Base) ;
  module Pretty = PrettyParse(Base.Parsers) ;
end ;

module OP_PAQ = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module O = Parse_o.PA(Base)(QH) ;
  module OP = Parse_op.PA(Base) ;
  module Q_ast_base = Parse_q_ast_base.PA(Base)(QH) ;
  module Q_ast = Parse_q_ast.PA(Base)(QH)(Q_ast_base) ;
  module Pretty = PrettyParse(Base.Parsers) ;
end ;

module OOP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module O = Parse_o.PA(Base)(QH) ;
  module OOP = Parse_oop.PA(Base) ;
  module Pretty = PrettyParse(Base.Parsers) ;
end ;
