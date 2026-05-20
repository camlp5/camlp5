(* camlp5r *)
(* printers.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

[@@@warnerror "-generative-application-expects-unit";] ;

open Mlsyntax ;

module R = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module R = Parse_r.PA(Base)(QH) ;
end ;

module RP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module R = Parse_r.PA(Base)(QH) ;
  module RP = Parse_rp.PA(Base) ;
end ;

module RP_Q = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module R = Parse_r.PA(Base)(QH) ;
  module RP = Parse_rp.PA(Base) ;
  module Q = Parse_q_MLast.PA(Base)(QH) ;
end ;

module RP_PAQ = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module R = Parse_r.PA(Base)(QH) ;
  module RP = Parse_rp.PA(Base) ;
  module Q_ast_base = Parse_q_ast_base.PA(Base)(QH) ;
  module Q_ast = Parse_q_ast.PA(Base)(QH)(Q_ast_base) ;
end ;

module O = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module O = Parse_o.PA(Base)(QH) ;
end ;

module OP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module O = Parse_o.PA(Base)(QH) ;
  module OP = Parse_op.PA(Base) ;
end ;

module OP_PAQ = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module O = Parse_o.PA(Base)(QH) ;
  module OP = Parse_op.PA(Base) ;
  module Q_ast_base = Parse_q_ast_base.PA(Base)(QH) ;
  module Q_ast = Parse_q_ast.PA(Base)(QH)(Q_ast_base) ;
end ;

module OOP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module QH = Quotation.QuotationExpansion(Base);
  module O = Parse_o.PA(Base)(QH) ;
  module OOP = Parse_oop.PA(Base) ;
end ;
