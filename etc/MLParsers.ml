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

module O = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module O = Parse_o.PA(Base) ;
end ;

module OP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module O = Parse_o.PA(Base) ;
  module OP = Parse_op.PA(Base) ;
end ;

module OOP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(Lexer) ;
  module O = Parse_o.PA(Base) ;
  module OOP = Parse_oop.PA(Base) ;
end ;
