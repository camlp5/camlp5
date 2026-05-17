(* camlp5r *)
(* printers.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

[@@@warnerror "-generative-application-expects-unit";] ;

open Mlsyntax ;

module R = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(struct end) ;
  module R = Parse_r.PA(Lexer)(Base) ;
end ;

module RP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(struct end) ;
  module R = Parse_r.PA(Lexer)(Base) ;
  module RP = Parse_rp.PA(Lexer)(Base) ;
end ;

module O = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(struct end) ;
  module O = Parse_o.PA(Lexer)(Base) ;
end ;

module OP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(struct end) ;
  module O = Parse_o.PA(Lexer)(Base) ;
  module OP = Parse_op.PA(Lexer)(Base) ;
end ;

module OOP = struct
  module Lexer = Plexer.Make(struct end) ;
  module Base = ParseBase(struct end) ;
  module O = Parse_o.PA(Lexer)(Base) ;
  module OOP = Parse_oop.PA(Lexer)(Base) ;
end ;
