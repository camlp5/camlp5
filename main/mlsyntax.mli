(* camlp5r *)
(* asttools.mli,v *)

value symbolchar_or : (char → bool) → int → ?lim:int → string → bool;
value symbolchar : int → ?lim:int → string → bool;
value dotsymbolchar : int → ?lim:int → string → bool;
value kwdopchar : string → int → bool;
module Original :
  sig
    value is_prefixop : string → bool;
    value is_infixop0_0 : string → bool;
    value is_infixop0_1 : string → bool;
    value is_infixop0_2 : string → bool;
    value is_infixop0 : string → bool;
    value is_infixop1 : string → bool;
    value is_infixop2 : string → bool;
    value is_infixop3 : string → bool;
    value is_infixop4 : string → bool;
    value is_hashop : string → bool;
    value is_operator0 : string → bool;
    value is_andop : string → bool;
    value is_letop : string → bool;
    value is_operator : string → bool;
    value is_infix_operator : string → bool;
    value is_dotop : string → bool;
    value is_special_op : string → bool;
  end
;
module Revised :
  sig
    value is_prefixop : string → bool;
    value is_infixop0_0 : string → bool;
    value is_infixop0_1 : string → bool;
    value is_infixop1 : string → bool;
    value is_infixop2 : string → bool;
    value is_infixop3 : string → bool;
    value is_infixop4 : string → bool;
    value is_hashop : string → bool;
    value is_andop : string → bool;
    value is_letop : string → bool;
    value is_infixop0_2 : string → bool;
    value is_infixop0 : string → bool;
    value is_operator0 : string → bool;
    value is_operator : string → bool;
    value is_infix_operator : string → bool;
    value is_dotop : string → bool;
    value is_special_op : string → bool;
  end
;
