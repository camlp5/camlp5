(* camlp5r *)
(* asttools.mli,v *)

val symbolchar_or : (char -> bool) -> int -> ?lim:int -> string -> bool;;
val symbolchar : int -> ?lim:int -> string -> bool;;
val dotsymbolchar : int -> ?lim:int -> string -> bool;;
val kwdopchar : string -> int -> bool;;
module Original :
  sig
    val is_prefixop : string -> bool;;
    val is_infixop0_0 : string -> bool;;
    val is_infixop0_1 : string -> bool;;
    val is_infixop0_2 : string -> bool;;
    val is_infixop0 : string -> bool;;
    val is_infixop1 : string -> bool;;
    val is_infixop2 : string -> bool;;
    val is_infixop3 : string -> bool;;
    val is_infixop4 : string -> bool;;
    val is_hashop : string -> bool;;
    val is_operator0 : string -> bool;;
    val is_andop : string -> bool;;
    val is_letop : string -> bool;;
    val is_operator : string -> bool;;
    val is_infix_operator : string -> bool;;
    val is_dotop : string -> bool;;
    val is_special_op : string -> bool;;
  end
;;
module Revised :
  sig
    val is_prefixop : string -> bool;;
    val is_infixop0_0 : string -> bool;;
    val is_infixop0_1 : string -> bool;;
    val is_infixop1 : string -> bool;;
    val is_infixop2 : string -> bool;;
    val is_infixop3 : string -> bool;;
    val is_infixop4 : string -> bool;;
    val is_hashop : string -> bool;;
    val is_andop : string -> bool;;
    val is_letop : string -> bool;;
    val is_infixop0_2 : string -> bool;;
    val is_infixop0 : string -> bool;;
    val is_operator0 : string -> bool;;
    val is_operator : string -> bool;;
    val is_infix_operator : string -> bool;;
    val is_dotop : string -> bool;;
    val is_special_op : string -> bool;;
  end
;;
