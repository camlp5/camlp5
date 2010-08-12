(* camlp5r q_MLast.cmo pa_extend.cmo *)
(* $Id: comp_head.ml.tpl,v 1.10 2010/08/12 11:50:44 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

module P =
  struct
    value gloc bp strm = Grammar.loc_of_token_interval bp (Stream.count strm);
    value vala symb = parser [: a = symb :] -> <:vala< a >>;
    value list0 symb =
      let rec loop al =
        parser
        [ [: a = symb; a = loop [a :: al] ! :] -> a
        | [: :] -> al ]
      in
      parser [: a = loop [] :] -> List.rev a
    ;
    value list0sep symb sep =
      let rec kont al =
        parser
        [ [: v = sep; a = symb; a = kont [a :: al] ! :] -> a
        | [: :] -> al ]
      in
      parser
      [ [: a = symb; a = kont [a] ! :] -> List.rev a
      | [: :] -> [] ]
    ;
    value list1 symb =
      let rec loop al =
        parser
        [ [: a = symb; a = loop [a :: al] ! :] -> a
        | [: :] -> al ]
      in
      parser [: a = symb; a = loop [a] ! :] -> List.rev a
    ;
    value list1sep symb sep =
      let rec kont al =
        parser
        [ [: v = sep; a = symb; a = kont [a :: al] ! :] -> a
        | [: :] -> al ]
      in
      parser [: a = symb; a = kont [a] ! :] -> List.rev a
    ;
    value option f =
      parser
      [ [: a = f :] -> Some a
      | [: :] -> None ]
    ;
    value bool f =
      parser
      [ [: _ = f :] -> True
      | [: :] -> False ]
    ;
    value token (p_con, p_prm) =
      if p_prm = "" then parser [: `(con, prm) when con = p_con :] -> prm
      else parser [: `(con, prm) when con = p_con && prm = p_prm :] -> prm
    ;
    value orzero f f0 =
      parser
      [ [: a = f :] -> a
      | [: a = f0 :] -> a ]
    ;
    value error entry prev_symb symb =
      symb ^ " expected" ^
      (if prev_symb = "" then "" else " after " ^ prev_symb) ^ " (in [" ^
      entry ^ "])"
    ;
    value lexer = Plexer.gmake ();
  end
;

(****************************************)

