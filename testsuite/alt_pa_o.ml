(* camlp5r *)
(* pa_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Asttools;
open Mlsyntax.Original;

value gram =
  Grammar.gcreate
    {Plexing.tok_func _ = failwith "no loaded parsing module";
     Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
     Plexing.tok_match = fun []; Plexing.tok_text _ = "";
     Plexing.tok_comm = None}
;

do {
  let odfa = Plexer.dollar_for_antiquotation.val in
  let osrs = Plexer.simplest_raw_strings.val in
  Plexer.dollar_for_antiquotation.val := False;
  Plexer.simplest_raw_strings.val := True;
  Plexer.utf8_lexing.val := True;
  Grammar.Unsafe.gram_reinit gram (Plexer.gmake ());
  Plexer.dollar_for_antiquotation.val := odfa;
  Plexer.simplest_raw_strings.val := osrs
};

value argle1 : Grammar.Entry.e unit = Grammar.Entry.create gram "argle1";
value argle1b : Grammar.Entry.e unit = Grammar.Entry.create gram "argle1b";
value argle2 : Grammar.Entry.e unit = Grammar.Entry.create gram "argle2";
value int_or_dot : Grammar.Entry.e unit = Grammar.Entry.create gram "int_or_dot";

value add_argle () = 
EXTEND
  GLOBAL: argle1 argle1b argle2
  ;
  int_or_dot: [[ LIDENT -> () | "." -> () ]] ;
  argle1:
    [ NONA
      [ [ "when" | ]; LIDENT -> ()
      | [ "when" | ]; "." -> ()
      ] ]
  ;
  argle1b:
    [ NONA
      [ OPT [ "when" ]; LIDENT -> ()
      | OPT [ "when" ]; "." -> ()
      ] ]
  ;
  argle2:
    [ [ [ "when" | ]; int_or_dot ->
          ()
      ] ]
  ;

END
;

match Sys.getenv "HAS_ARGLE" with [
  exception Not_found -> ()
| "true" -> add_argle ()
| _ -> () ]

;

value pa_argle1 s = s |> Stream.of_string |> Grammar.Entry.parse argle1 ;
value pa_argle1b s = s |> Stream.of_string |> Grammar.Entry.parse argle1b ;
value pa_argle2 s = s |> Stream.of_string |> Grammar.Entry.parse argle2 ;
