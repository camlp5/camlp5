(* camlp5r *)
(* pa_ounit2.ml,v *)

open Pcaml;
open Pa_extend;

EXTEND
  GLOBAL: expr;
  expr: LEVEL "<"
    [ [ e1 = SELF; ">:"; e2 = SELF →
        <:expr< OUnitTest.TestLabel $e1$ $e2$ >>
      | e1 = SELF; ">::"; e2 = SELF →
        <:expr< OUnitTest.TestLabel $e1$ (OUnitTest.TestCase  OUnitTest.Short  $e2$) >>
      | e1 = SELF; ">:::"; e2 = SELF →
        <:expr< OUnitTest.TestLabel $e1$ (OUnitTest.TestList $e2$) >>
      ] ]
  ;
END;
