open Pcaml ;
EXTEND
  expr:
  [ [ "sum";
      e =
      FOLD0 (fun e1 e2 -> <:expr< $e2$ + $e1$ >>) <:expr< 0 >>
        expr SEP ";";
      "end" -> e ] ] ;
END;
