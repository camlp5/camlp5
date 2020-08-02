(* camlp5r *)
(* camlp5o *)
(* pp_MLast.ml,v *)

declare
  type t = exn == ..;
  value show : exn -> string;
  value pp : Format.formatter -> exn -> unit;
  declare end;
end;


