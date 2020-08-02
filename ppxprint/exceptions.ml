(* camlp5r *)
(* camlp5o *)
(* pp_MLast.ml,v *)

declare
  type t = exn == ..;
  value show _ = "<exn>";
  value pp pps _ = Format.fprintf pps "<exn>";
  declare end;
end;


