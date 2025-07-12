(* camlp5r *)
(* pp_parsetree.ml,v *)

IFDEF BOOTSTRAP THEN

module Lexing = struct
[%%import: Lexing.position] [@@deriving show]
end
module Location = struct
[%%import: Location.t] [@@deriving show]
[%%import: 'a Location.loc] [@@deriving show]
end
module Longident = struct
[%%import: Longident.t] [@@deriving show]
end
module Asttypes = struct
[%%import: Asttypes.loc] [@@deriving show]
[%%import: Asttypes.arg_label] [@@deriving show]
[%%import: Asttypes.label] [@@deriving show]
[%%import: Asttypes.closed_flag] [@@deriving show]
[%%import: Asttypes.rec_flag] [@@deriving show]
[%%import: Asttypes.direction_flag] [@@deriving show]
[%%import: Asttypes.private_flag] [@@deriving show]
[%%import: Asttypes.mutable_flag] [@@deriving show]
[%%import: Asttypes.virtual_flag] [@@deriving show]
[%%import: Asttypes.override_flag] [@@deriving show]
[%%import: Asttypes.variance] [@@deriving show]
[%%import: Asttypes.injectivity] [@@deriving show]
end
[%%import: Parsetree.constant] [@@deriving show]
[%%import: Parsetree.location_stack] [@@deriving show]
[%%import: Parsetree.attribute] [@@deriving show]

END


