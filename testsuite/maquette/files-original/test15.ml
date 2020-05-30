module M = struct type t = { x : int; y : int };; end;;

let f {M.x; y} = x+y;;
