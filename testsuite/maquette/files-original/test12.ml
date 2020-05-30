
module M = struct
  type t1 = { a : int ; b : string } ;;
end ;;

let x = M.{ a = 1 ; b = "foo" } ;;

let f r b = { r with M.b } ;;

