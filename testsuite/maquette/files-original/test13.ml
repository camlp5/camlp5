let f = function
 | lazy (), _, {contents=None} -> 0
 | _, lazy (), {contents=Some x} -> 1
;;
let g = lazy () ;;
