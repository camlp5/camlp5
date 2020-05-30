      let ( --> ) q1 t q2 =
        match t with
        | QEPSILON -> epsilons := (q1,q2) :: !epsilons; q1
        | QCLASS cl -> transitions := (q1,cl,q2) :: !transitions; q1
 ;;

let _ = (q --> QCLASS (Atom (u.[i], u.[i]))) q' in 2 ;;

a --> b ;;

let used = !!free t in 1 ;;

(a + b) c ;;
