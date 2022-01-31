val equal : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val uniq1 : ('a -> 'a -> int) -> 'a -> 'a list -> 'a list
val uniq : ('a -> 'a -> int) -> 'a list -> 'a list
