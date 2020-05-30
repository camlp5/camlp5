
class type virtual ct = object
  val mutable virtual x : int
  val virtual mutable y : int
  method private virtual f : int
  method virtual private g : int
end;;

class virtual c = object
  val mutable virtual x : int
  val virtual mutable y : int
  method private virtual f : int
  method virtual private g : int
end;;
