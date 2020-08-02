(* camlp5o *)
(* pp_MLast.ml,v *)

IFDEF BOOTSTRAP THEN

type t = exn = .. [@@deriving show]

type t +=
    Help of string [@rebind_to Arg.Help]
  | Bad of string [@rebind_to Arg.Bad]
  | Finally_raised of t [@rebind_to Fun.Finally_raised]
  | Undefined [@rebind_to Lazy.Undefined]
  | Parse_error [@rebind_to Parsing.Parse_error]
  | QueueEmpty [@rebind_to Queue.Empty]
  | Scan_failure of string [@rebind_to Scanf.Scan_failure]
  | StackEmpty [@rebind_to Stack.Empty]
  | Exit [@rebind_to Stdlib.Exit]
  | Match_failure of (string * int * int) [@rebind_to Stdlib.Match_failure]
  | Assert_failure of (string * int * int) [@rebind_to Stdlib.Assert_failure]
  | Invalid_argument of string [@rebind_to Stdlib.Invalid_argument]
  | Failure of string [@rebind_to Stdlib.Failure]
  | Not_found [@rebind_to Stdlib.Not_found]
  | Out_of_memory [@rebind_to Stdlib.Out_of_memory]
  | Stack_overflow [@rebind_to Stdlib.Stack_overflow]
  | Sys_error of string [@rebind_to Stdlib.Sys_error]
  | End_of_file [@rebind_to Stdlib.End_of_file]
  | Division_by_zero [@rebind_to Stdlib.Division_by_zero]
  | Sys_blocked_io [@rebind_to Stdlib.Sys_blocked_io]
  | Undefined_recursive_module of (string * int * int) [@rebind_to Stdlib.Undefined_recursive_module]
  | StreamFailure [@rebind_to Stream.Failure]
  | Error of string [@rebind_to Stream.Error]
  | Break [@rebind_to Sys.Break]
[@@deriving show]

ELSE
END


