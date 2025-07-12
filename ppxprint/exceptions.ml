(* camlp5r *)
type t = exn == ..[@@"deriving_inline" show;];
[@@@"ocaml.text" "/*";];
module M_pp =
  struct
    type nonrec pp = { f : mutable Fmt.t t };
    value f =
      {f _ =
        invalid_arg
          ("pp: Maybe a [@@deriving show] is missing when extending the type " ^
           "t")}
    ;
  end
;
[@@@"ocaml.text" "/*";];
value pp x = M_pp.f.M_pp.f x;
value show arg = Format.asprintf "%a" M_pp.f.M_pp.f arg;
[@@@"end"];
type t +=
  [ Help = Arg.Help[@"name" "Arg.Help";]
  | Bad = Arg.Bad[@"name" "Arg.Bad";]
  | Finally_raised = Fun.Finally_raised[@"name" "Fun.Finally_raised";]
  | Undefined = Lazy.Undefined[@"name" "Lazy.Undefined";]
  | Parse_error = Parsing.Parse_error[@"name" "Parsing.Parse_error";]
  | QueueEmpty = Queue.Empty[@"name" "Queue.Empty";]
  | Scan_failure = Scanf.Scan_failure[@"name" "Scanf.Scan_failure";]
  | StackEmpty = Stack.Empty[@"name" "Stack.Empty";]
  | Exit = Stdlib.Exit[@"name" "Stdlib.Exit";]
  | Match_failure = Stdlib.Match_failure[@"name" "Stdlib.Match_failure";]
  | Assert_failure = Stdlib.Assert_failure[@"name" "Stdlib.Assert_failure";]
  | Invalid_argument
    = Stdlib.Invalid_argument[@"name" "Stdlib.Invalid_argument";]
  | Failure = Stdlib.Failure[@"name" "Stdlib.Failure";]
  | Not_found = Stdlib.Not_found[@"name" "Stdlib.Not_found";]
  | Out_of_memory = Stdlib.Out_of_memory[@"name" "Stdlib.Out_of_memory";]
  | Stack_overflow = Stdlib.Stack_overflow[@"name" "Stdlib.Stack_overflow";]
  | Sys_error = Stdlib.Sys_error[@"name" "Stdlib.Sys_error";]
  | End_of_file = Stdlib.End_of_file[@"name" "Stdlib.End_of_file";]
  | Division_by_zero
    = Stdlib.Division_by_zero[@"name" "Stdlib.Division_by_zero";]
  | Sys_blocked_io = Stdlib.Sys_blocked_io[@"name" "Stdlib.Sys_blocked_io";]
  | Undefined_recursive_module
    = Stdlib.Undefined_recursive_module[@"name" "Stdlib.Undefined_recursive_module";]
  | StreamFailure = Stream.Failure[@"name" "Stream.Failure";]
  | Error = Stream.Error[@"name" "Stream.Error";]
  | Break = Sys.Break[@"name" "Sys.Break";] ][@@"deriving_inline" show;]
;
let open M_pp in
let fallback = f.f in
f.f :=
  fun ofmt →
    fun
    [ Help v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Arg.Help@ %a)@]"
          (fun ofmt arg →
             let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
          v0
    | Bad v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Arg.Bad@ %a)@]"
          (fun ofmt arg →
             let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
          v0
    | Finally_raised v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Fun.Finally_raised@ %a)@]" pp v0
    | Undefined →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Lazy.Undefined@]"
    | Parse_error →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Parsing.Parse_error@]"
    | QueueEmpty →
        let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "@[<2>Queue.Empty@]"
    | Scan_failure v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Scanf.Scan_failure@ %a)@]"
          (fun ofmt arg →
             let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
          v0
    | StackEmpty →
        let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "@[<2>Stack.Empty@]"
    | Exit →
        let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "@[<2>Stdlib.Exit@]"
    | Match_failure v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Stdlib.Match_failure@ %a)@]"
          (fun (ofmt : Format.formatter) (v0, v1, v2) →
             let open Ppxprint_runtime.Runtime.Fmt in
             pf ofmt "(@[%a,@ %a,@ %a@])"
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
               v0
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
               v1
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
               v2)
          v0
    | Assert_failure v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Stdlib.Assert_failure@ %a)@]"
          (fun (ofmt : Format.formatter) (v0, v1, v2) →
             let open Ppxprint_runtime.Runtime.Fmt in
             pf ofmt "(@[%a,@ %a,@ %a@])"
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
               v0
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
               v1
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
               v2)
          v0
    | Invalid_argument v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Stdlib.Invalid_argument@ %a)@]"
          (fun ofmt arg →
             let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
          v0
    | Failure v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Stdlib.Failure@ %a)@]"
          (fun ofmt arg →
             let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
          v0
    | Not_found →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Stdlib.Not_found@]"
    | Out_of_memory →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Stdlib.Out_of_memory@]"
    | Stack_overflow →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Stdlib.Stack_overflow@]"
    | Sys_error v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Stdlib.Sys_error@ %a)@]"
          (fun ofmt arg →
             let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
          v0
    | End_of_file →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Stdlib.End_of_file@]"
    | Division_by_zero →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Stdlib.Division_by_zero@]"
    | Sys_blocked_io →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Stdlib.Sys_blocked_io@]"
    | Undefined_recursive_module v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Stdlib.Undefined_recursive_module@ %a)@]"
          (fun (ofmt : Format.formatter) (v0, v1, v2) →
             let open Ppxprint_runtime.Runtime.Fmt in
             pf ofmt "(@[%a,@ %a,@ %a@])"
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
               v0
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
               v1
               (fun ofmt arg →
                  let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
               v2)
          v0
    | StreamFailure →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "@[<2>Stream.Failure@]"
    | Error v0 →
        let open Ppxprint_runtime.Runtime.Fmt in
        pf ofmt "(@[<2>Stream.Error@ %a)@]"
          (fun ofmt arg →
             let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
          v0
    | Break →
        let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "@[<2>Sys.Break@]"
    | z → fallback ofmt z ];
[@@@"end"];
value print_exn exn = Some (show exn);
Printexc.register_printer print_exn;


