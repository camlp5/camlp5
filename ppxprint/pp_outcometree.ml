(* camlp5r *)
module Type_immediacy =
  struct
    type t =
      Type_immediacy.t == [ Unknown | Always | Always_on_64bits ][@@"deriving_inline" show;]
    ;
    value rec pp : Fmt.t t =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Unknown →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Type_immediacy.Unknown@]"
           | Always →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Type_immediacy.Always@]"
           | Always_on_64bits →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Type_immediacy.Always_on_64bits@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show : t → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
  end
;
open Pp_parsetree;
type out_name =
  Outcometree.out_name == { printed_name : mutable string }[@@"deriving_inline" show;]
;
value rec pp_out_name : Fmt.t out_name =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt ({printed_name = v_printed_name} : out_name) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>{ @[Outcometree.printed_name =@ %a@] }@]"
         (fun ofmt arg →
            let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
         v_printed_name)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_name : out_name → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_name arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type out_ident =
  Outcometree.out_ident ==
    [ Oide_apply of out_ident and out_ident
    | Oide_dot of out_ident and string
    | Oide_ident of out_name ][@@"deriving_inline" show;]
;
value rec pp_out_ident : Fmt.t out_ident =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Oide_apply v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oide_apply@ (@,%a,@ %a@,))@]"
             pp_out_ident v0 pp_out_ident v1
       | Oide_dot v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oide_dot@ (@,%a,@ %a@,))@]" pp_out_ident
             v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
       | Oide_ident v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oide_ident@ %a)@]" pp_out_name v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_ident : out_ident → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_ident arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type out_string =
  Outcometree.out_string == [ Ostr_string | Ostr_bytes ][@@"deriving_inline" show;]
;
value rec pp_out_string : Fmt.t out_string =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Ostr_string →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Ostr_string@]"
       | Ostr_bytes →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Ostr_bytes@]" ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_string : out_string → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_string arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type out_attribute =
  Outcometree.out_attribute == { oattr_name : string }[@@"deriving_inline" show;]
;
value rec pp_out_attribute : Fmt.t out_attribute =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt ({oattr_name = v_oattr_name} : out_attribute) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>{ @[Outcometree.oattr_name =@ %a@] }@]"
         (fun ofmt arg →
            let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
         v_oattr_name)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_attribute : out_attribute → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_attribute arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type out_value =
  Outcometree.out_value ==
    [ Oval_array of list out_value
    | Oval_char of char
    | Oval_constr of out_ident and list out_value
    | Oval_ellipsis
    | Oval_float of float
    | Oval_int of int
    | Oval_int32 of int32
    | Oval_int64 of int64
    | Oval_nativeint of nativeint
    | Oval_list of list out_value
    | Oval_printer of Format.formatter → unit
    | Oval_record of list (out_ident * out_value)
    | Oval_string of string and int and out_string
    | Oval_stuff of string
    | Oval_tuple of list out_value
    | Oval_variant of string and option out_value ][@@"deriving_inline" show;]
;
value rec pp_out_value : Fmt.t out_value =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Oval_array v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_array@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_value) arg)
             v0
       | Oval_char v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_char@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%C" arg)
             v0
       | Oval_constr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_constr@ (@,%a,@ %a@,))@]"
             pp_out_ident v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_value) arg)
             v1
       | Oval_ellipsis →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Oval_ellipsis@]"
       | Oval_float v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_float@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%F" arg)
             v0
       | Oval_int v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_int@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
             v0
       | Oval_int32 v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_int32@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%ldl" arg)
             v0
       | Oval_int64 v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_int64@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%LdL" arg)
             v0
       | Oval_nativeint v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_nativeint@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "%an" nativeint arg)
             v0
       | Oval_list v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_list@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_value) arg)
             v0
       | Oval_printer v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_printer@ %a)@]"
             (let open Ppxprint_runtime.Runtime.Fmt in const string "<fun>")
             v0
       | Oval_record v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_record@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])" pp_out_ident v0 pp_out_value
                          v1))
                  arg)
             v0
       | Oval_string v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_string@ (@,%a,@ %a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
             v1 pp_out_string v2
       | Oval_stuff v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_stuff@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0
       | Oval_tuple v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_tuple@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_value) arg)
             v0
       | Oval_variant v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Oval_variant@ (@,%a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_out_value arg ])
             v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_value : out_value → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_value arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type out_type =
  Outcometree.out_type ==
    [ Otyp_abstract
    | Otyp_open
    | Otyp_alias of out_type and string
    | Otyp_arrow of string and out_type and out_type
    | Otyp_class of bool and out_ident and list out_type
    | Otyp_constr of out_ident and list out_type
    | Otyp_manifest of out_type and out_type
    | Otyp_object of list (string * out_type) and option bool
    | Otyp_record of list (string * bool * out_type)
    | Otyp_stuff of string
    | Otyp_sum of list (string * list out_type * option out_type)
    | Otyp_tuple of list out_type
    | Otyp_var of bool and string
    | Otyp_variant of bool and out_variant and bool and option (list string)
    | Otyp_poly of list string and out_type
    | Otyp_module of out_ident and list string and list out_type
    | Otyp_attribute of out_type and out_attribute ]
and out_variant =
  Outcometree.out_variant ==
    [ Ovar_fields of list (string * bool * list out_type)
    | Ovar_typ of out_type ][@@"deriving_inline" show;]
;
value rec pp_out_type : Fmt.t out_type =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Otyp_abstract →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Otyp_abstract@]"
       | Otyp_open →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Otyp_open@]"
       | Otyp_alias v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_alias@ (@,%a,@ %a@,))@]"
             pp_out_type v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
       | Otyp_arrow v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_arrow@ (@,%a,@ %a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0 pp_out_type v1 pp_out_type v2
       | Otyp_class v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_class@ (@,%a,@ %a,@ %a@,))@]"
             Fmt.bool v0 pp_out_ident v1
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_type) arg)
             v2
       | Otyp_constr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_constr@ (@,%a,@ %a@,))@]"
             pp_out_ident v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_type) arg)
             v1
       | Otyp_manifest v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_manifest@ (@,%a,@ %a@,))@]"
             pp_out_type v0 pp_out_type v1
       | Otyp_object v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_object@ (@,%a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])"
                          (fun ofmt arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "%S" arg)
                          v0 pp_out_type v1))
                  arg)
             v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" Fmt.bool arg ])
             v1
       | Otyp_record v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_record@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1, v2) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a,@ %a@])"
                          (fun ofmt arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "%S" arg)
                          v0 Fmt.bool v1 pp_out_type v2))
                  arg)
             v0
       | Otyp_stuff v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_stuff@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0
       | Otyp_sum v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_sum@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1, v2) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a,@ %a@])"
                          (fun ofmt arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "%S" arg)
                          v0
                          (fun (ofmt : Format.formatter) arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "@[<2>[%a@,]@]"
                               (list ~{sep = semi} pp_out_type) arg)
                          v1
                          (fun ofmt →
                             fun
                             [ None →
                                 let open Ppxprint_runtime.Runtime.Fmt in
                                 const string "None" ofmt ()
                             | Some arg →
                                 let open Ppxprint_runtime.Runtime.Fmt in
                                 pf ofmt "(Some %a)" pp_out_type arg ])
                          v2))
                  arg)
             v0
       | Otyp_tuple v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_tuple@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_type) arg)
             v0
       | Otyp_var v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_var@ (@,%a,@ %a@,))@]" Fmt.bool v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
       | Otyp_variant v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "(@[<2>Outcometree.Otyp_variant@ (@,%a,@ %a,@ %a,@ %a@,))@]"
             Fmt.bool v0 pp_out_variant v1 Fmt.bool v2
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (fun (ofmt : Format.formatter) arg →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "@[<2>[%a@,]@]"
                           (list ~{sep = semi}
                              (fun ofmt arg →
                                 let open Ppxprint_runtime.Runtime.Fmt in
                                 pf ofmt "%S" arg))
                           arg)
                      arg ])
             v3
       | Otyp_poly v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_poly@ (@,%a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun ofmt arg →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "%S" arg))
                  arg)
             v0 pp_out_type v1
       | Otyp_module v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_module@ (@,%a,@ %a,@ %a@,))@]"
             pp_out_ident v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun ofmt arg →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "%S" arg))
                  arg)
             v1
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_type) arg)
             v2
       | Otyp_attribute v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Otyp_attribute@ (@,%a,@ %a@,))@]"
             pp_out_type v0 pp_out_attribute v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_type : out_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_variant : Fmt.t out_variant =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Ovar_fields v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Ovar_fields@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1, v2) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a,@ %a@])"
                          (fun ofmt arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "%S" arg)
                          v0 Fmt.bool v1
                          (fun (ofmt : Format.formatter) arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "@[<2>[%a@,]@]"
                               (list ~{sep = semi} pp_out_type) arg)
                          v2))
                  arg)
             v0
       | Ovar_typ v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Ovar_typ@ %a)@]" pp_out_type v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_variant : out_variant → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_variant arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type out_class_type =
  Outcometree.out_class_type ==
    [ Octy_constr of out_ident and list out_type
    | Octy_arrow of string and out_type and out_class_type
    | Octy_signature of option out_type and list out_class_sig_item ]
and out_class_sig_item =
  Outcometree.out_class_sig_item ==
    [ Ocsg_constraint of out_type and out_type
    | Ocsg_method of string and bool and bool and out_type
    | Ocsg_value of string and bool and bool and out_type ][@@"deriving_inline" show;]
;
value rec pp_out_class_type : Fmt.t out_class_type =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Octy_constr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Octy_constr@ (@,%a,@ %a@,))@]"
             pp_out_ident v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_type) arg)
             v1
       | Octy_arrow v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Octy_arrow@ (@,%a,@ %a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0 pp_out_type v1 pp_out_class_type v2
       | Octy_signature v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Octy_signature@ (@,%a,@ %a@,))@]"
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_out_type arg ])
             v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_out_class_sig_item) arg)
             v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_class_type : out_class_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_class_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_class_sig_item : Fmt.t out_class_sig_item =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Ocsg_constraint v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Ocsg_constraint@ (@,%a,@ %a@,))@]"
             pp_out_type v0 pp_out_type v1
       | Ocsg_method v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Ocsg_method@ (@,%a,@ %a,@ %a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0 Fmt.bool v1 Fmt.bool v2 pp_out_type v3
       | Ocsg_value v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Ocsg_value@ (@,%a,@ %a,@ %a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0 Fmt.bool v1 Fmt.bool v2 pp_out_type v3 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_class_sig_item : out_class_sig_item → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_class_sig_item arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type out_module_type =
  Outcometree.out_module_type ==
    [ Omty_abstract
    | Omty_functor of
        option (option string * out_module_type) and out_module_type
    | Omty_ident of out_ident
    | Omty_signature of list out_sig_item
    | Omty_alias of out_ident ]
and out_sig_item =
  Outcometree.out_sig_item ==
    [ Osig_class of
        bool and string and list (string * (bool * bool)) and
          out_class_type and out_rec_status
    | Osig_class_type of
        bool and string and list (string * (bool * bool)) and
          out_class_type and out_rec_status
    | Osig_typext of out_extension_constructor and out_ext_status
    | Osig_modtype of string and out_module_type
    | Osig_module of string and out_module_type and out_rec_status
    | Osig_type of out_type_decl and out_rec_status
    | Osig_value of out_val_decl
    | Osig_ellipsis ]
and out_type_decl =
  Outcometree.out_type_decl ==
    { otype_name : string;
      otype_params : list (string * (bool * bool));
      otype_type : out_type;
      otype_private : Asttypes.private_flag;
      otype_immediate : Type_immediacy.t;
      otype_unboxed : bool;
      otype_cstrs : list (out_type * out_type) }
and out_extension_constructor =
  Outcometree.out_extension_constructor ==
    { oext_name : string;
      oext_type_name : string;
      oext_type_params : list string;
      oext_args : list out_type;
      oext_ret_type : option out_type;
      oext_private : Asttypes.private_flag }
and out_type_extension =
  Outcometree.out_type_extension ==
    { otyext_name : string;
      otyext_params : list string;
      otyext_constructors : list (string * list out_type * option out_type);
      otyext_private : Asttypes.private_flag }
and out_val_decl =
  Outcometree.out_val_decl ==
    { oval_name : string;
      oval_type : out_type;
      oval_prims : list string;
      oval_attributes : list out_attribute }
and out_rec_status =
  Outcometree.out_rec_status == [ Orec_not | Orec_first | Orec_next ]
and out_ext_status =
  Outcometree.out_ext_status == [ Oext_first | Oext_next | Oext_exception ][@@"deriving_inline" show;]
;
value rec pp_out_module_type : Fmt.t out_module_type =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Omty_abstract →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Omty_abstract@]"
       | Omty_functor v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Omty_functor@ (@,%a,@ %a@,))@]"
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (fun (ofmt : Format.formatter) (v0, v1) →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "(@[%a,@ %a@])"
                           (fun ofmt →
                              fun
                              [ None →
                                  let open Ppxprint_runtime.Runtime.Fmt in
                                  const string "None" ofmt ()
                              | Some arg →
                                  let open Ppxprint_runtime.Runtime.Fmt in
                                  pf ofmt "(Some %a)"
                                    (fun ofmt arg →
                                       let open Ppxprint_runtime.Runtime.Fmt
                                       in
                                       pf ofmt "%S" arg)
                                    arg ])
                           v0 pp_out_module_type v1)
                      arg ])
             v0 pp_out_module_type v1
       | Omty_ident v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Omty_ident@ %a)@]" pp_out_ident v0
       | Omty_signature v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Omty_signature@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_sig_item)
                  arg)
             v0
       | Omty_alias v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Omty_alias@ %a)@]" pp_out_ident v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_module_type : out_module_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_module_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_sig_item : Fmt.t out_sig_item =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Osig_class v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "(@[<2>Outcometree.Osig_class@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]"
             Fmt.bool v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])"
                          (fun ofmt arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "%S" arg)
                          v0
                          (fun (ofmt : Format.formatter) (v0, v1) →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "(@[%a,@ %a@])" Fmt.bool v0 Fmt.bool v1)
                          v1))
                  arg)
             v2 pp_out_class_type v3 pp_out_rec_status v4
       | Osig_class_type v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "(@[<2>Outcometree.Osig_class_type@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]"
             Fmt.bool v0
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v1
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])"
                          (fun ofmt arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "%S" arg)
                          v0
                          (fun (ofmt : Format.formatter) (v0, v1) →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "(@[%a,@ %a@])" Fmt.bool v0 Fmt.bool v1)
                          v1))
                  arg)
             v2 pp_out_class_type v3 pp_out_rec_status v4
       | Osig_typext v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Osig_typext@ (@,%a,@ %a@,))@]"
             pp_out_extension_constructor v0 pp_out_ext_status v1
       | Osig_modtype v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Osig_modtype@ (@,%a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0 pp_out_module_type v1
       | Osig_module v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Osig_module@ (@,%a,@ %a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0 pp_out_module_type v1 pp_out_rec_status v2
       | Osig_type v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Osig_type@ (@,%a,@ %a@,))@]"
             pp_out_type_decl v0 pp_out_rec_status v1
       | Osig_value v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Osig_value@ %a)@]" pp_out_val_decl v0
       | Osig_ellipsis →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Osig_ellipsis@]" ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_sig_item : out_sig_item → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_sig_item arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_type_decl : Fmt.t out_type_decl =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({otype_name = v_otype_name; otype_params = v_otype_params;
           otype_type = v_otype_type; otype_private = v_otype_private;
           otype_immediate = v_otype_immediate;
           otype_unboxed = v_otype_unboxed; otype_cstrs = v_otype_cstrs} :
          out_type_decl) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Outcometree.otype_name =@ %a@];@ @[otype_params =@ %a@];@ @[otype_type =@ %a@];@ @[otype_private =@ %a@];@ @[otype_immediate =@ %a@];@ @[otype_unboxed =@ %a@];@ @[otype_cstrs =@ %a@] }@]"
         (fun ofmt arg →
            let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
         v_otype_name
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun (ofmt : Format.formatter) (v0, v1) →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(@[%a,@ %a@])"
                      (fun ofmt arg →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "%S" arg)
                      v0
                      (fun (ofmt : Format.formatter) (v0, v1) →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "(@[%a,@ %a@])" Fmt.bool v0 Fmt.bool v1)
                      v1))
              arg)
         v_otype_params pp_out_type v_otype_type Asttypes.pp_private_flag
         v_otype_private Type_immediacy.pp v_otype_immediate Fmt.bool
         v_otype_unboxed
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun (ofmt : Format.formatter) (v0, v1) →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(@[%a,@ %a@])" pp_out_type v0 pp_out_type v1))
              arg)
         v_otype_cstrs)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_type_decl : out_type_decl → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_type_decl arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_extension_constructor : Fmt.t out_extension_constructor =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({oext_name = v_oext_name; oext_type_name = v_oext_type_name;
           oext_type_params = v_oext_type_params; oext_args = v_oext_args;
           oext_ret_type = v_oext_ret_type; oext_private = v_oext_private} :
          out_extension_constructor) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Outcometree.oext_name =@ %a@];@ @[oext_type_name =@ %a@];@ @[oext_type_params =@ %a@];@ @[oext_args =@ %a@];@ @[oext_ret_type =@ %a@];@ @[oext_private =@ %a@] }@]"
         (fun ofmt arg →
            let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
         v_oext_name
         (fun ofmt arg →
            let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
         v_oext_type_name
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "%S" arg))
              arg)
         v_oext_type_params
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_type) arg)
         v_oext_args
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" pp_out_type arg ])
         v_oext_ret_type Asttypes.pp_private_flag v_oext_private)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_extension_constructor : out_extension_constructor → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_extension_constructor arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_type_extension : Fmt.t out_type_extension =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({otyext_name = v_otyext_name; otyext_params = v_otyext_params;
           otyext_constructors = v_otyext_constructors;
           otyext_private = v_otyext_private} :
          out_type_extension) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Outcometree.otyext_name =@ %a@];@ @[otyext_params =@ %a@];@ @[otyext_constructors =@ %a@];@ @[otyext_private =@ %a@] }@]"
         (fun ofmt arg →
            let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
         v_otyext_name
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "%S" arg))
              arg)
         v_otyext_params
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun (ofmt : Format.formatter) (v0, v1, v2) →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(@[%a,@ %a,@ %a@])"
                      (fun ofmt arg →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "%S" arg)
                      v0
                      (fun (ofmt : Format.formatter) arg →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "@[<2>[%a@,]@]"
                           (list ~{sep = semi} pp_out_type) arg)
                      v1
                      (fun ofmt →
                         fun
                         [ None →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             const string "None" ofmt ()
                         | Some arg →
                             let open Ppxprint_runtime.Runtime.Fmt in
                             pf ofmt "(Some %a)" pp_out_type arg ])
                      v2))
              arg)
         v_otyext_constructors Asttypes.pp_private_flag v_otyext_private)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_type_extension : out_type_extension → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_type_extension arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_val_decl : Fmt.t out_val_decl =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({oval_name = v_oval_name; oval_type = v_oval_type;
           oval_prims = v_oval_prims; oval_attributes = v_oval_attributes} :
          out_val_decl) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Outcometree.oval_name =@ %a@];@ @[oval_type =@ %a@];@ @[oval_prims =@ %a@];@ @[oval_attributes =@ %a@] }@]"
         (fun ofmt arg →
            let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
         v_oval_name pp_out_type v_oval_type
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "%S" arg))
              arg)
         v_oval_prims
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_out_attribute) arg)
         v_oval_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_val_decl : out_val_decl → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_val_decl arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_rec_status : Fmt.t out_rec_status =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Orec_not →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Orec_not@]"
       | Orec_first →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Orec_first@]"
       | Orec_next →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Orec_next@]" ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_rec_status : out_rec_status → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_rec_status arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_out_ext_status : Fmt.t out_ext_status =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Oext_first →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Oext_first@]"
       | Oext_next →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Oext_next@]"
       | Oext_exception →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Outcometree.Oext_exception@]" ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_ext_status : out_ext_status → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_ext_status arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type out_phrase =
  Outcometree.out_phrase ==
    [ Ophr_eval of out_value and out_type
    | Ophr_signature of list (out_sig_item * option out_value)
    | Ophr_exception of (Exceptions.t * out_value) ][@@"deriving_inline" show;]
;
value rec pp_out_phrase : Fmt.t out_phrase =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Ophr_eval v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Ophr_eval@ (@,%a,@ %a@,))@]"
             pp_out_value v0 pp_out_type v1
       | Ophr_signature v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Ophr_signature@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])" pp_out_sig_item v0
                          (fun ofmt →
                             fun
                             [ None →
                                 let open Ppxprint_runtime.Runtime.Fmt in
                                 const string "None" ofmt ()
                             | Some arg →
                                 let open Ppxprint_runtime.Runtime.Fmt in
                                 pf ofmt "(Some %a)" pp_out_value arg ])
                          v1))
                  arg)
             v0
       | Ophr_exception v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Outcometree.Ophr_exception@ %a)@]"
             (fun (ofmt : Format.formatter) (v0, v1) →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(@[%a,@ %a@])" Exceptions.pp v0 pp_out_value v1)
             v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_out_phrase : out_phrase → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_out_phrase arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];


