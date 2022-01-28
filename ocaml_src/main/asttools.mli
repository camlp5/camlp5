(* camlp5r *)
(* asttools.mli,v *)

open MLast;;

val prefix_eq : string -> string -> bool;;
type ('a, 'b) choice =
    Left of 'a
  | Right of 'b
;;
val isLeft : ('a, 'b) choice -> bool;;
val isRight : ('a, 'b) choice -> bool;;
val outLeft : ('a, 'b) choice -> 'a;;
val outRight : ('a, 'b) choice -> 'b;;
val option_map : ('a -> 'b) -> 'a option -> 'b option;;
val mustSome : string -> 'a option -> 'a;;
val mustLeft : string -> ('a, 'b) choice -> 'a;;
val mustRight : string -> ('a, 'b) choice -> 'b;;
val stream_npeek :
  int -> (string * string) Stream.t -> (string * string) list;;
val longid_concat : longid -> longid -> longid;;
val longid_last : longid -> longid;;
val module_type_unwrap_attrs : module_type -> module_type * attribute list;;
val module_expr_unwrap_attrs : module_expr -> module_expr * attribute list;;
val sep_last : 'a list -> 'a * 'a list;;
val try_find : ('a -> 'b) -> 'a list -> 'b;;
val expr_to_path_module_expr : expr -> module_expr option;;
val expr_last_is_uid : expr -> bool;;
val expr_first_is_id : expr -> bool;;
val expr_is_module_path : expr -> bool;;
val check_stream :
  ?avoid_tokens:(string * string) list ->
    (int *
       ((string * string) list -> 'a option, (string * string) list -> bool)
         choice)
      list ->
    (string * string) Stream.t -> int * 'a;;
type 'a fsm =
  { start : 'a;
    accept : 'a;
    fail : 'a;
    delta : ('a * (string * string -> 'a)) list }
;;
val check_fsm : 'a fsm -> (string * string) Stream.t -> bool;;
val type_binder_fsm : string fsm;;
val expr_wrap_attrs : loc -> expr -> attribute list -> expr;;
val expr_to_inline : expr -> (loc * string) option -> attribute list -> expr;;
val ctyp_wrap_attrs : ctyp -> attribute list -> ctyp;;
val ctyp_to_inline : ctyp -> (loc * string) option -> attribute list -> ctyp;;
val patt_wrap_attrs : patt -> attribute list -> patt;;
val patt_to_inline : patt -> (loc * string) option -> attribute list -> patt;;
val class_expr_wrap_attrs : class_expr -> attribute list -> class_expr;;
val class_type_wrap_attrs : class_type -> attribute list -> class_type;;
val module_type_wrap_attrs : module_type -> attribute list -> module_type;;
val module_expr_wrap_attrs : module_expr -> attribute list -> module_expr;;
val str_item_to_inline : str_item -> (loc * string) option -> str_item;;
val sig_item_to_inline : sig_item -> (loc * string) option -> sig_item;;
val longident_of_string_list : loc -> string list -> longid;;
val string_list_of_longident : longid -> string list;;
val longident_lident_of_string_list : loc -> string list -> longid_lident;;
val string_list_of_longident_lident : longid_lident -> string list;;
val expr_of_string_list : loc -> string list -> expr;;
val expr_concat : expr -> expr -> expr;;
