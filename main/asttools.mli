(* camlp5r *)
(* asttools.mli,v *)

open MLast;

value prefix_eq : string → string → bool;
type choice α β =
  [ Left of α
  | Right of β ]
;
value isLeft : choice α β → bool;
value isRight : choice α β → bool;
value outLeft : choice α β → α ;
value outRight : choice α β → β ;
value option_map : (α → β) → option α → option β;
value mustSome : string → option α → α;
value mustLeft : string → choice α β → α;
value mustRight : string → choice α β → β;
value stream_npeek :
  int → Stream.t (string * string) → list (string * string);
value longid_concat : longid → longid → longid;
value longid_last : longid → longid;
value module_type_unwrap_attrs :
  module_type → (module_type * list attribute);
value module_expr_unwrap_attrs :
  module_expr → (module_expr * list attribute);
value sep_last : list α → (α * list α);
value try_find : (α → β) → list α → β;
value expr_to_path_module_expr : expr → option module_expr;
value expr_last_is_uid : expr → bool;
value expr_first_is_id : expr → bool;
value expr_is_module_path : expr → bool;
value check_stream :
  ?avoid_tokens:list (string * string) →
    list
      (int *
       choice (list (string * string) → option α)
         (list (string * string) → bool)) →
    Stream.t (string * string) → (int * α);
type fsm 'a = { start : 'a ; accept : 'a ; fail : 'a ; delta : list ('a * (string * string) -> 'a) } ;
value check_fsm : fsm 'a -> Stream.t (string * string) -> bool ;
value type_binder_fsm : fsm string ;
value expr_wrap_attrs :
  loc → expr → list attribute → expr;
value expr_to_inline :
  expr → option (loc * string) → list attribute → expr;
value ctyp_wrap_attrs : ctyp → list attribute → ctyp;
value ctyp_to_inline :
  ctyp → option (loc * string) → list attribute → ctyp;
value patt_wrap_attrs : patt → list attribute → patt;
value patt_to_inline :
  patt → option (loc * string) → list attribute → patt;
value class_expr_wrap_attrs :
  class_expr → list attribute → class_expr;
value class_type_wrap_attrs :
  class_type → list attribute → class_type;
value module_type_wrap_attrs :
  module_type → list attribute → module_type;
value module_expr_wrap_attrs :
  module_expr → list attribute → module_expr;
value str_item_to_inline :
  str_item → option (loc * string) → str_item;
value sig_item_to_inline :
  sig_item → option (loc * string) → sig_item;
value longident_of_string_list : loc → list string → longid;
value string_list_of_longident : longid → list string;
value longident_lident_of_string_list : loc → list string → longid_lident;
value string_list_of_longident_lident : longid_lident → list string;
value expr_of_string_list : loc -> list string -> expr ;
value expr_concat : expr -> expr -> expr ;
