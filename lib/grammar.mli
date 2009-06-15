(* camlp5r *)
(* $Id: grammar.mli,v 1.30 2007/12/27 19:50:50 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2008 *)

(** Extensible grammars.

    This module implements the Camlp5 extensible grammars system.
    Grammars entries can be extended using the [EXTEND] statement,
    added by loading the Camlp5 [pa_extend.cmo] file. *)

type g = 'x;
   (** The type for grammars, holding entries. *)
type token = (string * string);

value gcreate : Plexing.lexer token -> g;
   (** Create a new grammar, without keywords, using the lexer given
       as parameter. *)
value tokens : g -> string -> list (string * int);
   (** Given a grammar and a token pattern constructor, returns the list of
       the corresponding values currently used in all entries of this grammar.
       The integer is the number of times this pattern value is used.

       Examples:
-      The call [Grammar.tokens g ""] returns the keywords list.
-      The call [Grammar.tokens g "IDENT"] returns the list of all usages
       of the pattern "IDENT" in the [EXTEND] statements. *)
value glexer : g -> Plexing.lexer token;
   (** Return the lexer used by the grammar *)

type parsable = 'abstract;
value parsable : g -> Stream.t char -> parsable;
   (** Type and value allowing to keep the same token stream between
       several calls of entries of the same grammar, to prevent possible
       loss of tokens. To be used with [Entry.parse_parsable] below *)

module Entry :
  sig
    type e 'a = 'x;
    value create : g -> string -> e 'a;
    value parse : e 'a -> Stream.t char -> 'a;
    value parse_all : e 'a -> Stream.t char -> list 'a;
    value parse_token : e 'a -> Stream.t token -> 'a;
    value parse_parsable : e 'a -> parsable -> 'a;
    value name : e 'a -> string;
    value of_parser : g -> string -> (Stream.t token -> 'a) -> e 'a;
    value print : e 'a -> unit;
    value find : e 'a -> string -> e Obj.t;
    external obj : e 'a -> Gramext.g_entry token = "%identity";
  end
;
   (** Module to handle entries.
-      [Entry.e] is the type for entries returning values of type ['a].
-      [Entry.create g n] creates a new entry named [n] in the grammar [g].
-      [Entry.parse e] returns the stream parser of the entry [e].
-      [Entry.parse_all e] returns the stream parser returning all possible
          values while parsing with the entry [e]: may return more than one
          value when the parsing algorithm is [Backtracking]
-      [Entry.parse_all e] returns the parser returning all possible values.
-      [Entry.parse_token e] returns the token parser of the entry [e].
-      [Entry.parse_parsable e] returns the parsable parser of the entry [e].
-      [Entry.name e] returns the name of the entry [e].
-      [Entry.of_parser g n p] makes an entry from a token stream parser.
-      [Entry.print e] displays the entry [e] using [Format].
-      [Entry.find e s] finds the entry named [s] in the rules of [e].
-      [Entry.obj e] converts an entry into a [Gramext.g_entry] allowing
          to see what it holds. *)

value of_entry : Entry.e 'a -> g;
   (** Return the grammar associated with an entry. *)

(** {6 Clearing grammars and entries} *)

module Unsafe :
  sig
    value gram_reinit : g -> Plexing.lexer token -> unit;
    value clear_entry : Entry.e 'a -> unit;
  end
;
   (** Module for clearing grammars and entries. To be manipulated with
       care, because: 1) reinitializing a grammar destroys all tokens
       and there may have problems with the associated lexer if there
       are keywords; 2) clearing an entry does not destroy the tokens
       used only by itself.
-      [Unsafe.reinit_gram g lex] removes the tokens of the grammar
-      and sets [lex] as a new lexer for [g]. Warning: the lexer
-      itself is not reinitialized.
-      [Unsafe.clear_entry e] removes all rules of the entry [e]. *)

(** {6 Parsing algorithm} *)

type parse_algorithm = Gramext.parse_algorithm ==
  [ Predictive | Backtracking | DefaultAlgorithm ]
;
   (** Type of algorithm used in grammar entries.
         [Predictive]: use imperative streams with predictive parsing
         [Backtracking]: use functional streams with full backtracking
         [DefaultAlgorithm]: found in the variable [backtrack_parse] below.
       The default, when a grammar is created, is [DefaultAlgorithm]. *)

value set_algorithm : g -> parse_algorithm -> unit;
   (** Set the parsing algorithm for all entries of a given grammar. *)

value backtrack_parse : ref bool;
   (** If [True], the default parsing uses full backtracking. If [False],
       it uses parsing with normal streams. If the environment variable
       CAMLP5PARAM contains "b", the default is [True]; otherwise, the
       default is [False]. *)

value backtrack_stalling_limit : ref int;
   (** Limitation of backtracking to prevent stalling in case of syntax
       error. In backtracking algorithm, when there is a syntax error,
       the parsing continues trying to find another solution. It some
       grammars, it can be very long before checking all possibilities.
       This number limits the number of tokens tests after a backtrack.
       (The number of tokens tests is reset to zero when the token
       stream overtakes the last reached token.) The default is 10000.
       If set to 0, there is no limit. Can be set by the environment
       variable CAMLP5PARAM by "l=value". *)

(** {6 Functorial interface} *)

   (** Alternative for grammars use. Grammars are no more Ocaml values:
       there is no type for them. Modules generated preserve the
       rule "an entry cannot call an entry of another grammar" by
       normal OCaml typing. *)

module type GLexerType =
  sig
    type te = 'x;
    value lexer : Plexing.lexer te;
  end
;
   (** The input signature for the functor [Grammar.GMake]: [te] is the
       type of the tokens. *)

module type S =
  sig
    type te = 'x;
    type parsable = 'x;
    value parsable : Stream.t char -> parsable;
    value tokens : string -> list (string * int);
    value glexer : Plexing.lexer te;
    value set_algorithm : parse_algorithm -> unit;
    module Entry :
      sig
        type e 'a = 'y;
        value create : string -> e 'a;
        value parse : e 'a -> parsable -> 'a;
        value parse_token : e 'a -> Stream.t te -> 'a;
        value name : e 'a -> string;
        value of_parser : string -> (Stream.t te -> 'a) -> e 'a;
        value print : e 'a -> unit;
        external obj : e 'a -> Gramext.g_entry te = "%identity";
      end
    ;
    module Unsafe :
      sig
        value gram_reinit : Plexing.lexer te -> unit;
        value clear_entry : Entry.e 'a -> unit;
      end
    ;
    value extend :
      Entry.e 'a -> option Gramext.position ->
        list
          (option string * option Gramext.g_assoc *
           list (list (Gramext.g_symbol te) * Gramext.g_action)) ->
        unit;
    value delete_rule : Entry.e 'a -> list (Gramext.g_symbol te) -> unit;
  end
;
   (** Signature type of the functor [Grammar.GMake]. The types and
       functions are almost the same than in generic interface, but:
-      Grammars are not values. Functions holding a grammar as parameter
         do not have this parameter yet.
-      The type [parsable] is used in function [parse] instead of
         the char stream, avoiding the possible loss of tokens.
-      The type of tokens (expressions and patterns) can be any
         type (instead of (string * string)); the module parameter
         must specify a way to show them as (string * string) *)

module GMake (L : GLexerType) : S with type te = L.te;

(** {6 Miscellaneous} *)

value skip_item : 'a -> 'a;
   (** [Grammar.skip_item x] can be called in a semantic action of
       a grammar rule to ask the grammar to skip that item if it
       is called in a list (LIST0 or LIST1). The function returns
       the item itself (for typing reasons) but its value is ignored.
       This function is used to allow IFDEF and IFNDEF for cases of
       constructor declarations and pattern matchings. *)

value error_verbose : ref bool;
   (** Flag for displaying more information in case of parsing error;
       default = [False] *)

value warning_verbose : ref bool;
   (** Flag for displaying warnings while extension; default = [True] *)

value strict_parsing : ref bool;
   (** Flag to apply strict parsing, without trying to recover errors;
       default = [False] *)

value print_entry : Format.formatter -> Gramext.g_entry 'te -> unit;
   (** General printer for all kinds of entries (obj entries) *)

value iter_entry :
  (Gramext.g_entry 'te -> unit) -> Gramext.g_entry 'te -> unit;
  (** [Grammar.iter_entry f e] applies [f] to the entry [e] and
      transitively all entries called by [e]. The order in which
      the entries are passed to [f] is the order they appear in
      each entry. Each entry is passed only once. *)

value fold_entry :
  (Gramext.g_entry 'te -> 'a -> 'a) -> Gramext.g_entry 'te -> 'a -> 'a;
  (** [Grammar.fold_entry f e init] computes [(f eN .. (f e2 (f e1 init)))],
      where [e1 .. eN] are [e] and transitively all entries called by [e].
      The order in which the entries are passed to [f] is the order they
      appear in each entry. Each entry is passed only once. *)

value reinit_entry_functions : Gramext.g_entry 'te -> unit;

(*** For system use *)

value loc_of_token_interval : int -> int -> Ploc.t;
value extend :
  list
    (Gramext.g_entry 'te * option Gramext.position *
     list
       (option string * option Gramext.g_assoc *
        list (list (Gramext.g_symbol 'te) * Gramext.g_action))) ->
    unit;
value delete_rule : Entry.e 'a -> list (Gramext.g_symbol token) -> unit;

value parse_top_symb :
  Gramext.g_entry 'te -> Gramext.g_symbol 'te -> Stream.t 'te -> Obj.t;
value symb_failed_txt :
  Gramext.g_entry 'te -> Gramext.g_symbol 'te -> Gramext.g_symbol 'te ->
    string;
value create_local_entry : g -> string -> Entry.e 'a;
