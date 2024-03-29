(* camlp5r *)
(* plexer.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** This module contains the lexer used for ocaml syntax (revised and
    normal). *)

val gmake : unit -> (string * string) Plexing.lexer;;
   (** [gmake ()] returns a lexer compatible with the extensible
    grammars. The returned tokens follow the normal syntax and the
    revised syntax lexing rules.

    The token type is "<tt>(string * string)</tt>" just like the pattern
    type.

       The meaning of the tokens are:
-      * [("", s)] is the keyword [s].
-      * [("", s)] is the keyword [s],
-      * [("LIDENT", s)] is the ident [s] starting with a lowercase letter,
-      * [("UIDENT", s)] is the ident [s] starting with an uppercase letter,
-      * [("INT", s)] is an integer constant whose string source is [s],
-      * [("INT_l", s)] is an 32 bits integer constant,
-      * [("INT_L", s)] is an 64 bits integer constant,
-      * [("INT_n", s)] is an native integer constant,
-      * [("FLOAT", s)] is a float constant whose string source is [s],
-      * [("STRING", s)] is the string constant [s],
-      * [("CHAR", s)] is the character constant [s],
-      * [("TILDEIDENT", s)] is the tilde character [~] followed by the
         ident [s],
-      * [("TILDEIDENTCOLON", s)] is the tilde character [~] followed by the
         ident [s] and a colon [:],
-      * [("QUESTIONIDENT", s)] is the question mark [?] followed by the
         ident [s],
-      * [("QUESTIONIDENTCOLON", s)] is the question mark [?] followed by the
         ident [s] and a colon [:],
-      * [("QUOTATION", "t:s")] is a quotation [t] holding the string [s],
-      * [("ANTIQUOT", "t:s")] is an antiquotation [t] holding the string [s],
-      * [("EOI", "")] is the end of input.

       The associated token patterns in the EXTEND statement hold the
       same names than the first string (constructor name) of the tokens
       expressions above.

       Warning: the string associated with the [STRING] constructor is
       the string found in the source without any interpretation. In
       particular, the backslashes are not interpreted. For example, if
       the input is ["\n"] the string is *not* a string with one
       element containing the "newline" character, but a string of two
       elements: the backslash and the ["n"] letter.

       Same thing for the string associated with the [CHAR] constructor.

       The functions [Plexing.eval_string] and [Plexing.eval_char] allow
       to convert them into the real corresponding string or char
       value. *)

val simplest_raw_strings : bool ref;;
   (** When False (default), the next call to [Plexer.gmake ()] returns a
       lexer where {|...|} is not a valid raw-string.  Setting it to True
       will allow such strings to be valid raw-strings, while checking for
       and throwing an error if "{|" and "|}" are specified  as keywords. *)

val dollar_for_antiquotation : bool ref;;
   (** When True (default), the next call to [Plexer.gmake ()] returns a
       lexer where the dollar sign is used for antiquotations. If False,
       the dollar sign can be used as token. *)

val specific_space_dot : bool ref;;
   (** When [False] (default), the next call to [Plexer.gmake ()] returns a
       lexer where there is no difference between dots which have spaces
       before and dots which don't have spaces before. If [True], dots
       which have spaces before return the keyword " ." (space dot) and
       the ones which don't have spaces before return the keyword "."
       (dot alone). *)

val no_quotations : bool ref;;
   (** When True, all lexers built by [Plexer.gmake ()] do not lex the
       quotation syntax. Default is False (quotations are lexed). *)

val utf8_lexing : bool ref;;
   (** When True, all lexers built by [Plexer.gmake ()] use utf-8 encoding
       to specify letters and punctuation marks. Default is False (all
       characters between '\128' and '\255' are considered as letters) *)

val parse_antiloc : string -> (Ploc.t * string * string) option;;
   (** breaks apart the payload of an ANTIQUOT_LOC
       (which is <begin-pos>,<end-pos>:<type>:<token-string>)
       into its colon-separated parts *)

val parse_antiquot : string -> (string * string) option;;
   (** breaks apart the payload of an ANTIQUOT
       (which is <type>:<token-string>)
       into its colon-separated parts *)

(*** For system use *)

val force_antiquot_loc : bool ref;;
