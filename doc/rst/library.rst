Library
=======

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Library
      :name: library
      :class: top

   All modules defined in "gramlib.cma", but *not* including all Camlp5
   modules used by the Camlp5 commands and kits.

   .. container::
      :name: tableofcontents

   .. rubric:: Ploc module
      :name: ploc-module

   Building and combining locations. This module also contains some
   pervasive types and functions.

   ``type t = 'abstract;``
      Location type.

   .. rubric:: located exceptions
      :name: located-exceptions

   ``exception Exc of location and exn;``
      "``Ploc.Exc loc e``" is an encapsulation of the exception "``e``"
      with the input location "``loc``". To be used to specify a
      location for an error. This exception must not be raised by the
      OCaml function "``raise``", but rather by "``Ploc.raise``" (see
      below), to prevent the risk of several encapsulations of
      "``Ploc.Exc``".
   ``value raise : t -> exn -> 'a;``
      "``Ploc.raise loc e``", if "``e``" is already the exception
      "``Ploc.Exc``", re-raise it (ignoring the new location "``loc``"),
      else raise the exception "``Ploc.Exc loc e``".

   .. rubric:: making locations
      :name: making-locations

   ``value make_loc : string -> int -> int -> (int * int) -> string -> t;``
      "``Ploc.make_loc fname line_nb bol_pos (bp, ep) comm``" creates a
      location starting at line number "``line_nb``", where the position
      of the beginning of the line is "``bol_pos``" and between the
      positions "``bp``" (included) and "``ep``" excluded. And
      "``comm``" is the comment before the location. The positions are
      in number of characters since the begin of the stream.
   ``value make_unlined : (int * int) -> t;``
      "``Ploc.make_unlined``" is like "``Ploc.make``" except that the
      line number is not provided (to be used e.g. when the line number
      is unknown).

   ``value dummy : t;``
      "``Ploc.dummy``" is a dummy location, used in situations when
      location has no meaning.

   .. rubric:: getting location info
      :name: getting-location-info

   ``value file_name : t -> string;``
      "``Ploc.file_name loc``" returns the file name of the location.
   ``value first_pos : t -> int;``
      "``Ploc.first_pos loc``" returns the initial position of the
      location in number of characters since the beginning of the
      stream.
   ``value last_pos : t -> int;``
      "``Ploc.last_pos loc``" returns the final position plus one of the
      location in number of characters since the beginning of the
      stream.
   ``value line_nb : t -> int;``
      "``Ploc.line_nb loc``" returns the line number of the location or
      "``-1``" if the location does not contain a line number (i.e.
      built with "``Ploc.make_unlined``" above).
   ``value bol_pos : t -> int;``
      "``Ploc.bol_pos loc``" returns the position of the beginning of
      the line of the location in number of characters since the
      beginning of the stream, or "``0``" if the location does not
      contain a line number (i.e. built the with "``Ploc.make_unlined``"
      above).
   ``value comment : t -> string;``
      "``Ploc.comment loc``" returns the comment before the location.

   .. rubric:: combining locations
      :name: combining-locations

   ``value encl : t -> t -> t;``
      "``Ploc.encl loc1 loc2``" returns the location starting at the
      smallest start and ending at the greatest end of the locations
      "``loc1``" and "``loc2``". In other words, it is the location
      enclosing "``loc1``" and "``loc2``".
   ``value shift : int -> t -> t;``
      "``Ploc.shift sh loc``" returns the location "``loc``" shifted
      with "``sh``" characters. The line number is not recomputed.
   ``value sub : t -> int -> int -> t;``
      "``Ploc.sub loc sh len``" is the location "``loc``" shifted with
      "``sh``" characters and with length "``len``". The previous ending
      position of the location is lost.
   ``value after : t -> int -> int -> t;``
      "``Ploc.after loc sh len``" is the location just after loc
      (starting at the end position of "``loc``") shifted with "``sh``"
      characters and of length "``len``".
   ``value with_comment : t -> string -> t;``
      Change the comment part of the given location

   .. rubric:: miscellaneous
      :name: miscellaneous

   ``value name : ref string;``
      "``Ploc.name.val``" is the name of the location variable used in
      grammars and in the predefined quotations for OCaml syntax trees.
      Default: "``"loc"``".

   ``value get : string -> t -> (int * int * int * int * int);``
      "``Ploc.get fname loc``" returns in order: 1/ the line number of
      the begin of the location, 2/ its column, 3/ the line number of
      the first character not in the location, 4/ its column and 5/ the
      length of the location. The parameter "``fname``" is the file
      where the location occurs.
   ``value from_file : string -> t -> (string * int * int * int);``
      "``Ploc.from_file fname loc``" reads the file "``fname``" up to
      the location "``loc``" and returns the real input file, the line
      number and the characters location in the line; the real input
      file can be different from "``fname``" because of possibility of
      line directives typically generated by /lib/cpp.

   .. rubric:: pervasives
      :name: pervasives

   ::

      type vala 'a =
        [ VaAnt of string
        | VaVal of 'a ]
      ;

   Encloser of many abstract syntax tree notes types, in "strict" mode.
   This allow the system of antiquotations of abstract syntax tree
   quotations to work when using the quotation kit "``q_ast.cmo``".

   ``value call_with : ref 'a -> 'a -> ('b -> 'c) -> 'b -> 'c;``
      "``Ploc.call_with r v f a``" sets the reference "``r``" to the
      value "``v``", then calls "``f a``", and resets "``r``" to its
      initial value. If "``f a``" raises an exception, its initial value
      is also reset and the exception is reraised. The result is the
      result of "``f     a``".

   .. rubric:: Plexing module
      :name: plexing-module

   Lexing for Camlp5 grammars.

   This module defines the Camlp5 lexer type to be used in extensible
   grammars (see module "``Grammar``"). It also provides some useful
   functions to create lexers.

   ``type pattern = (string * string);``
      Type for values used by the generated code of the EXTEND statement
      to represent terminals in entry rules.

      -  The first string is the constructor name (must start with an
         uppercase character). When empty, the second string should be a
         keyword.
      -  The second string is the constructor parameter. Empty if it has
         no parameter (corresponding to the 'wildcard' pattern).
      -  The way tokens patterns are interpreted to parse tokens is done
         by the lexer, function "``tok_match``" below.

   ``exception Error of string;``
      A lexing error exception to be used by lexers.

   .. rubric:: lexer type
      :name: lexer-type

   ::

      type lexer 'te =
        { tok_func : lexer_func 'te;
          tok_using : pattern -> unit;
          tok_removing : pattern -> unit;
          tok_match : mutable pattern -> 'te -> string;
          tok_text : pattern -> string;
          tok_comm : mutable option (list Ploc.t) }

   The type for lexers compatible with Camlp5 grammars. The parameter
   type "``'te``" is the type of the tokens.

   -  The field "``tok_func``" is the main lexer function. See
      "``lexer_func``" type below.
   -  The field "``tok_using``" is a function called by the "``EXTEND``"
      statement to warn the lexer that a rule uses this pattern (given
      as parameter). This allow the lexer 1/ to check that the pattern
      constructor is really among its possible constructors 2/ to enter
      the keywords in its tables.
   -  The field "``tok_removing``" is a function possibly called by the
      "``DELETE_RULE``" statement to warn the lexer that this pattern
      (given as parameter) is no longer used in the grammar (the grammar
      system maintains a number of usages of all patterns and calls this
      function when this number falls to zero). If it is a keyword, this
      allows the lexer to remove it in its tables.
   -  The field "``tok_match``" is a function called by the Camlp5
      grammar system to ask the lexer how the input tokens should be
      matched against the patterns. Warning: for efficiency, this
      function must be written as a function taking patterns as
      parameters and, for each pattern value, returning a function
      matching a token, *not* as a function with two parameters.
   -  The field "``tok_text``" is a function called by the grammar
      system to get the name of the tokens for the error messages, in
      case of syntax error, or for the displaying of the rules of an
      entry.
   -  The field "``tok_comm``" is a mutable place where the lexer can
      put the locations of the comments, if its initial value is not
      "``None``". If it is "``None``", nothing has to be done by the
      lexer.

   ``and lexer_func 'te = Stream.t char -> (Stream.t 'te *       location_function)``
      The type of a lexer function (field "``tok_func``" of the type
      "``lexer``"). The character stream is the input stream to be
      lexed. The result is a pair of a token stream and a location
      function (see below) for this tokens stream.

   ``and location_function = int -> Ploc.t;``
      The type of a function giving the location of a token in the
      source from the token number in the stream (starting from zero).

   ``value lexer_text : pattern -> string;``
      A simple "``tok_text``" function.

   ``value default_match : pattern -> (string * string) ->       string;``
      A simple "``tok_match``" function, appling to the token type
      "``(string * string)``".

   .. rubric:: lexers from parsers or ocamllex
      :name: lexers-from-parsers-or-ocamllex

   The functions below create lexer functions either from a
   "``char    stream``" parser or for an "``ocamllex``" function. With
   the returned function "``f``", it is possible to get a simple lexer
   (of the type "``Plexing.lexer``" above):

   ::

         {Plexing.tok_func = f;
          Plexing.tok_using = (fun _ -> ());
          Plexing.tok_removing = (fun _ -> ());
          Plexing.tok_match = Plexing.default_match;
          Plexing.tok_text = Plexing.lexer_text}

   Note that a better "``tok_using``" function would check the used
   tokens and raise "``Plexing.Error``" for incorrect ones. The other
   functions "``tok_removing``", "``tok_match``" and "``tok_text``" may
   have other implementations as well.

   ::

      value lexer_func_of_parser :
        ((Stream.t char * ref int * ref int) -> ('te * Ploc.t)) -> lexer_func 'te;

   A lexer function from a lexer written as a char stream parser
   returning the next token and its location. The two references with
   the char stream contain the current line number and the position of
   the beginning of the current line.
   ::

      value lexer_func_of_ocamllex : (Lexing.lexbuf -> 'te) -> lexer_func 'te;

   A lexer function from a lexer created by "``ocamllex``".
   .. rubric:: function to build a stream and a location function
      :name: function-to-build-a-stream-and-a-location-function

   ::

      value make_stream_and_location :
        (unit -> ('te * Ploc.t)) -> (Stream.t 'te * location_function);

   .. rubric:: useful functions and values
      :name: useful-functions-and-values

   ``value eval_char : string -> char;``
   ``value eval_string : Ploc.t -> string -> string;``
      Convert a char or a string token, where the backslashes are not
      been interpreted into a real char or string; raise "``Failure``"
      if a bad backslash sequence is found;
      "``Plexing.eval_char (Char.escaped c)``" returns "``c``" and
      "``Plexing.eval_string (String.escaped s)``" returns ``s``.

   ``value restore_lexing_info : ref (option (int * int));``
   ``value line_nb : ref (ref int);``
   ``value bol_pos : ref (ref int);``
      Special variables used to reinitialize line numbers and position
      of beginning of line with their correct current values when a
      parser is called several times with the same character stream.
      Necessary for directives (e.g. #load or #use) which interrupt the
      parsing. Without usage of these variables, locations after the
      directives can be wrong.

   .. rubric:: backward compatibilities
      :name: backward-compatibilities

   Deprecated since version 4.08.

   ``type location = Ploc.t;``
   ``value make_loc : (int * int) -> location;``
   ``value dummy_loc : location;``
   .. rubric:: Plexer module
      :name: plexer-module

   This module contains a lexer used for OCaml syntax (revised and
   normal).

   .. rubric:: lexer
      :name: lexer

   ``value gmake : unit -> Plexing.lexer (string * string);``
      "``gmake ()``" returns a lexer compatible with the extensible
      grammars. The returned tokens follow the normal syntax and the
      revised syntax lexing rules.

   The token type is "``(string * string)``" just like the pattern type.

   The meaning of the tokens are:

   -  ``("", s)`` is the keyword ``s``,
   -  ``("LIDENT", s)`` is the ident ``s`` starting with a lowercase
      letter,
   -  ``("UIDENT", s)`` is the ident ``s`` starting with an uppercase
      letter,
   -  ``("INT", s)`` is an integer constant whose string source is
      ``s``,
   -  ``("INT_l", s)`` is an 32 bits integer constant whose string
      source is ``s``,
   -  ``("INT_L", s)`` is an 64 bits integer constant whose string
      source is ``s``,
   -  ``("INT_n", s)`` is an native integer constant whose string source
      is ``s``,
   -  ``("FLOAT", s)`` is a float constant whose string source is ``s``,
   -  ``("STRING", s)`` is the string constant ``s``,
   -  ``("CHAR", s)`` is the character constant ``s``,
   -  ``("TILDEIDENT", s)`` is the tilde character "``~``" followed by
      the ident ``s``,
   -  ``("TILDEIDENTCOLON", s)`` is the tilde character "``~``" followed
      by the ident ``s`` and a colon "``:``",
   -  ``("QUESTIONIDENT", s)`` is the question mark "``?``" followed by
      the ident ``s``,
   -  ``("QUESTIONIDENTCOLON", s)`` is the question mark "``?``"
      followed by the ident ``s`` and a colon "``:``",
   -  ``("QUOTATION", "t:s")`` is a quotation "``t``" holding the string
      ``s``,
   -  ``("ANTIQUOT", "t:s")`` is an antiquotation "``t``" holding the
      string ``s``,
   -  ``("EOI", "")`` is the end of input.

   The associated token patterns in the EXTEND statement hold the same
   names as the first string (constructor name) of the tokens
   expressions above.

   Warning: the string associated with the "``STRING``" constructor is
   the string found in the source without any interpretation. In
   particular, the backslashes are not interpreted. For example, if the
   input is ``"\n"`` the string is \*not\* a string with one element
   containing the "newline" character, but a string of two elements: the
   backslash and the ``"n"`` letter.

   Same thing for the string associated with the "``CHAR``" constructor.

   The functions "``Plexing.eval_string``" and "``Plexing.eval_char``"
   allow to convert them into the real corresponding string or char
   value.

   .. rubric:: flags
      :name: flags

   ``value dollar_for_antiquotation : ref bool;``
      When True (default), the next call to "``Plexer.gmake ()``"
      returns a lexer where the dollar sign is used for antiquotations.
      If False, there is no antiquotations and the dollar sign can be
      used as normal token.

   ``value specific_space_dot : ref bool;``
      When "``False``" (default), the next call to "``Plexer.gmake ()``"
      returns a lexer where there is no difference between dots which
      have spaces before and dots which don't have spaces before. If
      "``True``", dots which have spaces before return the keyword
      ``" ."`` (space dot) and the ones which don't have spaces before
      return the keyword ``"."`` (dot alone).

   ``value no_quotations : ref bool;``
      When "``True``", all lexers built by "``Plexer.gmake       ()``"
      do not lex the quotation syntax. Default is "``False``"
      (quotations are lexed).

   ``value utf8_lexing : ref bool;``
      When "``True``", all lexers built by "``Plexer.gmake        ()]``"
      use utf-8 encoding to specify letters and punctuation marks.
      Default is False (all characters between '\128' and '\255' are
      considered as letters).

   .. rubric:: Gramext module
      :name: gramext-module

   This module is not intended to be used by the casual programmer.

   It shows, in clear, the implementations of grammars and entries
   types, the normal access being through the "``Grammar``" module where
   these types are abstract. It can be useful for programmers interested
   in scanning the contents of grammars and entries, for example to make
   analyses on them.

   .. rubric:: grammar type
      :name: grammar-type

   ::

      type grammar 'te =
        { gtokens : Hashtbl.t Plexing.pattern (ref int);
          glexer : mutable Plexing.lexer 'te }
      ;

   The visible type of grammars, i.e. the implementation of the abstract
   type "``Grammar.g``". It is also the implementation of an internal
   grammar type used in the Grammar functorial interface.
   The type parameter "``'te``" is the type of the tokens, which is
   "``(string * string)``" for grammars built with
   "``Grammar.gcreate``", and any type for grammars built with the
   functorial interface. The field "``gtokens``" records the count of
   usages of each token pattern, allowing to call the lexer function
   "``tok_removing``" (see the `Plexing module <#a:Plexing-module>`__)
   when this count reaches zero. The field "``lexer``" is the lexer.
   .. rubric:: entry type
      :name: entry-type

   ::

      type g_entry 'te =
        { egram : grammar 'te;
          ename : string;
          elocal : bool;
          estart : mutable int -> Stream.t 'te -> Obj.t;
          econtinue : mutable int -> int -> Obj.t -> Stream.t 'te -> Obj.t;
          edesc : mutable g_desc 'te }

   The visible type for grammar entries, i.e. the implementation of the
   abstract type "``Grammar.Entry.e``" and the type of entries in the
   Grammar functorial interface. Notice that these entry types have a
   type parameter which does not appear in the "``g_entry``" type (the
   "``'te``" parameter is, as for grammars above, the type of the
   tokens). This is due to the specific typing system of the EXTEND
   statement which sometimes must hide real types, the OCaml normal type
   system not being able to type Camlp5 grammars.
   Meaning of the fields:

   -  ``egram`` : the associated grammar
   -  ``ename`` : the entry name
   -  ``elocal`` : True if the entry is local (local entries are written
      with a star character "*" by Grammar.Entry.print)
   -  ``estart`` and ``econtinue`` are parsers of the entry used in the
      `grammar machinery <grammars.html#a:Grammar-machinery>`__
   -  ``edesc`` : the entry description (see below)

   ::

      and g_desc 'te =
        [ Dlevels of list (g_level 'te)
        | Dparser of Stream.t 'te -> Obj.t ]

   The entry description.

   -  The constructor "``Dlevels``" is for entries built by
      "``Grammar.Entry.create``" and extendable by the EXTEND statement.
   -  The constructor "``Dparser``" is for entries built by
      "``Grammar.Entry.of_parser``".

   ::

      and g_level 'te =
        { assoc : g_assoc;
          lname : option string;
          lsuffix : g_tree 'te;
          lprefix : g_tree 'te }
      and g_assoc = [ NonA | RightA | LeftA ]

   Description of an entry level.

   -  ``assoc`` : the level associativity
   -  ``lname`` : the level name, if any
   -  ``lsuffix`` : the tree composed of the rules starting with
      "``SELF``"
   -  ``lprefix`` : the tree composed of the rules not starting with
      "``SELF``"

   ::

      and g_symbol 'te =
        [ Smeta of string and list (g_symbol 'te) and Obj.t
        | Snterm of g_entry 'te
        | Snterml of g_entry 'te and string
        | Slist0 of g_symbol 'te
        | Slist0sep of g_symbol 'te and g_symbol 'te
        | Slist1 of g_symbol 'te
        | Slist1sep of g_symbol 'te and g_symbol 'te
        | Sopt of g_symbol 'te
        | Sflag of g_symbol 'te
        | Sself
        | Snext
        | Stoken of Plexing.pattern
        | Stree of g_tree 'te ]

   Description of a rule symbol.

   -  The constructor "``Smeta``" is used by the extensions `FOLD0 and
      FOLD1 <grammars.html#a:Extensions-FOLD0-and-FOLD1>`__
   -  The constructor "``Snterm``" is the representation of a
      non-terminal (a call to another entry)
   -  The constructor "``Snterml``" is the representation of a
      non-terminal at some given level
   -  The constructor "``Slist0``" is the representation of the symbol
      LIST0
   -  The constructor "``Slist0sep``" is the representation of the
      symbol LIST0 followed by SEP
   -  The constructor "``Slist1``" is the representation of the symbol
      LIST1
   -  The constructor "``Slist1sep``" is the representation of the
      symbol LIST1 followed by SEP
   -  The constructor "``Sopt``" is the representation of the symbol OPT
   -  The constructor "``Sflag``" is the representation of the symbol
      FLAG
   -  The constructor "``Sself``" is the representation of the symbol
      SELF
   -  The constructor "``Snext``" is the representation of the symbol
      NEXT
   -  The constructor "``Stoken``" is the representation of a token
      pattern
   -  The constructor "``Stree``" is the representation of a anonymous
      rule list (between brackets).

   ::

      and g_action = Obj.t

   The semantic action, represented by a type "``Obj.t``" due to the
   specific typing of the EXTEND statement (the semantic action being
   able to be any function type, depending on the rule).
   ::

      and g_tree 'te =
        [ Node of g_node 'te
        | LocAct of g_action and list g_action
        | DeadEnd ]
      and g_node 'te =
        { node : g_symbol 'te; son : g_tree 'te; brother : g_tree 'te }
      ;

   The types of tree and tree nodes, representing a list of factorized
   rules in an entry level.

   -  The constructor "``Node``" is a representation of a symbol (field
      "``node``"), the rest of the rule tree (field "``son``"), and the
      following node, if this node fails (field "``brother``")
   -  The constructor "``LocAct``" is the representation of an action,
      which is a function having all pattern variables of the rule as
      parameters and returning the rule semantic action. The list of
      actions in the constructor correspond to possible previous actions
      when it happens that rules are masked by other rules.
   -  The constructor "``DeadEnd``" is a representation of a nodes where
      the tree fails or is in syntax error.

   ::

      type position =
        [ First
        | Last
        | Before of string
        | After of string
        | Level of string ]
      ;

   The type of position where an entry extension takes place.

   -  ``First`` : corresponds to FIRST
   -  ``Last`` : corresponds to LAST
   -  ``Before s`` : corresponds to BEFORE "s"
   -  ``After s`` : corresponds to AFTER "s"
   -  ``Level s`` : corresponds to LEVEL "s"

   The module contains other definitions but for internal use.

   .. rubric:: Grammar module
      :name: grammar-module

   Extensible grammars.

   This module implements the Camlp5 extensible grammars system.
   Grammars entries can be extended using the ``EXTEND`` statement,
   added by loading the Camlp5 "``pa_extend.cmo``" file.

   .. rubric:: main types and values
      :name: main-types-and-values

   ``type g = 'abstract;``
      The type of grammars, holding entries.

   ``value gcreate : Plexing.lexer (string * string) -> g;``
      Create a new grammar, without keywords, using the given lexer.

   ``value tokens : g -> string -> list (string * int);``
      Given a grammar and a token pattern constructor, returns the list
      of the corresponding values currently used in all entries of this
      grammar. The integer is the number of times this pattern value is
      used. Examples:

      -  The call: ``Grammar.tokens g ""`` returns the keywords list.
      -  The call: ``Grammar.tokens g "IDENT"`` returns the list of all
         usages of the pattern "IDENT" in the ``EXTEND`` statements.

   ``value glexer : g -> Plexing.lexer token;``
      Return the lexer used by the grammar

   ``type parsable = 'abstract;``
   ``value parsable : g -> Stream.t char -> parsable;``
      Type and value allowing to keep the same token stream between
      several calls of entries of the same grammar, to prevent loss of
      tokens. To be used with ``Entry.parse_parsable`` below

   ::

      module Entry =
        sig
          type e 'a = 'x;
          value create : g -> string -> e 'a;
          value parse : e 'a -> Stream.t char -> 'a;
          value parse_all : e 'a -> Stream.t char -> list 'a;
          value parse_token_stream : e 'a -> Stream.t token -> 'a;
          value parse_parsable : e 'a -> parsable -> 'a;
          value name : e 'a -> string;
          value of_parser : g -> string -> (Stream.t token -> 'a) -> e 'a;
          value print : e 'a -> unit;
          value find : e 'a -> string -> e Obj.t;
          external obj : e 'a -> Gramext.g_entry token = "%identity";
        end;

   Module to handle entries.

   -  ``Grammar.Entry.e`` : type for entries returning values of type
      "``'a``".
   -  ``Grammar.Entry.create g n`` : creates a new entry named "``n``"
      in the grammar "``g``".
   -  ``Grammar.Entry.parse e`` : returns the stream parser of the entry
      "``e``".
   -  ``Grammar.Entry.parse_all e`` : returns the stream parser
      returning all possible values while parsing with the entry
      "``e``": may return more than one value when the parsing algorithm
      is "``Grammar.Backtracking``".
   -  ``Grammar.Entry.parse_token_stream e`` : returns the token stream
      parser of the entry "``e``".
   -  ``Grammar.Entry.parse_parsable e`` : returns the parsable parser
      of the entry "``e``".
   -  ``Grammar.Entry.name e`` : returns the name of the entry "``e``".
   -  ``Grammar.Entry.of_parser g n p`` : makes an entry from a token
      stream parser.
   -  ``Grammar.Entry.print e`` : displays the entry "``e``" using
      "``Format``".
   -  ``Grammar.Entry.find e s`` : finds the entry named ``s`` in the
      rules of "``e``".
   -  ``Grammar.Entry.obj e`` : converts an entry into a
      "``Gramext.g_entry``" allowing to see what it holds.

   ``value of_entry : Entry.e 'a -> g;``
      Return the grammar associated with an entry.

   .. rubric:: printing grammar entries
      :name: printing-grammar-entries

   The function "``Grammar.Entry.print``" displays the current contents
   of an entry. Interesting for debugging, to look at the result of a
   syntax extension, to see the names of the levels.

   Try, for example, in the OCaml toplevel:

   ::

        Grammar.Entry.print Format.std_formatter Pcaml.expr

   The display does not include the patterns nor the semantic actions,
   whose sources are not recorded in the grammar entries data.

   Moreover, the local entries (not specified in the GLOBAL indicator of
   the EXTEND statement) are indicated with a star ("``*``") to inform
   that they are not directly accessible.

   .. rubric:: clearing grammars and entries
      :name: clearing-grammars-and-entries

   ::

      module Unsafe :
        sig
          value gram_reinit : g -> Plexing.lexer token -> unit;
          value clear_entry : Entry.e 'a -> unit;
        end;

   Module for clearing grammars and entries. To be manipulated with
   care, because: 1) reinitializing a grammar destroys all tokens and
   there may be problems with the associated lexer if there are
   keywords; 2) clearing an entry does not destroy the tokens used only
   by itself.

   -  ``Grammar.Unsafe.reinit_gram g lex`` removes the tokens of the
      grammar and sets "``lex``" as a new lexer for "``g``". Warning:
      the lexer itself is not reinitialized.
   -  ``Grammar.Unsafe.clear_entry e`` removes all rules of the entry
      "``e``".

   .. rubric:: scan entries
      :name: scan-entries

   ``value print_entry : Format.formatter -> Gramext.g_entry 'te -> unit;``
      General printer for all kinds of entries (obj entries).

   ::

      value iter_entry :
        (Gramext.g_entry 'te -> unit) -> Gramext.g_entry 'te -> unit;

   "``Grammar.iter_entry f e``" applies "``f``" to the entry "``e``" and
   transitively all entries called by "``e``". The order in which the
   entries are passed to "``f``" is the order they appear in each entry.
   Each entry is passed only once.

   ``value fold_entry : (Gramext.g_entry 'te -> 'a -> 'a) -> Gramext.g_entry 'te -> 'a -> 'a;``
      "``Grammar.fold_entry f e init``" computes
      "``(f eN .. (f     e2 (f e1 init)))``", where "``e1 .. eN``" are
      "``e``" and transitively all entries called by "``e``". The order
      in which the entries are passed to "``f``" is the order they
      appear in each entry. Each entry is passed only once.

   .. rubric:: parsing algorithm
      :name: parsing-algorithm

   ::

      type parse_algorithm = Gramext.parse_algorithm ==
        [ Imperative | Backtracking | DefaultAlgorithm ]
      ;

   Type of algorithm used in grammar entries.

   -  ``Imperative``: use imperative streams
   -  ``Functional``: use functional streams with limited backtracking
   -  ``Backtracking``: use functional streams with full backtracking
   -  ``DefaultAlgorithm``: use the general default algorithm set by the
      function "``set_default_algorithm``" below, or through the
      environment variable ``CAMLP5PARAM``.

   The default, when a grammar is created, is ``DefaultAlgorithm``.

   ``value set_algorithm : g -> parse_algorithm -> unit;``
      Set the parsing algorithm for all entries of a given grammar.

   ``value set_default_algorithm : parse_algorithm -> unit;``
      Set the default parsing algorithm for all grammars. If the
      environment variable CAMLP5PARAM contains "b", the default is
      ``Backtracking``; if it contains 'f', the default is
      ``Functional``; if it contains 'p', the default is ``Predictive``.

   ``value default_algorithm : unit -> parse_algorithm;``
      Return the current default algorithm.

   ``value backtrack_stalling_limit : ref int;``
      Limitation of backtracking to prevent stalling in case of syntax
      error. In backtracking algorithm, when there is a syntax error,
      the parsing continues trying to find another solution. It some
      grammars, it can be very long before checking all possibilities.
      This number limits the number of tokens tests after a backtrack.
      (The number of tokens tests is reset to zero when the token stream
      overtakes the last reached token.) The default is 10000. If set to
      0, there is no limit. Can be set by the environment variable
      CAMLP5PARAM by "l=value".

   ``value backtrack_parse : ref bool;``
      Deprecated since 2017-06-06; rather use "set_default_algorithm
      Backtracking".

   .. rubric:: functorial interface
      :name: functorial-interface

   Alternative for grammar use. Grammars are not Ocaml values: there is
   no type for them. Modules generated preserve the rule "an entry
   cannot call an entry of another grammar" by normal OCaml typing.

   ::

      module type GLexerType =
        sig
          type te = 'x;
          value lexer : Plexing.lexer te;
        end;

   The input signature for the functor "``Grammar.GMake``": "``te``" is
   the type of the tokens.
   ::

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
              value parse_token_stream : e 'a -> Stream.t te -> 'a;
              value name : e 'a -> string;
              value of_parser : string -> (Stream.t te -> 'a) -> e 'a;
              value print : e 'a -> unit;
              external obj : e 'a -> Gramext.g_entry te = "%identity";
            end;
          module Unsafe :
            sig
              value gram_reinit : Plexing.lexer te -> unit;
              value clear_entry : Entry.e 'a -> unit;
            end;
        end;

   Signature type of the functor "``Grammar.GMake``". The types and
   functions are almost the same than in generic interface, but:

   -  Grammars are not values. Functions holding a grammar as parameter
      do not have this parameter yet.
   -  The type "``parsable``" is used in function "``parse``" instead of
      the char stream, avoiding the possible loss of tokens.
   -  The type of tokens (expressions and patterns) can be any type
      (instead of (string \* string)); the module parameter must specify
      a way to show them as (string \* string).

   ``module GMake (L : GLexerType) : S with type te = L.te;``

   .. rubric:: grammar flags
      :name: grammar-flags

   ``value skip_item : 'a -> 'a;``
      ``Grammar.skip_item x`` can be called in a semantic action of a
      grammar rule to ask the grammar to skip that item if it is called
      in a list (LIST0 or LIST1). The function returns the item itself
      (for typing reasons) but its value is ignored. This function is
      used to allow IFDEF and IFNDEF for cases of constructor
      declarations and pattern matchings.

   ``value error_verbose : ref bool;``
      Flag for displaying more information in case of parsing error;
      default = "``False``".

   ``value warning_verbose : ref bool;``
      Flag for displaying warnings while extension; default =
      "``True``".

   ``value strict_parsing : ref bool;``
      Flag to apply strict parsing, without trying to recover errors;
      default = "``False``".

   .. rubric:: Diff module
      :name: diff-module

   Differences between two arrays. Used in Camlp5 sources, but can be
   used for other applications, independantly from Camlp5 stuff.

   ::

      value f : array 'a -> array 'a -> (array bool * array bool);

   ``Diff.f a1 a2`` returns a pair of boolean arrays ``(d1, d2)``.

   -  ``d1`` has the same size as ``a1``.
   -  ``d2`` has the same size as ``a2``.
   -  ``d1.(i)`` is ``True`` if ``a1.(i)`` has no corresponding value in
      ``a2``.
   -  ``d2.(i)`` is ``True`` if ``a2.(i)`` has no corresponding value in
      ``a1``.
   -  ``d1`` and ``d2`` have the same number of values equal to
      ``False``.

   Can be used, e.g., to write the ``diff`` program (comparison of two
   files), the input arrays being the array of lines of each file.

   Can be used also to compare two strings (they must have been exploded
   into arrays of chars), or two DNA strings, and so on.

   .. rubric:: Extfold module
      :name: extfold-module

   Module internally used to make the symbols `FOLD0 and
   FOLD1 <grammars.html#a:Extensions-FOLD0-and-FOLD1>`__ work in the
   EXTEND statement + extension "``pa_extfold.cmo``".

   .. rubric:: Extfun module
      :name: extfun-module

   Extensible functions.

   This module implements pattern matching extensible functions which
   work with the parsing kit "``pa_extfun.cmo``", the syntax of an
   extensible function being:

   ::

        extfun e with [ pattern_matching ]

   See chapter : `Extensible functions <extfun.html>`__.

   ``type t 'a 'b = 'x;``
      The type of the extensible functions of type ``'a ->       'b``.

   ``value empty : t 'a 'b;``
      Empty extensible function.
   ``value apply : t 'a 'b -> 'a -> 'b;``
      Apply an extensible function.
   ``exception Failure;``
      Match failure while applying an extensible function.
   ``value print : t 'a 'b -> unit;``
      Print patterns in the order they are recorded in the data
      structure.

   .. rubric:: Eprinter module
      :name: eprinter-module

   This module allows creation of printers, apply them and clear them.
   It is also internally used by the "``EXTEND_PRINTER``" statement.

   ``type t 'a = 'abstract;``
      Printer type, to print values of type "``'a``".

   ``type pr_context = Pprintf.pr_context;``
      Printing context.

   ``value make : string -> t 'a;``
      Builds a printer. The string parameter is used in error messages.
      The printer is created empty and can be extended with the
      "``EXTEND_PRINTER``" statement.

   ``value apply : t 'a -> pr_context -> 'a -> string;``
      Applies a printer, returning the printed string of the parameter.
   ``value apply_level : t 'a -> string -> pr_context -> 'a ->       string;``
      Applies a printer at some specific level. Raises "``Failure``" if
      the given level does not exist.

   ``value clear : t 'a -> unit;``
      Clears a printer, removing all its levels and rules.

   ``value print : t 'a -> unit;``
      Print printer patterns, in the order they are recorded, for
      debugging purposes.

   Some other types and functions exist, for internal use.

   .. rubric:: Fstream module
      :name: fstream-module

   This module implement functional streams and parsers together with
   backtracking parsers.

   To be used with syntax "``pa_fstream.cmo``". The syntax is:

   -  stream: "``fstream [: ... :]``"
   -  functional parser: "``fparser [ [: ... :] -> ... | ... ]``"
   -  backtracking parser: "``bparser [ [: ... :] -> ... | ... ]``"

   Functional parsers are of type:

   ::

        Fstream.t 'a -> option ('b * Fstream.t 'a)

   Backtracking parsers are of type:

   ::

        Fstream.t 'a -> option ('b * Fstream.t 'a * Fstream.kont 'a 'b)

   Functional parsers use limited backtrack, i.e if a rule fails, the
   next rule is tested with the initial stream; limited because in the
   case of a rule with two consecutive symbols "``a``" and "``b``", if
   "``b``" fails, the rule fails: there is no try with the next rule of
   "``a``".

   Backtracking parsers have full backtrack. If a rule fails, the next
   case of the previous rule is tested.

   .. rubric:: Functional streams
      :name: functional-streams

   ``type t 'a = 'x;``
      The type of 'a functional streams.

   ``value from : (int -> option 'a) -> t 'a;``
      "``Fstream.from f``" returns a stream built from the function
      "``f``". To create a new stream element, the function "``f``" is
      called with the current stream count. The user function "``f``"
      must return either "``Some <value>``" for a value or "``None``" to
      specify the end of the stream.

   ``value of_list : list 'a -> t 'a;``
      Return the stream holding the elements of the list in the same
      order.
   ``value of_string : string -> t char;``
      Return the stream of the characters of the string parameter.
   ``value of_channel : in_channel -> t char;``
      Return the stream of the characters read from the input channel.

   ``value iter : ('a -> unit) -> t 'a -> unit;``
      "``Fstream.iter f s``" scans the whole stream s, applying function
      "``f``" in turn to each stream element encountered.

   ``value next : t 'a -> option ('a * t 'a);``
      Return "``Some (a, s)``" where "``a``" is the first element of the
      stream and ``s`` the remaining stream, or "``None``" if the stream
      is empty.
   ``value empty : t 'a -> option (unit * t 'a);``
      Return "``Some ((), s)``" if the stream is empty where ``s`` is
      itself, else "``None``".
   ``value count : t 'a -> int;``
      Return the current count of the stream elements, i.e. the number
      of the stream elements discarded.
   ``value count_unfrozen : t 'a -> int;``
      Return the number of unfrozen elements in the beginning of the
      stream; useful to determine the position of a parsing error
      (longest path).

   .. rubric:: Backtracking parsers
      :name: backtracking-parsers

   ``type kont 'a 'b = [ K of unit -> option ('b * t 'a * kont 'a 'b) ];``
      The type of continuation of a backtracking parser.

   ``type bp 'a 'b = t 'a -> option ('b * t 'a * kont 'a 'b);``
      The type of a backtracking parser.

   ``value bcontinue : kont 'a 'b -> option ('b * t 'a * kont 'a 'b);``
      "``bcontinue k``" return the next solution of a backtracking
      parser.

   ``value bparse_all : bp 'a 'b -> t 'a -> list 'b;``
      "``bparse_all p strm``" return the list of all solutions of a
      backtracking parser applied to a functional stream.

   .. rubric:: Pprintf module
      :name: pprintf-module

   Definitions for pprintf statement.

   This module contains types and functions for the "pprintf" statement
   used by the syntax extension "pa_pprintf.cmo".

   ``type pr_context = { ind : int; bef : string; aft : string;       dang : string };``
      Printing context.

      -  "``ind``" : the current indendation
      -  "``bef``" : what should be printed before, in the same line
      -  "``aft``" : what should be printed after, in the same line
      -  "``dang``" : the dangling token to know whether parentheses are
         necessary

   ``value empty_pc : pr_context;``
      Empty printer context, equal to
      ``{ind = 0; bef = ""; aft =       ""; dang = ""}``

   ::

      value sprint_break :
        int -> int -> pr_context -> (pr_context -> string) ->
          (pr_context -> string) -> string;

   "``sprint_break nspaces offset pc f g``" concat the two strings
   returned by "``f``" and "``g``", either in one line, if it holds
   without overflowing (see module "``Pretty``"), with "``nspaces``"
   spaces betwen them, or in two lines with "``offset``" spaces added in
   the indentation for the second line.
   This function don't need to be called directly. It is generated by
   the "``pprintf``" statement according to its parameters when the
   format contains breaks, like "``@;``" and "``@ ``".
   ::

      value sprint_break_all :
        bool -> pr_context -> (pr_context -> string) ->
          list (int * int * pr_context -> string) -> string;

   "``sprint_break_all force_newlines pc f fl``" concat all strings
   returned by the list with separators "``f-fl``", the separators being
   the number of spaces and the offset like in the function
   "``sprint_break``". The function works as "all or nothing", i.e. if
   the resulting string does not hold on the line, all strings are
   printed in different lines (even if sub-parts could hold in single
   lines). If the parameter "``force_newline``" is "``True``", all
   strings are printed in different lines, no horizontal printing is
   tested.
   This function don't need to be called directly. It is generated by
   the "``pprintf``" statement according to its parameters when the
   format contains parenthesized parts with "break all" like "``@[<a>``"
   and "``@]``", or "``@[<b>``" and "``@]``".
   .. rubric:: Pretty module
      :name: pretty-module

   Pretty printing on strings. Basic functions.

   ``value horiz_vertic : (unit -> 'a) -> (unit -> 'a) -> 'a;``
      "``horiz_vertic h v``" first calls "``h``" to print the data
      horizontally, i.e. without newlines. If the displaying contains
      newlines or if its size exceeds the maximum line length (see
      variable "``line_length``" below), then the function "``h``" stops
      and the function "``v``" is called which can print using several
      lines.

   ``value sprintf : format 'a unit string -> 'a;``
      "``sprintf fmt ...``" formats some string like
      "``Printf.sprintf``" does, except that, if it is called in the
      context of the \*first\* function of "``horiz_vertic``" above, it
      checks whether the resulting string has chances to fit in the
      line. If not, i.e. if it contains newlines or if its length is
      greater than "``max_line_length.val``", the function gives up
      (raising some internal exception). Otherwise the built string is
      returned. "``sprintf``" behaves like "``Printf.sprintf``" if it is
      called in the context of the \*second\* function of
      "``horiz_vertic``" or without context at all.

   ``value line_length : ref int;``
      "``line_length``" is the maximum length (in characters) of the
      line. Default = 78. Can be set to any other value before printing.

   ``value horizontally : unit -> bool;``
      "``horizontally ()``" returns the fact that the context is an
      horizontal print.

   .. rubric:: Deprecated modules Stdpp and Token
      :name: deprecated-modules-stdpp-and-token

   The modules "``Stdpp``" and "``Token``" have been deprecated since
   version 5.00. The module "``Stdpp``" was renamed "``Ploc``" and most
   of its variables and types were also renamed. The module "``Token``"
   was renamed "``Plexing``"

   Backward compatibility is assured. See the files "``stdpp.mli``" and
   "``token.mli``" in the Camlp5 distribution to convert from old to new
   names, if any. After several versions or years, the modules
   "``Stdpp``" and "``Token``" will disappear from Camlp5.

   .. container:: trailer
