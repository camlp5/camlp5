# Camlp5 Tutorial Examples

This directory contains tutorial examples for Camlp5.  Many of these
examples are written in "revised syntax", because they use
syntax-extensions that only work with revised syntax.  They're ordered
by complexity thus:

1. `streams`: a simple calculator written using camlp5 stream-parsers,
in "original syntax", and a `Stdlib.Genlex` lexer.

2. `streams-revised`: the same calculator, but translated to "revised syntax".

3. `calc` : the same calculator, but with the parser written using
camlp5's extensible grammars, and using the built-in lexer.

4. `calc+functorial`: the same calculator, but this time we use the
functorial version of grammars (grammar machinery defined by a
functor, so you can have many grammars at the same time.

All the *following* examples add onto the previous, adding variables
and assignment statements.  In addition, there is a pretty-printer
(written using Camlp5's extensible printers) and the parser/printer
preserves (c++-style single-line) comments in its output (so, a
demonstration of how to preserve comments, and when using ocamllex).

5. `calc+ocamllex`: the same calculator, but with some added function
(variables, sequence of statements, assignment) and written using an
ocamllex lexer.  There's a pretty-printer, and we preserve comments
that come before statements.

5. `calc+pa_lexer`: the same as #3, but with a camlp5 lexer (a copy of
the builtin lexer, modified to support C++ style single-line comments).

6. `protobuf2`: a Google Protocol Buffers IDL (version 2) parser and
pretty-printer.  Again, we preserve comments at statement-level.
