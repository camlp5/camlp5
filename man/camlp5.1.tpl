.TH CAMLP5 1  "" "INRIA"
.SH NAME
camlp5n - Pre-Precessor-Pretty-Printer for ocamln
.br
mkcamlp5n - Create custom camlp5n
.br
mkcamlp5n.opt - Create custom camlp5n (native code)
.br
ocpp5 - Universal preprocessor

.SH SYNOPSIS
.B camlp5n
[
load-options
] [--] [
other-options
]
.br
.B camlp5no
[
load-options
] [--] [
other-options
]
.br
.B camlp5nr
[
load-options
] [--] [
other-options
]
.br
.B camlp5nsch
[
load-options
] [--] [
other-options
]
.br
.B camlp5no.cma
.br
.B camlp5nr.cma
.br
.B camlp5nsch.cma
.br
.B mkcamlp5n
.br
.B mkcamlp5n.opt
.br
.B ocpp5
[
load-options
]
file
.LP
.br
.B camlp5no.opt
[--] [
other-options
]
.br
.B camlp5nr.opt
[--] [
other-options
]

.SH DESCRIPTION
.B camlp5n
is a Pre-Processor-Pretty-Printer for OCaml, parsing a source
file and printing some result on standard output.
.LP
.B camlp5no,
.B camlp5nr
and
.B camlp5nsch
are versions of
.B camlp5n
with some files already loaded (see further).
.LP
.B camlp5no.cma,
.B camlp5nr.cma
and
.B camlp5nsch.cma
are files to be loaded in ocamln toplevel to use the camlp5n machinery
.LP
.B mkcamlp5n
and
.B mkcamlp5n.opt
creates camlp5n executables with almost the same options than
ocamlnmktop. See further.
.LP
.B ocpp5
is an universal preprocessor, treating any kind of source file,
generating the same text with the possible quotations expanded.
.LP
.B camlp5no.opt
and
.B camlp5nr.opt
are versions of camlp5no and camlp5nr compiled by the native-code compiler
ocamlnopt. They are faster but not extensible. And they are not available
in all installations of camlp5n.

.SH LOAD OPTIONS

The load options select parsing and printing actions recorded in OCaml
object files (ending with .cmo or .cma). Several usage of these options
are authorized. They must precede the other options.

.LP
An optional
.B \-\-
may end the load options.

.TP
.BI \-I\  directory
Add
.I directory
in the search path for files loaded. Unless the option \-nolib is used,
the camlp5n library directory is appended to the path. Warning: there is
no automatic search in the current directory: add "\-I ." for this.
.TP
.B \-where
Print camlp5n library directory name and exit.
.TP
.B \-nolib
No automatic search for objects files in camlp5n library directory.
.TP
.BI object-file
The file is loaded in camlp5n core.

.SH OTHER OPTIONS

.LP
The others options are:

.TP
.I file
Treat
.I file
as an interface file if it ends with .mli and as an implementation file
if it ends with .ml.

.TP
.BI \-intf\  file
Treat
.I file
as an interface file, whatever its extension.
.TP
.BI \-impl\  file
Treat
.I file
as an implementation file, whatever its extension.
.TP
.B \-unsafe
Generate unsafe accesses to arrays and strings.
.TP
.B \-noassert
Do not compile assertion checks.
.TP
.B \-verbose
More verbose in parsing errors.
.TP
.BI \-QD\  file
Dump in
.I file
in case of syntax error in the result of a quotation expansion.
.TP
.BI \-o\  out-file
Print the result on out-file instead of standard output. File is opened
with open_out_bin (see OCaml library Pervasives).
.TP
.B \-v
Print the version number and exit.
.TP
.B \-help
Print the available options and exit. This print includes the options
possibly added by the loaded object files.

.LP
The others options can be extended by loaded object files. The provided
files add the following options:

.TP
.BI \-l\  line-length
Added by pr_o.cmo and pr_r.cmo: set the line length (default 78).
.TP
.BI \-sep\  string
Added by pr_o.cmo and pr_r.cmo: print this string between phrases instead
of comments.
.TP
.BI \-no_ss
Added by pr_o.cmo: do not print double semicolons
.TP
.BI \-D\  ident
Added by pa_macro.cmo: define the ident.
.TP
.BI \-U\  ident
Added by pa_macro.cmo: undefine the ident.

.SH "PROVIDED FILES"
These files are installed in the directory LIBDIR/camlp5n.

.LP
Parsing files:
.nf
.ta 1c
	pa_r.cmo: revised syntax
	pa_rp.cmo: streams and parsers
	pa_lexer.cmo: lexers
	pa_o.cmo: normal syntax
	pa_op.cmo: streams and parsers
	pa_oop.cmo: streams and parsers (without code optimization)
	pa_scheme.cmo: scheme syntax
	pa_extend.cmo: syntax extension for grammars
	pa_extfold.cmo: extension of pa_extend with FOLD0 and FOLD1
	pa_extfun.cmo: syntax extension for extensible functions
	pa_extprint.cmo: syntax extensions for extensible printers
	pa_pprintf.cmo: syntax extension for pprintf statement
	pa_fstream.cmo: syntax extension for functional streams
	pa_macro.cmo: add macros (ifdef, define) like in C
	pa_lefteval.cmo: left-to-right evaluation of parameters
	pa_pragma.cmo: directive #pragma
.fi
.LP
Printing files:
.nf
.ta 1c
	pr_r.cmo: revised syntax without objects and labels
	pr_ro.cmo: revised syntax for objects and labels
	pr_rp.cmo: try to rebuild streams and parsers syntax
	pr_o.cmo: normal syntax
	pr_op.cmo: try to rebuild streams and parsers syntax
	pr_scheme.cmo: Scheme syntax
	pr_schemep.cmo: try to rebuild streams and parsers syntax
	pr_extend.cmo: try to rebuild EXTEND statements
	pr_extfun.cmo: try to rebuild extfun statements
	pr_extprint.cmo: try to rebuild EXTEND_PRINTER statements
	pr_dump.cmo: dump syntax tree for ocamln compiler
	pr_depend.cmo: file dependencies
	pr_null.cmo: no output
.fi
.LP
Quotation expanders:
.nf
.ta 1c
	q_MLast.cmo: syntax tree nodes (in revised syntax)
	q_ast.cmo: syntax tree nodes in user full syntax
	q_phony.cmo: keeping quotations for pretty printing
.fi
.LP
The command
.B camlp5no
is a shortcut for:
.nf
.ta 1c
	camlp5n pa_o.cmo pa_op.cmo pr_dump.cmo
.fi
.LP
The command
.B camlp5nr
is a shortcut for:
.nf
.ta 1c
	camlp5n pa_r.cmo pa_rp.cmo pr_dump.cmo
.fi
.LP
The command
.B camlp5nsch
is a shortcut for:
.nf
.ta 1c
	camlp5n pa_scheme.cmo pr_dump.cmo
.fi
.LP
.LP
The file
.B camlp5no.cma
can be loaded in the toplevel to start camlp5n with OCaml syntax.
.LP
The file
.B camlp5nr.cma
can be loaded in the toplevel to start camlp5n with revised syntax.
.LP
The file
.B camlp5nsch.cma
can be loaded in the toplevel to start camlp5n with Scheme syntax.

.SH "MKCAMLP5"

.B mkcamlp5n
and
.B mkcamlp5n.opt
creates camlp5n executables with almost the same options than
ocamlnmktop. The version
.B mkcamlp5n.opt
can create native code executables, faster but not extensible.
.LP
For mkcamlp5n, the interfaces to be visible must be explicitly added in
the command line as ".cmi" files. For example, how to add the the
OCaml module "str":
.nf
.ta 1c
	mkcamlp5n \-custom str.cmi str.cma \-cclib \-lstr \-o camlp5nstr
.fi
.LP

.SH "ENVIRONMENT VARIABLE"

The following environment variable is also consulted:

.TP
.B CAMLP5PARAM
Set the grammars parsing algorithm parameters.
This variable must be a sequence of parameter specifications.
A parameter specification is a letter optionally followed by an =
and a value. There are four possible parameters:

.TP
.BR b \ (backtrack)
Set the backtrack algorithm as default.
.TP
.BR t \ (trace)
Trace symbols (terminals and non-terminals) while parsing with backtracking.
.TP
.BR y \ (trace-stalling)
In backtracking, trace the advance in the input stream (number of unfrozen
tokens) and the possible stalling (number of tokens tests).
.TP
.BR l \ (maximum-stalling)
Set the maximum stalling value.

.SH "FILES"
Library directory of camlp5n in the present installation:
.br
LIBDIR/camlp5n

.SH "SEE ALSO"
Camlp5 - Reference Manual
.br
ocamlnc(1), ocamln(1), ocamlnmktop(1).

.SH AUTHOR
Daniel de Rauglaudre, INRIA Rocquencourt.
