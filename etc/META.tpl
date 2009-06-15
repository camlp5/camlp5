# Specifications for the "camlp5" preprocessor:
requires = ""
version = "@VERSION@"
description = "Base for camlp5 syntax extensions"
directory = "@CAMLP5DIR@"

# For the toploop:
archive(byte,toploop,camlp5o) = "camlp5o.cma"
archive(byte,toploop,camlp5r) = "camlp5r.cma"

# Scheme-like syntax:
# Do #predicates "syntax,camlp5scheme", followed by #require "camlp5"
archive(byte,toploop,camlp5scheme) = "camlp5sch.cma"

# Standard ML-like syntax:
# Do #predicates "syntax,camlp5sml", followed by #require "camlp5"
archive(byte,toploop,camlp5sml) = "gramlib.cma camlp5_top.cma pa_sml.cmo"

# Lisp-like syntax:
# Do #predicates "syntax,camlp5lisp", followed by #require "camlp5"
archive(byte,toploop,camlp5lisp) = "gramlib.cma camlp5_top.cma pa_lisp.cmo"

# For the preprocessor itself:
archive(syntax,preprocessor,camlp5o) = "pa_o.cmo pa_op.cmo pr_dump.cmo"
archive(syntax,preprocessor,camlp5r) = "pa_r.cmo pa_rp.cmo pr_dump.cmo"
archive(syntax,preprocessor,camlp5sml) = "pa_sml.cmo pr_dump.cmo"
archive(syntax,preprocessor,camlp5scheme) = "pa_scheme.cmo pr_dump.cmo"
archive(syntax,preprocessor,camlp5lisp) = "pa_lisp.cmo pr_dump.cmo"
preprocessor = "camlp5 -nolib"

package "gramlib" (
  requires(toploop) = "camlp5"
  version = "@VERSION@"
  description = "Grammar library to create syntax extensions"
  archive(byte) = "gramlib.cma"
  archive(byte,toploop) = ""  # already contained in camlp5*.cma
  archive(native) = "gramlib.cmxa"
)

package "quotations" (
  requires = "camlp5"
  version = "@VERSION@"
  description = "Syntax extension: Quotations to create AST nodes"
  archive(syntax,preprocessor) = "q_MLast.cmo"
  archive(syntax,toploop) = "q_MLast.cmo"
)

package "phony_quotations" (
  requires = "camlp5"
  version = "@VERSION@"
  description = "Syntax extension: Phony quotations"
  archive(syntax,preprocessor) = "q_phony.cmo"
  archive(syntax,toploop) = "q_phony.cmo"
)

package "extend" (
  requires = "camlp5"
  version = "@VERSION@"
  description = "Syntax extension: EXTEND the camlp5 grammar"
  archive(syntax,preprocessor) = "pa_extend.cmo"
  archive(syntax,toploop) = "pa_extend.cmo"
)

package "extfun" (
  requires = "camlp5"
  version = "@VERSION@"
  description = "Syntax extension: Extensible functions"
  archive(syntax,preprocessor) = "pa_extfun.cmo"
  archive(syntax,toploop) = "pa_extfun.cmo"
)

package "fstream" (
  requires = "camlp5"
  version = "@VERSION@"
  description = "Syntax extension: Functional stream parsers"
  archive(syntax,preprocessor) = "pa_fstream.cmo"
  archive(syntax,toploop) = "pa_fstream.cmo"
)

package "macro" (
  requires = "camlp5"
  version = "@VERSION@"
  description = "Syntax extension: Conditional compilation"
  archive(syntax,preprocessor) = "pa_macro.cmo"
  archive(syntax,toploop) = "pa_macro.cmo"
)
