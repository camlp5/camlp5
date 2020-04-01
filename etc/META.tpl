# Specifications for the "camlp5" preprocessor:
requires = ""
version = "@VERSION@"
description = "Base for camlp5 syntax extensions"
directory = "@CAMLP5DIR@"

# For linking
archive(byte) = "odyl.cma camlp5.cma"
archive(native) = "odyl.cmxa camlp5.cmxa"

# For the toploop:
archive(byte,toploop) = "odyl.cma camlp5.cma"
archive(byte,toploop,syntax,camlp5o) = "camlp5o.cma"
archive(byte,toploop,syntax,camlp5r) = "camlp5r.cma"

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

package "pa_r" (
  error(camlp5o) = "camlp5.pa_r cannot be used with syntax camlp5o"

  requires(syntax,toploop) = "camlp5"
  archive(syntax,toploop,-camlp5r)      = "pa_r.cmo pa_rp.cmo"
  archive(syntax,toploop,camlp5r)      = ""

  package "syntax" (
    archive(syntax,preprocessor) = "pa_r.cmo pa_rp.cmo"
  )

  requires(byte) = "camlp5"
  archive(byte) = "pa_r.cmo pa_rp.cmo"
)

package "pa_o" (
  error(camlp5r) = "camlp5.pa_o cannot be used with syntax camlp5r"

  requires(syntax,toploop) = "camlp5"
  archive(syntax,toploop,-camlp5o)      = "pa_o.cmo pa_op.cmo"
  archive(syntax,toploop,camlp5o)      = ""

  package "syntax" (
    archive(syntax,preprocessor) = "pa_o.cmo"
  )

  requires(byte) = "camlp5"
  archive(byte) = "pa_o.cmo"
)

package "pa_op" (
  error(camlp5r) = "camlp5.pa_op cannot be used with syntax camlp5r"

  requires(syntax,toploop) = "camlp5.pa_o"
  archive(syntax,toploop,-camlp5o)      = "pa_op.cmo"
  archive(syntax,toploop,camlp5o)      = ""

  package "syntax" (
    requires(syntax,preprocessor) = "camlp5.pa_o.syntax"
    archive(syntax,preprocessor) = "pa_op.cmo"
  )

  requires(byte) = "camlp5.pa_o"
  archive(byte) = "pa_op.cmo"
)

package "pr_r" (
  requires(syntax,toploop) = "camlp5"
  archive(syntax,toploop)      = "pr_r.cmo pr_ro.cmo pr_rp.cmo"

  package "syntax" (
    archive(syntax,preprocessor) = "pr_r.cmo pr_ro.cmo pr_rp.cmo"
  )

  requires(byte) = "camlp5"
  archive(byte) = "pr_r.cmo pr_ro.cmo pr_rp.cmo"
)

package "pr_o" (
  requires(syntax,toploop) = "camlp5"
  archive(syntax,toploop)      = "pr_o.cmo pr_op.cmo"

  package "syntax" (
    archive(syntax,preprocessor) = "pr_o.cmo pr_op.cmo"
  )

  requires(byte) = "camlp5"
  archive(byte) = "pr_o.cmo pr_op.cmo"
)

package "pr_dump" (
  requires(syntax,toploop) = "camlp5"
  archive(syntax,toploop)      = "pr_dump.cmo"

  package "syntax" (
    archive(syntax,preprocessor) = "pr_dump.cmo"
  )

  requires(byte) = "camlp5"
  archive(byte) = "pr_dump.cmo"
)

package "pr_official" (
  requires(byte) = "camlp5"
  archive(byte) = "pr_official.cmo"
)

package "pa_scheme" (
  requires(byte) = "camlp5"
  archive(byte) = "pa_scheme.cmo"
)

package "pa_schemer" (
  requires(byte) = "camlp5"
  archive(byte) = "pa_schemer.cmo"
)

package "pr_scheme" (
  requires(byte) = "camlp5"
  archive(byte) = "pr_scheme.cmo"
)

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

  package "syntax" (
    archive(syntax,preprocessor) = "q_MLast.cmo"
    archive(syntax,toploop) = "q_MLast.cmo"
  )

  archive(byte) = "q_MLast.cmo"
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

package "pragma" (
  requires = "camlp5"
  version = "@VERSION@"
  description = "Syntax extension: (experimental) Pragmas"
  archive(syntax,preprocessor) = "pa_pragma.cmo"
  archive(syntax,toploop) = "pa_pragma.cmo"
)
