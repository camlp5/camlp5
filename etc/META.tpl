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

requires(byte,toploop,syntax,camlp5r) = "compiler-libs.common"
archive(byte,toploop,syntax,camlp5r) = "camlp5r.cma"

# Scheme-like syntax:
# Do #predicates "syntax,camlp5scheme", followed by #require "camlp5"
archive(byte,toploop,camlp5scheme) = "camlp5sch.cma"

# Standard ML-like syntax:
# Do #predicates "syntax,camlp5sml", followed by #require "camlp5"
archive(byte,toploop,camlp5sml) = "odyl.cma camlp5.cma camlp5_top.cma pa_sml.cmo"

# Lisp-like syntax:
# Do #predicates "syntax,camlp5lisp", followed by #require "camlp5"
archive(byte,toploop,camlp5lisp) = "odyl.cma camlp5.cma camlp5_top.cma pa_lisp.cmo"

# For the preprocessor itself:
archive(syntax,preprocessor,camlp5o) = "pa_o.cmo pa_op.cmo pr_dump.cmo"
archive(syntax,preprocessor,camlp5r) = "pa_r.cmo pa_rp.cmo pr_dump.cmo"
archive(syntax,preprocessor,camlp5sml) = "pa_sml.cmo pr_dump.cmo"
archive(syntax,preprocessor,camlp5scheme) = "pa_scheme.cmo pr_dump.cmo"
archive(syntax,preprocessor,camlp5lisp) = "pa_lisp.cmo pr_dump.cmo"
preprocessor = "camlp5 -nolib"

package "pa_r" (
  error(syntax_camlp5o) = "camlp5.pa_r cannot be used with syntax camlp5o"

  requires(toploop) = "camlp5"
  archive(toploop,-camlp5r)      = "pa_r.cmo pa_rp.cmo"
  archive(syntax,toploop,camlp5r)      = ""

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pa_r.cmo pa_rp.cmo"
  archive(syntax,preprocessor,native) = "pa_r.cmx pa_rp.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pa_r.cmo pa_rp.cmo"
    archive(native) = "pa_r.cmx pa_rp.cmx"
  )
)

package "pa_o" (
  error(syntax_camlp5r) = "camlp5.pa_o cannot be used with syntax camlp5r"

  requires(toploop) = "camlp5"
  archive(toploop,-camlp5o)      = "pa_o.cmo pa_op.cmo"
  archive(syntax,toploop,camlp5o)      = ""

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pa_o.cmo"
  archive(syntax,preprocessor,native) = "pa_o.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pa_o.cmo"
    archive(native) = "pa_o.cmx"
  )
)

package "pa_op" (
  error(syntax_camlp5r) = "camlp5.pa_op cannot be used with syntax camlp5r"

  requires(toploop) = "camlp5.pa_o"
  archive(toploop,-camlp5o)      = "pa_op.cmo"
  archive(syntax,toploop,camlp5o)      = ""

  requires(syntax,preprocessor) = "camlp5.pa_o"
  archive(syntax,preprocessor,-native) = "pa_op.cmo"
  archive(syntax,preprocessor,native) = "pa_op.cmx"

  package "link" (
    requires = "camlp5.pa_o.link"
    archive(byte) = "pa_op.cmo"
    archive(native) = "pa_op.cmx"
  )
)

package "pr_r" (
  requires(toploop) = "camlp5"
  archive(toploop)      = "pr_r.cmo pr_ro.cmo pr_rp.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pr_r.cmo pr_ro.cmo pr_rp.cmo"
  archive(syntax,preprocessor,native) = "pr_r.cmx pr_ro.cmx pr_rp.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pr_r.cmo pr_ro.cmo pr_rp.cmo"
    archive(native) = "pr_r.cmx pr_ro.cmx pr_rp.cmx"
  )
)

package "pr_o" (
  requires(toploop) = "camlp5"
  archive(toploop)      = "pr_o.cmo pr_op.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pr_o.cmo pr_op.cmo"
  archive(syntax,preprocessor,native) = "pr_o.cmx pr_op.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pr_o.cmo pr_op.cmo"
    archive(native) = "pr_o.cmx pr_op.cmx"
  )
)

package "pr_dump" (
  requires(toploop) = "camlp5"
  archive(toploop)      = "pr_dump.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pr_dump.cmo"
  archive(syntax,preprocessor,native) = "pr_dump.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pr_dump.cmo"
    archive(native) = "pr_dump.cmx"
  )
)

package "pr_depend" (
  requires(toploop) = "camlp5"
  archive(toploop)      = "pr_depend.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pr_depend.cmo"
  archive(syntax,preprocessor,native) = "pr_depend.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pr_depend.cmo"
    archive(native) = "pr_depend.cmx"
  )
)

package "pr_official" (
  requires(toploop) = "camlp5"
  archive(toploop)      = "pr_official.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pr_official.cmo"
  archive(syntax,preprocessor,native) = "pr_official.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pr_official.cmo"
    archive(native) = "pr_official.cmx"
  )
)

package "pa_scheme" (
  requires(toploop) = "camlp5"
  archive(toploop)      = "pa_scheme.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pa_scheme.cmo"
  archive(syntax,preprocessor,native) = "pa_scheme.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pa_scheme.cmo"
    archive(native) = "pa_scheme.cmx"
  )
)

package "pa_schemer" (
  requires(byte) = "camlp5"
  archive(byte) = "pa_schemer.cmo"
)

package "pr_scheme" (
  requires(toploop) = "camlp5"
  archive(toploop)      = "pr_scheme.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pr_scheme.cmo"
  archive(syntax,preprocessor,native) = "pr_scheme.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pr_scheme.cmo"
    archive(native) = "pr_scheme.cmx"
  )
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
  version = "@VERSION@"
  description = "Syntax extension: Quotations to create AST nodes"

  requires(toploop) = "camlp5"
  archive(toploop) = "q_MLast.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "q_MLast.cmo"
  archive(syntax,preprocessor,native) = "q_MLast.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "q_MLast.cmo"
    archive(native) = "q_MLast.cmx"
  )
)

package "parser_quotations" (
  version = "@VERSION@"
  description = "Syntax extension: Quotations to create AST nodes, but using pa_r/pa_o"

  requires(toploop) = "camlp5.parser_quotations_base"
  archive(toploop) = "q_ast.cmo"

  requires(syntax,preprocessor) = "camlp5.parser_quotations_base"
  archive(syntax,preprocessor,-native) = "q_ast.cmo"
  archive(syntax,preprocessor,native) = "q_ast.cmx"

  package "link" (
    requires = "camlp5.parser_quotations_base.link"
    archive(byte) = "q_ast.cmo"
    archive(native) = "q_ast.cmx"
  )
)

package "parser_quotations_base" (
  version = "@VERSION@"
  description = "Syntax extension: Quotations to create AST nodes (this is the base module), but using pa_r/pa_o"

  requires(toploop) = "camlp5"
  archive(toploop) = "q_ast_base.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "q_ast_base.cmo"
  archive(syntax,preprocessor,native) = "q_ast_base.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "q_ast_base.cmo"
    archive(native) = "q_ast_base.cmx"
  )
)

package "phony_quotations" (
  version = "@VERSION@"
  description = "Syntax extension: Phony quotations"

  requires(toploop) = "camlp5"
  archive(toploop) = "q_phony.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "q_phony.cmo"
  archive(syntax,preprocessor,native) = "q_phony.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "q_phony.cmo"
    archive(native) = "q_phony.cmx"
  )
)


package "extend_m" (
  error(syntax_camlp5o) = "camlp5.extend_m cannot be used with syntax camlp5o"

  requires(toploop) = "camlp5.extend"
  archive(toploop)      = "pa_extend_m.cmo"

  requires(syntax,preprocessor) = "camlp5.extend"
  archive(syntax,preprocessor,-native) = "pa_extend_m.cmo"
  archive(syntax,preprocessor,native) = "pa_extend_m.cmx"
  requires = "camlp5.extend"

  package "link" (
  requires = "camlp5.extend"
  archive(byte) = "pa_extend_m.cmo"
  archive(native) = "pa_extend_m.cmx"
  )
)

package "extend" (
  warning(syntax_camlp5o) = "camlp5.extend SHOULD NOT be used with syntax camlp5o"

  requires(toploop) = "camlp5"
  archive(toploop)      = "pa_extend.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pa_extend.cmo"
  archive(syntax,preprocessor,native) = "pa_extend.cmx"
  requires = "camlp5"

  package "link" (
  requires = "camlp5"
  archive(byte) = "pa_extend.cmo"
  archive(native) = "pa_extend.cmx"
  )
)

package "extfun" (
  version = "@VERSION@"
  description = "Syntax extension: Extensible functions"

  requires(toploop) = "camlp5"
  archive(toploop)      = "pa_extfun.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pa_extfun.cmo"
  archive(syntax,preprocessor,native) = "pa_extfun.cmx"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pa_extfun.cmo"
    archive(native) = "pa_extfun.cmx"
  )
)


package "extfold" (
  version = "@VERSION@"
  description = "Syntax extension: Extensible folders"

  requires(toploop) = "camlp5.extend"
  archive(toploop)      = "pa_extfold.cmo"

  requires(syntax,preprocessor) = "camlp5.extend"
  archive(syntax,preprocessor,-native) = "pa_extfold.cmo"
  archive(syntax,preprocessor,native) = "pa_extfold.cmx"
  requires = "camlp5"

  package "link" (
    requires = "camlp5.extend.link"
    archive(byte) = "pa_extfold.cmo"
    archive(native) = "pa_extfold.cmx"
  )
)

package "extprint" (
  version = "@VERSION@"
  description = "Syntax extension: Extensible printers"

  requires(toploop) = "camlp5"
  archive(toploop)      = "pa_extprint.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pa_extprint.cmo"
  archive(syntax,preprocessor,native) = "pa_extprint.cmx"
  requires = "camlp5"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pa_extprint.cmo"
    archive(native) = "pa_extprint.cmx"
  )
)

package "pprintf" (
  version = "@VERSION@"
  description = "Syntax extension: ``pprintf'' preprocessor support"

  requires(toploop) = "camlp5"
  archive(toploop)      = "pa_pprintf.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pa_pprintf.cmo"
  archive(syntax,preprocessor,native) = "pa_pprintf.cmx"
  requires = "camlp5"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pa_pprintf.cmo"
    archive(native) = "pa_pprintf.cmx"
  )
)


package "pa_lexer" (
  version = "@VERSION@"
  description = "Syntax extension: Stream lexers"

  requires(toploop) = "camlp5"
  archive(toploop)      = "pa_lexer.cmo"

  requires(syntax,preprocessor) = "camlp5"
  archive(syntax,preprocessor,-native) = "pa_lexer.cmo"
  archive(syntax,preprocessor,native) = "pa_lexer.cmx"
  requires = "camlp5"

  package "link" (
    requires = "camlp5"
    archive(byte) = "pa_lexer.cmo"
    archive(native) = "pa_lexer.cmx"
  )
)

package "fstream" (
  version = "@VERSION@"
  description = "Syntax extension: Functional stream parsers"

  requires(toploop) = "camlp5"
  archive(toploop) = "pa_fstream.cmo"

  archive(syntax,preprocessor) = "pa_fstream.cmo"
  archive(syntax,preprocessor,-native) = "pa_fstream.cmo"
  archive(syntax,preprocessor,native) = "pa_fstream.cmx"

  requires = "camlp5"
)

package "macro" (
  version = "@VERSION@"
  description = "Syntax extension: Conditional compilation"

  requires(toploop) = "camlp5"
  archive(toploop) = "pa_macro.cmo"

  archive(syntax,preprocessor) = "pa_macro.cmo"
  archive(syntax,preprocessor,-native) = "pa_macro.cmo"
  archive(syntax,preprocessor,native) = "pa_macro.cmx"
  requires = "camlp5"
)

package "macro_gram" (
  version = "@VERSION@"
  description = "Syntax extension: Conditional compilation"

  requires(toploop) = "camlp5,camlp5.macro"
  archive(toploop) = "pa_macro_gram.cmo"

  archive(syntax,preprocessor) = "pa_macro_gram.cmo"
  archive(syntax,preprocessor,-native) = "pa_macro_gram.cmo"
  archive(syntax,preprocessor,native) = "pa_macro_gram.cmx"
  requires = "camlp5,camlp5.macro"
)

package "pragma" (
  version = "@VERSION@"
  description = "Syntax extension: (experimental) Pragmas"

  archive(syntax,preprocessor) = "pa_pragma.cmo"
  archive(syntax,preprocessor,-native) = "pa_pragma.cmo"
  archive(syntax,preprocessor,native) = "pa_pragma.cmx"
  requires = "camlp5"
)

package "toploop" (
  package "link" (
  requires = "camlp5"
  version = "@VERSION@"
  description = "Internal support for toploop to use Camlp5"
  archive(byte) = "camlp5_top_funs.cmo"
  )

  archive(byte,toploop) = "camlp5_top.cma"
)
