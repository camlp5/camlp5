#!/usr/bin/env perl

use strict ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for "sexp_example"
description = "sexp example parsing & quotation support"

package "runtime" (
  directory = "$destdir/sexp_example"
  archive(toploop) = "sexp.cmo"
)

package "quotations" (
  requires(toploop) = "camlp5,camlp5.quotations,sexp_example.runtime"
  archive(toploop) = "q_sexp.cmo"

    requires(syntax,preprocessor) = "camlp5,camlp5.quotations,sexp_example.runtime"
    archive(syntax,preprocessor,-native) = "q_sexp.cmo"
    archive(syntax,preprocessor,native) = "q_sexp.cmx"

  package "link" (
  requires(byte) = "camlp5,camlp5.quotations.link"
  archive(byte) = "q_sexp.cmo"
  )
  requires = "camlp5,camlp5.quotations"
)

package "pa_sexp" (
  requires(toploop) = "camlp5"
  archive(toploop) = "pa_sexp.cmo"

    requires(syntax,preprocessor) = "camlp5,fmt,sexp_example.runtime"
    archive(syntax,preprocessor,-native) = "pa_sexp.cmo"
    archive(syntax,preprocessor,native) = "pa_sexp.cmx"

  package "link" (
  requires(byte) = "camlp5,fmt,sexp_example.runtime"
  archive(byte) = "pa_sexp.cmo"
  )
  requires = "camlp5,fmt,sexp_example.runtime"
)

EOF
