#!/usr/bin/env perl

use strict ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for the "pa_sexp" preprocessor:
description = "pa_sexp parsing & quotation support"

  requires(toploop) = "camlp5,camlp5.quotations"
  archive(toploop) = "sexp.cmo pa_sexp.cmo q_sexp.cmo"

    requires(syntax,preprocessor) = "camlp5,camlp5.quotations"
    archive(syntax,preprocessor,-native) = "sexp.cmo pa_sexp.cmo q_sexp.cmo"
    archive(syntax,preprocessor,native) = "sexp.cmx pa_sexp.cmx q_sexp.cmx"

  package "link" (
  requires(byte) = "camlp5,camlp5.quotations.link"
  archive(byte) = "sexp.cmo pa_sexp.cmo q_sexp.cmo"
  )
  requires = "camlp5,camlp5.quotations"

  package "runtime" (
    directory = "$destdir/pa_sexp"
    archive(byte) = "sexp.cmo"
  )

EOF
