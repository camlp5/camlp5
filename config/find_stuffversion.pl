#!/usr/bin/env perl

use strict;
use Data::Dumper ;

{
  my $oversion = $ARGV[0] ;
  die "mal-formatted ocaml version detected: please report to maintainer with this output: ".Dumper(\@ARGV)
    unless $oversion =~ s,^(\d+(?:\.\d+)+)(?:[~-].*)?$,$1, ;

  if (-d "ocaml_stuff/$oversion" && -f "ocaml_src/lib/versdep/$oversion.ml") {
    print "$oversion\n";
    exit ;
  }

  print STDERR "WARNING: missing directory ocaml_stuff/$oversion\n" if (! -d "ocaml_stuff/$oversion") ;
  print STDERR "WARNING: missing file ocaml_src/lib/versdep/$oversion.ml\n" if (! -f "ocaml_src/lib/versdep/$oversion.ml") ;

  $oversion =~ s,\.\d+$,.0, ;
  if (-d "ocaml_stuff/$oversion" && -f "ocaml_src/lib/versdep/$oversion.ml") {
    print STDERR "WARNING: FALLING BACK to saved info for ocaml version $oversion; please report to maintainer\n" ;
    print "$oversion\n";
    exit ;
  }


  # let the configure script fail in the usual way
  print "$oversion\n";
}
