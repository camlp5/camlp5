#!/usr/bin/perl

use strict ;

our $verbose ;

while (@ARGV) {
  if ($ARGV[0] eq '-v') {
    shift @ARGV ;
    $verbose = 1 ;
  }
  else { last ; }
}

{
  my $launch = "env TOP=.. ocamlfind camlp5-buildscripts/LAUNCH --" ;

  foreach my $f (@ARGV) {
    my $l = `head -1 $f` ;
    if ($l =~ m/camlp5r(.*)\*\)/) {
      v_system("${launch} ocamldep -pp 'camlp5r -I ../local-install/lib/camlp5 $1' $f")
    }
    elsif ($l =~ m/camlp5o(.*)\*\)/) {
      v_system("${launch} ocamldep -pp 'camlp5r -I ../local-install/lib/camlp5 $1' $f")
    }
    else {
      v_system("${launch} ocamldep -pp 'camlp5o -I ../local-install/lib/camlp5' $f")
    }
  }
}

sub v_system {
  my $cmd = shift;
  print STDERR "<<$cmd>>\n" if ($main::verbose);
  system $cmd;
}
