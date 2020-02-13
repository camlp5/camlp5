#!/usr/bin/env perl

use strict ;

use Data::Dumper ;
use IPC::System::Simple qw(systemx runx capturex $EXITVAL);
use String::ShellQuote ;

my @toremove ;

END { v_systemx("rm", "-f", @toremove) ; }

our $verbose ;

{
  my @interfaces ;
  my @options ;

  my $opt ;
  if ($0 =~ /mkcamlp5\.opt.*/) {
    $opt = 1 ;
  }

  while (@ARGV) {
    if ($ARGV[0] eq '-help') {
      shift @ARGV ;
      usage() ; exit ;
    }
    elsif ($ARGV[0] eq '-v') {
      shift @ARGV ;
      $verbose = 1 ;
    }
    elsif ($ARGV[0] =~ m,([^\./]+)\.cmi$,) {
      die "cannot specify .cmi files for $0" if $opt ;
      shift @ARGV ;
      push(@interfaces, ucfirst($1)) ;
    }
    else {
      push(@options, shift @ARGV) ;
    }
  }

  my @link ;
  unless ($opt) {
    my $stringified = join('; ', map { '"'.$_.'"' ; } @interfaces) ;
    my $txt = <<"EOF";
Dynlink.set_allowed_units [
  $stringified
] ;;
EOF
    push(@toremove, "link$$.ml", "link$$.cmi", "link$$.cmo", "link$$.cmx") ;
    f_write("link$$.ml", $txt) ;
    push(@link, "link$$.ml") ;
  }

  v_systemx("ocamlfind",
	    ($opt ? "ocamlopt" : "ocamlc"),
	    "-package", "camlp5",
	    "-linkall", "-linkpkg",
	    ($opt ? ("odyl.cmxa", "camlp5.cmxa") : ("odyl.cma", "camlp5.cma")),
	    @link, @options,
	    ($opt ? "odyl.cmx" : "odyl.cmo")
	   ) ;
}

sub v_systemx {
  my $codes ;
  $codes = shift if (ref($_[0]) eq 'ARRAY') ;
  my @cmd = @_ ;
  print STDERR join(' ', map { shell_quote($_) } @cmd)."\n" if ($main::verbose) ;

  if ($codes) {
    return runx($codes, @cmd) ;
  }
  else {
    return runx(@cmd) ;
  }
}

sub f_write {
  my $f = shift;
  open(F,">$f") || die "cannot open $f for writing";
  print F @_;
  close(F);
}

sub usage {
  print <<"EOF";
Options:
  -I <dir>   Add directory in search path for object files

All options of ocamlc (and ocamlfind) are also available

Files:
  .cmi file  Add visible interface for possible future loading
  .cmo file  Load this file in core
  .cma file  Load this file in core

EOF
}
