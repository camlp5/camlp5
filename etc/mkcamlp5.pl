#!/usr/bin/env perl

use strict ;

use Data::Dumper ;
use IPC::System::Simple qw(systemx runx capturex $EXITVAL);
use String::ShellQuote ;

my @toremove ;

our $ocaml_version = capturex("ocamlc","-version") ;
chomp $ocaml_version ;
our $ocaml_lib = capturex("ocamlc","-where") ;
chomp $ocaml_lib ;

our $verbose ;
our $preserve ;
our $noexecute ;
our $randompid = $$ ;

END { systemx("rm", "-f", @toremove) unless $preserve ; }

{
  my @interfaces ;
  my @options ;
  my @predicates = ("syntax","preprocessor") ;
  my @packages = ("camlp5") ;

  my $opt ;
  if ($0 =~ /mkcamlp5\.opt.*/) {
    $opt = 1 ;
    push(@predicates,"native") ;
  }
  else {
    push(@predicates,"byte") ;
  }

  while (@ARGV) {
    if ($ARGV[0] eq '-help') {
      shift @ARGV ;
      usage() ; exit ;
    }
    elsif ($ARGV[0] eq '-verbose') {
      $verbose = shift @ARGV ;
    }
    elsif ($ARGV[0] eq '-random-pid') {
      shift @ARGV ;
      $randompid = shift @ARGV ;
    }
    elsif ($ARGV[0] eq '-preserve') {
      shift @ARGV ;
      $preserve = 1 ;
    }
    elsif ($ARGV[0] eq '-n') {
      shift @ARGV ;
      $noexecute = 1 ;
    }
    elsif ($ARGV[0] eq '-package') {
      shift @ARGV ;
      push(@packages, split(/,/, shift @ARGV)) ;
    }
    elsif ($ARGV[0] eq '-predicates') {
      shift @ARGV ;
      push(@predicates, split(/,/, shift @ARGV)) ;
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
    my $txt ;
    if (($ocaml_version cmp "4.08.0") < 0) {
      my $crcs = capturex("$ocaml_lib/extract_crc", "-I", $ocaml_lib, @interfaces) ;
      print STDERR $crcs if $main::verbose ;
      $txt = <<"EOF";
$crcs
let _ = Dynlink.add_available_units crc_unit_list
EOF
    }
    else {
    $txt = <<"EOF";
Dynlink.set_allowed_units [
  $stringified
] ;;
EOF
    }
    push(@toremove, "link${randompid}.ml", "link${randompid}.cmi", "link${randompid}.cmo", "link${randompid}.cmx") ;
    f_write("link${randompid}.ml", $txt) ;
    push(@link, "link${randompid}.ml") ;
  }

  my @verbose ;
  @verbose = ( "-verbose" ) if $verbose ;
  v_systemx("ocamlfind",
	    ($opt ? "ocamlopt" : "ocamlc"),
	    "-predicates", join(',', @predicates),
	    "-package", join(',', @packages),
	    @verbose,
	    "-linkall", "-linkpkg",
	    @link, @options,
	    ($opt ? "odyl.cmx" : "odyl.cmo")
	   ) ;
}

sub v_systemx {
  my $codes ;
  $codes = shift if (ref($_[0]) eq 'ARRAY') ;
  my @cmd = @_ ;
  print STDERR join(' ', map { shell_quote($_) } @cmd)."\n" if ($main::verbose) ;
  return if $noexecute ;
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
