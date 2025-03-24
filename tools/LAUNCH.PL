#!/usr/bin/env perl

use strict ;
use IPC::System::Simple qw(systemx runx capturex $EXITVAL);
use String::ShellQuote ;
use File::Basename;

our $verbose = 0 ;

while(@ARGV) {
  if ($ARGV[0] eq '-v') {
    shift @ARGV ;
    $verbose = 1 ;
  }
  elsif ($ARGV[0] eq '-vv') {
    shift @ARGV ;
    $verbose = 2 ;
  }
  else { last ; }
}

{
  my $wd = dirname(dirname($0)) ;

  my $top = $ENV{'TOP'} || die "environment variable TOP MUST be set" ;

  my $searchpathsep;
  print STDERR "OS: <<$^O>>\n" if $main::verbose > 1;
  if ($^O eq 'MSWin32' || $^O eq 'cygwin') {
    $searchpathsep = ";";
  }
  else {
    $searchpathsep = ":";
  }

  my %newenv ;
  $newenv{'PATH'} = "$top/local-install/bin:$ENV{'PATH'}" ;
  $newenv{'OCAMLPATH'} = "$top/local-install/lib:" ;

  local %ENV = (%ENV, %newenv) ;

  v_systemx([0], [@ARGV]) ;
}

sub v_systemx {
  croak( "v_systemx: must specify exit codes") unless (ref($_[0]) eq 'ARRAY') ;
  my $codes = shift ;
  my @cmd = @{ shift @_ } ;
  my %args = @_ ;

  print STDERR ("PATH=".shell_quote($ENV{'PATH'})." OCAMLPATH=".shell_quote($ENV{'OCAMLPATH'})."\n") if $main::verbose > 1;
  print STDERR join(' ', map { shell_quote($_) } @cmd)."\n" if $main::verbose > 0;

  return runx($codes, @cmd) ;
}

