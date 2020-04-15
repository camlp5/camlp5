#!/usr/bin/env perl

use strict ;
use IPC::System::Simple qw(systemx runx capturex $EXITVAL);
use String::ShellQuote ;
use File::Basename;

our $verbose = 0 ;

{
  my $wd = dirname(dirname($0)) ;

  my $top = $ENV{'TOP'} || $wd;

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

  print STDERR join(' ', map { shell_quote($_) } @cmd)."\n" if $main::verbose ;

  return runx($codes, @cmd) ;
}

