#!/usr/bin/perl

use Data::Dumper ;
use Carp::Assert ;
use Getopt::Long;
use IPC::System::Simple qw(systemx runx capturex $EXITVAL);
use String::ShellQuote ;

our $verbose = 0 ;
our $syntax ;

our $ocamlformat = $ENV{'HOME'}."/Hack/Ocaml/GENERIC/4.09.0/bin/ocamlformat" ;

{
  GetOptions(
    "syntax=s" => \$syntax,
    "verbose" => \$verbose,
      )
      or die("Error in command line arguments\n");

  my $src = shift @ARGV ;
  my $dst = shift @ARGV ;
  if ($syntax eq 'revised') {
    my $txt = f_read($src) ;
    $txt =~ s|^#load.*$||gm ;
    $txt =~ s|\(\*.*?\*\)| onlynl($&) |gse ;
    $txt =~ s,→,->,gs ;
    $txt =~ s,declare end;,,gm ;
    $txt =~ s,;(?:\s*;)*,;,gs ;
    f_write($dst, $txt) ; 
  }
  else {
    my $tyflag = "--impl" ;
    $tyflag = "--intf" if ($src =~ m/\.mli/) ;

    my $txt = v_capturex("./roundtrip_lexer.byte",
			 "-mode","lexer-passthru",
			 "-strip-comments",
			 $src) ;
#    my $txt = f_read($src) ;
#    $txt =~ s|\(\*.*?\*\)| onlynl($&) |gse ;
    $txt =~ s,→,->,gs ;
    f_write($src.".2", $txt) ;

    my $txt = v_capturex($ocamlformat, 
			 "--enable-outside-detected-project", "--no-comment-check",
			 $tyflag, $src.".2") ;
    f_write($dst, $txt) ; 
  }
}

sub onlynl {
  my $s = shift ;
  $s =~ s,[^\n],,gs;
  return $s;
}

sub f_read {
  my $f = shift;
  open(F,"<$f") || die "cannot open $f for reading";
  my @l = <F>;
  close(F);
  return (wantarray ? @l : join('', @l)) ;
}

sub f_write {
  my $f = shift;
  open(F,">$f") || die "cannot open $f for writing";
  print F @_;
  close(F);
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

sub v_capturex {
  my $codes ;
  $codes = shift if (ref($_[0]) eq 'ARRAY') ;
  my @cmd = @_ ;
  print STDERR join(' ', map { shell_quote($_) } @cmd)."\n" if ($main::verbose) ;

  if ($codes) {
    return capturex($codes, @cmd) ;
  }
  else {
    return capturex(@cmd) ;
  }
}
