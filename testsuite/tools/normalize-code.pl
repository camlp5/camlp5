#!/usr/bin/perl

{
  my $src = shift @ARGV ;
  my $dst = shift @ARGV ;
  my $txt = f_read($src) ;
  $txt =~ s|\(\*.*?\*\)| onlynl($&) |gse ;
  $txt =~ s,→,->,gs ;
  $txt =~ s,declare end;,,gm ;
  $txt =~ s,;(?:\s*;)*,;,gs ;
  f_write($dst, $txt) ; 
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
