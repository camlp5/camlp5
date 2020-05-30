#!/usr/bin/env perl

while (<ARGV>) {

  $_ =~ s/Plexer.gmake\s*\(\s*\)\s*/Lazy.force P.lexer/ ;
  $_ =~ s/Grammar.Entry.of_parser\s+gram\s+"[^"]+"//;

  next if /^\s*EXTEND/../^\s*END/ ;
#  next if /Grammar.Entry.of_parser/;
  next if /Grammar.Entry.gcreate/;
  next if /Grammar.Entry.create/;
  next if /^\s*#load/ ;
  die "MUST preprocess away IFDEFs first" if /IFDEF/ ;
  next if /DELETE_RULE/ ;
  print ;
}
