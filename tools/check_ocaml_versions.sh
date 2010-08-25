#!/bin/sh -e
# $Id: check_ocaml_versions.sh,v 1.8 2010/08/25 17:29:10 deraugla Exp $

TOP=$HOME/work
DEST=$TOP/usr
OCAMLSDIR=$TOP/ocaml/release
CAMLP5DIR=$TOP/camlp5
MODE=--strict

cd $DEST
PATH=$(pwd)/bin:$PATH

cd $OCAMLSDIR
dirs=$(ls | grep -v '^[1|2]' | grep -v '^3.0[0-6]' | grep -v csl)
echo =====================
echo $dirs
for i in $dirs; do
  echo =====================
  echo date: $(date) version: $i
  echo "+++++ cd $OCAMLSDIR/$i"
  cd $OCAMLSDIR/$i
  sed -e 's/ camlp4o[a-z]* / /g' Makefile | grep -v partial-install.sh |
  grep -v 'cd ocamldoc' | grep -v 'cd camlp4' > tmp; mv tmp Makefile
  touch config/Makefile
  echo "+++++ make clean"
  make clean
  echo "+++++ ./configure -bindir $TOP/usr/bin -libdir $TOP/usr/lib/ocaml -mandir $TOP/usr/man"
  ./configure -bindir $DEST/bin -libdir $DEST/lib/ocaml -mandir $DEST/man
  sed -e 's/ graph//' config/Makefile > tmp; mv tmp config/Makefile
  echo "+++++ make install"
  make install
  echo "+++++ make clean"
  make clean
  echo "+++++ cd $CAMLP5DIR"
  cd $CAMLP5DIR
  echo "+++++ make clean"
  make clean
  echo "+++++ ./configure $MODE"
  ./configure $MODE
  echo "+++++ time make world.opt"
  time make world.opt
  echo "+++++ make install"
  make install
  echo "+++++ make clean"
  make clean
done 2>&1

echo date: $(date) end
