#!/bin/sh -e
# $Id: check_ocaml_versions.sh,v 1.1 2010/08/20 10:06:00 deraugla Exp $

TOP=$HOME/work
OCAMLSDIR=$TOP/ocaml/release
CAMLP5DIR=$TOP/camlp5
MODE=--strict

cd $TOP
PATH=$(pwd)/usr/bin:$PATH

cd ocaml/release
dirs=$(ls | grep -v '^[1|2]' | grep -v '^3.0[0-7]' | grep -v csl)
dirs=$(ls | grep -v '^[1|2]' | grep -v '^3.0[0-5]' | grep -v csl)
echo =====================
echo $dirs
for i in $dirs; do
  echo =====================
  echo date: $(date) version: $i
  echo "+++++ cd $OCAMLSDIR/$i"
  cd $OCAMLSDIR/$i
  sed -e 's/ camlp4o[a-z]* / /g' Makefile | grep -v partial-install.sh |
  grep -v 'cd ocamldoc' > tmp; mv tmp Makefile
#  echo all clean install opt opt.opt: > camlp4/Makefile
#  echo all clean install installopt opt.opt: > ocamldoc/Makefile
#  echo all allopt clean install installopt partialclean: > otherlibs/graph/Makefile
  touch config/Makefile
  echo "+++++ make clean"
  make clean
  echo "+++++ ./configure -bindir $TOP/usr/bin -libdir $TOP/usr/lib/ocaml -mandir $TOP/usr/man"
  ./configure -bindir $TOP/usr/bin -libdir $TOP/usr/lib/ocaml -mandir $TOP/usr/man
  sed -e 's/ graph//' config/Makefile > tmp; mv tmp config/Makefile
  echo "+++++ time make world.opt"
  time make world.opt
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
