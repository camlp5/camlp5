#!/bin/sh -e
# $Id: check_ocaml_versions.sh,v 1.26 2010/08/29 05:23:19 deraugla Exp $

TOP=$HOME/work
DEST=$TOP/usr
OCAMLSDIR=$TOP/ocaml/release
CAMLP5DIR=$TOP/camlp5
MODE=--strict
DOOPT=1

cd $DEST
PATH=$(pwd)/bin:$PATH

cd $OCAMLSDIR

dirs=$(ls | grep -v '^[1|2]' | grep -v '^3.00' | grep -v csl)
dirs="3.01"
# dirs="3.02 3.03-alpha 3.04 3.05 3.06 3.07 3.08.4 3.09.3 3.10.2 3.11.2 3.12.0"

# WARNING: on 64 bits arch, rather use this:
# dirs=$(ls | grep -v '^[1|2]' | grep -v '^3.0[0-6]' | grep -v csl)

echo =====================
echo $dirs
for i in $dirs; do
  echo =====================
  echo date: $(date) version: $i
  echo "+++++ cd $OCAMLSDIR/$i"
  cd $OCAMLSDIR/$i
  sed -e 's/ camlp4o[a-z]* / /g' Makefile | grep -v partial-install.sh |
  grep -v 'cd ocamldoc' | grep -v 'cd camlp4' |
  sed -e 's/ ocamlbuild.byte / /g' |  sed -e 's/ ocamlbuild.native / /g' |
  grep -v '$(MAKE) ocamlbuildlib.native'  > tmp
  mv tmp Makefile
  touch config/Makefile
  echo "+++++ make clean"
  make clean
  echo "+++++ ./configure -bindir $TOP/usr/bin -libdir $TOP/usr/lib/ocaml -mandir $TOP/usr/man"
  ./configure -bindir $DEST/bin -libdir $DEST/lib/ocaml -mandir $DEST/man
  sed -e 's/ graph//' config/Makefile > tmp; mv tmp config/Makefile
  if [ "$DOOPT" = "0" ]; then
    echo "+++++ time make world"
    time make world
  elif [ "$i" = "3.01" -o "$i" = "3.02" -o "$i" = "3.03-alpha" -o \
         "$i" = "3.04" ]
  then
    echo "+++++ time make world opt opt.opt"
    time make world opt opt.opt
  else
    echo "+++++ time make world.opt"
    time make world.opt
  fi
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
  if [ "$DOOPT" = "0" ]; then
    echo "+++++ time make world"
    time make world
  else
    echo "+++++ time make world.opt"
    time make world.opt
  fi
  echo "+++++ make install"
  make install
  echo "+++++ make clean"
  make clean
done 2>&1

echo date: $(date) end
