#!/bin/sh -e
dir=`dirname $OTOP`
if test "`basename $dir`" != "ocaml_stuff"; then
    COMM="$OTOP/boot/ocamlrun$EXE $OTOP/ocamlc -I $OTOP/stdlib"
else
    COMM=ocamlc$OPT
fi
echo $COMM $*
$COMM $*
