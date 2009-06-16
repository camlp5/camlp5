#!/bin/sh -e
dir=`dirname $OTOP`
if test "`basename $dir`" != "ocaml_stuff"; then
    COMM="$OTOP/boot/ocamlrun$EXE $OTOP/ocamlopt -I $OTOP/stdlib"
else
    COMM=ocamlopt$OPT
fi
echo $COMM $*
$COMM $*
