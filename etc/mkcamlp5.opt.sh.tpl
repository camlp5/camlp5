#!/bin/sh
# mkcamlp5.opt.sh.tpl,v

OLIB=`OCAMLNc -where`
LIB=LIBDIR/CAMLP5N

INTERFACES=
OPTS=
INCL="-I ."
while test "" != "$1"; do
    case $1 in
    -I) INCL="$INCL -I $2"; shift;;
    -help)
        echo "Usage: mkCAMLP5N.opt [options] [files]"
        echo "Options:"
        echo "  -I <dir>   Add directory in search patch for object files"
        echo
        echo "All options of OCAMLNopt are also available"
        echo
        echo "Files:"
        echo "  .cmx file  Load this file in core"
        echo "  .cmxa file Load this file in core"
        exit 0;;
    *) OPTS="$OPTS $1";;
    esac
    shift
done

set -e
OCAMLNopt -I $LIB odyl.cmxa CAMLP5N.cmxa $INCL $OPTS odyl.cmx -linkall
