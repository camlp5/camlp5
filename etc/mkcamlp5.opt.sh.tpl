#!/bin/sh
# $Id: mkcamlp5.opt.sh.tpl,v 1.2 2007/11/20 08:55:44 deraugla Exp $

OLIB=`ocamlc -where`
LIB=LIBDIR/camlp5

INTERFACES=
OPTS=
INCL="-I ."
while test "" != "$1"; do
    case $1 in
    -I) INCL="$INCL -I $2"; shift;;
    -help)
        echo "Usage: mkcamlp5.opt [options] [files]"
        echo "Options:"
        echo "  -I <dir>   Add directory in search patch for object files"
        echo
        echo "All options of ocamlopt are also available"
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
ocamlopt -I $LIB odyl.cmxa camlp5.cmxa $INCL $OPTS odyl.cmx -linkall
