#!/bin/bash

N=$1
echo $N | perl -p -e 's,\+.*$,, ; s,\.,_,g; $_ = "OCAML_".$_'
