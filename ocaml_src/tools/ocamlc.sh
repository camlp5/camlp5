#!/bin/bash -e

COMM=${OCAMLN}c

echo ocamlfind $COMM -package $C5PACKAGES $*
ocamlfind $COMM -package $C5PACKAGES $*
