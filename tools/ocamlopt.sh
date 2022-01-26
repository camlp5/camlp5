#!/bin/sh -e

COMM=${OCAMLN}opt
echo ocamlfind $COMM -package camlp-streams,compiler-libs $*
ocamlfind $COMM -package camlp-streams,compiler-libs $*
