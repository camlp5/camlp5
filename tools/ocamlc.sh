#!/bin/sh -e

COMM=${OCAMLN}c
echo ocamlfind $COMM -package camlp-streams,compiler-libs $*
ocamlfind $COMM -package camlp-streams,compiler-libs $*
