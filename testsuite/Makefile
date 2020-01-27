# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

DIFF=diff -Bwi -u20
RM=rm

all: o2r_test.byte r2sch_test.byte sch2r_test.pa_scheme.byte sch2r_test.pa_schemer.byte
	./o2r_test.byte
	./r2sch_test.byte
	./sch2r_test.pa_scheme.byte
	./sch2r_test.pa_schemer.byte

INCLUDES=-I ../main -I ../lib -I ../meta -I ../etc -I ../top -I ../odyl
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)
COMPILERLIBS= -I +compiler-libs ocamlcommon.cma ocamlbytecomp.cma ocamltoplevel.cma
PACKAGES=rresult,fmt,pcre,ounit2

testutil.cmo: testutil.ml

testutil2.cmo: testutil2.ml
	ocamlfind ocamlc $(DEBUG) -package $(PACKAGES) -c testutil2.ml

o2r_test.byte: o2r_test.ml testutil.cmo
	ocamlfind ocamlc $(DEBUG) -package ounit2 -linkall -linkpkg $(COMPILERLIBS) -I ../main ../odyl/odyl.cma ../main/camlp5.cma ../etc/pa_o.cmo ../etc/pr_r.cmo testutil.cmo o2r_test.ml -o o2r_test.byte

r2sch_test.byte: r2sch_test.ml testutil.cmo
	ocamlfind ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg $(COMPILERLIBS) -I ../main ../odyl/odyl.cma ../main/camlp5.cma ../meta/pa_r.cmo ../etc/pr_scheme.cmo testutil.cmo r2sch_test.ml -o r2sch_test.byte

sch2r_test.pa_scheme.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	ocamlfind ocamlc $(DEBUG) -package $(PACKAGES) -I ../main -I ../lib -I ../etc -c sch2r_test.ml
	ocamlfind ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -I ../main -I ../lib -I ../etc ../odyl/odyl.cma ../main/camlp5.cma ../etc/pa_scheme.cmo ../etc/pr_r.cmo testutil.cmo testutil2.cmo sch2r_test.cmo -o sch2r_test.pa_scheme.byte

sch2r_test.pa_schemer.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	ocamlfind ocamlc $(DEBUG) -package $(PACKAGES) -I ../main -I ../lib -I ../etc -c sch2r_test.ml
	ocamlfind ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -I ../main -I ../lib -I ../etc ../odyl/odyl.cma ../main/camlp5.cma ../etc/pa_schemer.cmo ../etc/pr_r.cmo testutil.cmo testutil2.cmo sch2r_test.cmo -o sch2r_test.pa_schemer.byte

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo
