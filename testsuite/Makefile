# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

DIFF=diff -Bwi -u20
RM=rm

all: o2r_test.byte r2sch_test.byte sch2r_test.pa_scheme.byte sch2r_test.pa_schemer.byte extfun_test.byte
	./o2r_test.byte
	./r2sch_test.byte
	./sch2r_test.pa_scheme.byte
	./sch2r_test.pa_schemer.byte
	./extfun_test.byte

OCAMLFIND=PATH=$(TOP)/local-install/bin:$(PATH) OCAMLPATH=$(TOP)/local-install/lib: ocamlfind
CAMLP5LIB=$(shell $(OCAMLFIND) query camlp5)
CAMLP5R=$(TOP)/local-install/bin/camlp5r -I $(CAMLP5LIB)
INCLUDES=-I $(CAMLP5LIB)
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)
COMPILERLIBS= -I +compiler-libs ocamlcommon.cma ocamlbytecomp.cma ocamltoplevel.cma
PACKAGES=rresult,fmt,pcre,ounit2,compiler-libs.common,camlp5

pa_ounit2.cmo: pa_ounit2.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl pa_ounit2.ml

testutil.cmo: testutil.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl testutil.ml

testutil2.cmo: testutil2.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -c testutil2.ml

extfun_test.byte: extfun_test.ml testutil.cmo pa_ounit2.cmo
	$(CAMLP5R) -I . pa_ounit2.cmo -mode S -o extfun_test.ppo extfun_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -linkall -linkpkg odyl.cma camlp5.cma pa_o.cmo pr_r.cmo testutil.cmo -impl extfun_test.ppo -o extfun_test.byte

o2r_test.byte: o2r_test.ml testutil.cmo pa_ounit2.cmo
	$(CAMLP5R) -I . pa_ounit2.cmo -mode S -o o2r_test.ppo o2r_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -linkall -linkpkg odyl.cma camlp5.cma pa_o.cmo pr_r.cmo testutil.cmo -impl o2r_test.ppo -o o2r_test.byte

r2sch_test.byte: r2sch_test.ml testutil.cmo pa_ounit2.cmo
	$(CAMLP5R) -I . pa_ounit2.cmo -mode S -o r2sch_test.ppo r2sch_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg odyl.cma camlp5.cma pa_r.cmo pr_scheme.cmo testutil.cmo -impl r2sch_test.ppo -o r2sch_test.byte

sch2r_test.cmo: sch2r_test.ml testutil.cmo testutil2.cmo pa_ounit2.cmo
	$(CAMLP5R) -I . pa_ounit2.cmo -mode S -o sch2r_test.ppo sch2r_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -c -impl sch2r_test.ppo

sch2r_test.pa_scheme.byte: sch2r_test.cmo testutil.cmo testutil2.cmo pa_ounit2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg odyl.cma camlp5.cma pa_scheme.cmo pr_r.cmo testutil.cmo testutil2.cmo sch2r_test.cmo -o sch2r_test.pa_scheme.byte

sch2r_test.pa_schemer.byte: sch2r_test.cmo testutil.cmo testutil2.cmo pa_ounit2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg odyl.cma camlp5.cma ../etc/pa_schemer.cmo pr_r.cmo testutil.cmo testutil2.cmo sch2r_test.cmo -o sch2r_test.pa_schemer.byte

setup:
	opam install rresult fmt pcre ounit2

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo
