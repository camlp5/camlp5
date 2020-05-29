# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

DIFF=diff -Bwi -u20
RM=rm

TESTS=official2official_test o2r_test r2r_test r2o_test o2o_test o2official_test r2official_test \
        r2sch_test q_MLast_test \
	sch2r_test.pa_scheme sch2r_test.pa_schemer \
	extfun_test o_top_test grammar_bug_test little_lang_test

all-tests: all $(TESTS)

all: roundtrippers \
	o2r_test.byte \
	r2r_test.byte \
	r2o_test.byte \
	o2o_test.byte \
	o2official_test.byte \
	r2official_test.byte \
	official2official_test.byte \
	r2sch_test.byte \
	q_MLast_test.byte \
	sch2r_test.pa_scheme.byte \
	sch2r_test.pa_schemer.byte \
	extfun_test.byte \
	roundtrip_lexer.byte \
	o_top_test.byte \
	tools/ROUNDTRIP-pa_r-pr_r.byte \
	tools/ROUNDTRIP-pa_r-pr_r.opt \
	tools/ROUNDTRIP-pa_o-pr_o.byte \
	tools/ROUNDTRIP-pa_o-pr_o.opt \
	grammar_bug_test \
	little_lang_test \

roundtrippers: \
	tools/ROUNDTRIP-pa_r-pr_r.byte \
	tools/ROUNDTRIP-pa_r-pr_r.opt \
	tools/ROUNDTRIP-pa_o-pr_o.byte \
	tools/ROUNDTRIP-pa_o-pr_o.opt \

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
OCAMLTOPLEVEL=$(LAUNCH) ocaml
CAMLP5LIB=$(shell $(OCAMLFIND) query camlp5)
MKCAMLP5=$(LAUNCH) mkcamlp5 -verbose
MKCAMLP5OPT=$(LAUNCH) mkcamlp5.opt -verbose
CAMLP5R=$(LAUNCH) camlp5r -I $(CAMLP5LIB)
INCLUDES=-I $(CAMLP5LIB)
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)
COMPILERLIBS= -I +compiler-libs ocamlcommon.cma ocamlbytecomp.cma ocamltoplevel.cma
PACKAGES_NOCAMLP5=rresult,fmt,pcre,ounit2,compiler-libs.common
PACKAGES=$(PACKAGES_NOCAMLP5),camlp5

pa_ounit2.cmo: pa_ounit2.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl pa_ounit2.ml

test.cmo: test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),camlp5.quotations -syntax camlp5r -warn-error A -c -i -impl test.ml

testutil.cmo: testutil.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl testutil.ml

testutil2.cmo: testutil2.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -c testutil2.ml

roundtrip_lexer.byte: roundtrip_lexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg roundtrip_lexer.ml -o roundtrip_lexer.byte

extfun_test:: extfun_test.byte
	./extfun_test.byte

extfun_test.byte: extfun_test.ml testutil.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo -impl extfun_test.ml -o extfun_test.byte

papr_test_matrix.cmo: papr_test_matrix.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl papr_test_matrix.ml

o2r_test:: o2r_test.byte
	./o2r_test.byte $(TESTARGS)

o2r_test.byte: o2r_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo o2r_test.ml -o o2r_test.byte

r2r_test:: r2r_test.byte
	./r2r_test.byte $(TESTARGS)

r2r_test.byte: r2r_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo r2r_test.ml -o r2r_test.byte


r2o_test:: r2o_test.byte
	./r2o_test.byte $(TESTARGS)

r2o_test.byte: r2o_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_o.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo r2o_test.ml -o r2o_test.byte


o2o_test:: o2o_test.byte
	./o2o_test.byte $(TESTARGS)

o2o_test.byte: o2o_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op.link,camlp5.pr_o.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo o2o_test.ml -o o2o_test.byte

o2official_test:: o2official_test.byte
	./o2official_test.byte $(TESTARGS)

o2official_test.byte: o2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op.link,camlp5.pr_official.link -syntax camlp5r -I ../etc -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo o2official_test.ml -o o2official_test.byte


r2official_test:: r2official_test.byte
	./r2official_test.byte $(TESTARGS)

r2official_test.byte: r2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_official.link -syntax camlp5r -I ../etc -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo r2official_test.ml -o r2official_test.byte



official2official_test:: official2official_test.byte
	./official2official_test.byte $(TESTARGS)

official2official_test.byte: official2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo official2official_test.ml -o official2official_test.byte

r2sch_test:: r2sch_test.byte
	./r2sch_test.byte

r2sch_test.byte: r2sch_test.ml testutil.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_scheme.link -syntax camlp5r -linkall -linkpkg testutil.cmo -impl r2sch_test.ml -o r2sch_test.byte

q_MLast_test:: q_MLast_test.byte
	./q_MLast_test.byte

q_MLast_test.byte: q_MLast_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_r.link,camlp5.quotations.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo -impl q_MLast_test.ml -o q_MLast_test.byte

grammar_bug_test:: grammar_bug_test.byte
	HAS_ARGLE=true ./grammar_bug_test.byte

grammar_bug_test.byte: grammar_bug_test.ml alt_pa_o.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -I ../main -linkall -linkpkg alt_pa_o.ml grammar_bug_test.ml -o grammar_bug_test.byte

little_lang_test:: little_lang_test.byte
	./little_lang_test.byte

little_lang_test.byte: little_lang_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -I ../main -linkall -linkpkg testutil.cmo testutil2.cmo little_lang_test.ml -o little_lang_test.byte

o_top_test:: o_top_test.byte
	./o_top_test.byte

o_top_test.byte: o_top_test.ml testutil.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_op.link,camlp5.pr_official.link -syntax camlp5r -linkall -linkpkg -I ../top -I ../etc ../top/camlp5_top_funs.cmo testutil.cmo testutil2.cmo -impl o_top_test.ml -o o_top_test.byte

sch2r_test.pa_scheme:: sch2r_test.pa_scheme.byte
	./sch2r_test.pa_scheme.byte

sch2r_test.pa_scheme.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),camlp5.pa_scheme.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo sch2r_test.ml -o sch2r_test.pa_scheme.byte

sch2r_test.pa_schemer:: sch2r_test.pa_schemer.byte
	./sch2r_test.pa_schemer.byte

sch2r_test.pa_schemer.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg pa_schemer.cmo testutil.cmo testutil2.cmo sch2r_test.ml -o sch2r_test.pa_schemer.byte

tools/ROUNDTRIP-pa_r-pr_r.byte:
	$(MKCAMLP5) -package camlp5.pa_r.link,camlp5.pr_r.link,camlp5.extend.link,camlp5.phony_quotations.link -o $@

tools/ROUNDTRIP-pa_r-pr_r.opt:
	$(MKCAMLP5OPT) -package camlp5.pa_r.link,camlp5.pr_r.link,camlp5.extend.link,camlp5.phony_quotations.link -o $@

tools/ROUNDTRIP-pa_o-pr_o.byte:
	$(MKCAMLP5) -package camlp5.pa_o.link,camlp5.pr_o.link -o $@

tools/ROUNDTRIP-pa_o-pr_o.opt:
	$(MKCAMLP5OPT) -package camlp5.pa_o.link,camlp5.pr_o.link -o $@

setup-ocaml:
	opam install -y rresult fmt pcre ounit2 bos

setup: setup-ocaml
	sudo apt-get install libstring-shellquote-perl libdigest-md5-file-perl

toplevel::
	$(OCAMLTOPLEVEL) -nopromptcont

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo tools/*.byte tools/*.opt

realclean: clean
