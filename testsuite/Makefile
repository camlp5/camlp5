# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

ifeq ($(OS),Windows_NT)
BSDIR:=$(shell ocamlfind query camlp5-buildscripts)
#LAUNCH:=env TOP=$(TOP) $(BSDIR)/LAUNCH.PL -OCAMLPATH-pathsep ";" -vv
#LAUNCHPL:=env TOP=$(TOP) $(BSDIR)/LAUNCH.PL -vv
#LAUNCH:=env TOP=$(TOP) ../tools/LAUNCH.PL -vv
#LAUNCH:=env TOP=$(TOP) ocamlfind camlp5-buildscripts/LAUNCH$(EXE) -v --
endif
DIFF=diff -Bwi -u20
RM=rm

TESTS= $(MATRIXTESTS) \
	$(ANTIQUOTATIONTESTS) \
        r2sch_test.TEST sch2r_test.pa_scheme.TEST sch2r_test.pa_schemer.TEST \
	extfun_test.TEST reloc_test.TEST o_top_test2.TEST o_top_test.TEST r_top_test.TEST grammar_bug_test.TEST \
	little_lang_test.TEST o_lexer_test.TEST r_lexer_test.TEST quotedext_test.TEST

MATRIXTESTS=official2official_matrixtest.TEST o2official_matrixtest.TEST r2official_matrixtest.TEST o2r_matrixtest.TEST r2r_matrixtest.TEST r2o_matrixtest.TEST o2o_matrixtest.TEST

ANTIQUOTATIONTESTS= \
	q_MLast_antiquottest.TEST \
	revised_parser_antiquottest.TEST \
	official_parser_antiquottest.TEST \

export LC_ALL=C

all-tests:: all $(TESTS)
matrix-tests:: $(MATRIXTESTS)

antiquotation-tests:: $(ANTIQUOTATIONTESTS)

%.TEST: %.byte
	$(NOVERBOSE) mkdir -p _build
	./$< $(TESTARGS)

all: roundtrippers \
	roundtrip_lexer.byte \
	$(TESTS:.TEST=.byte)

matrix-test:: $(MATRIXTESTS)
	for t in $(MATRIXTESTS); do echo "==== $$t ====" ; ./$$t -only-test $(ONLYTEST) || true; done

roundtrippers: \
	tools/ROUNDTRIP-pa_r-pr_r.byte \
	tools/ROUNDTRIP-pa_r-pr_r.opt \
	tools/ROUNDTRIP-pa_o-pr_o.byte \
	tools/ROUNDTRIP-pa_o-pr_o.opt \

OCAMLFIND=$(LAUNCH) ocamlfind
OCAMLTOPLEVEL=$(LAUNCH) ocaml
CAMLP5LIB=$(shell $(OCAMLFIND) query camlp5)
MKCAMLP5=$(LAUNCH) mkcamlp5 -verbose
MKCAMLP5OPT=$(LAUNCH) mkcamlp5 -opt -verbose
CAMLP5R=$(LAUNCH) camlp5r -I $(CAMLP5LIB)
INCLUDES=-I $(CAMLP5LIB)
UNQUOTED_WARNERR := $(shell echo $(WARNERR))
OCAMLCFLAGS=$(DEBUG) $(UNQUOTED_WARNERR) $(INCLUDES)
COMPILERLIBS= -I +compiler-libs ocamlcommon.cma ocamlbytecomp.cma ocamltoplevel.cma
PACKAGES_NOCAMLP5=rresult,fmt,pcre2,ounit2,compiler-libs.common,$(C5PACKAGES)
PACKAGES=$(PACKAGES_NOCAMLP5),camlp5,camlp5.macro
YAWRAP=ocamlfind camlp5-buildscripts/ya-wrap-ocamlfind

OCAMLC=$(LAUNCH) $(YAWRAP) ocamlfind ocamlc
OCAMLDEP=$(LAUNCH) $(YAWRAP) ocamlfind ocamldep
OCAMLLINKC=$(LAUNCH) $(OCAMLFIND) ocamlc
#$(LAUNCH) $(YAWRAP) $(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) -package $(PACKAGES) -c $<

.ml.cmo:
	$(LAUNCH) $(YAWRAP) ocamlfind ocamlc $(DEBUG) $(OCAMLCFLAGS) -package $(PACKAGES) -warn-error A -warn-error -53 -c $<

%.byte: | %.ml
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers -linkall -linkpkg $+ -o $@

o2r_matrixtest.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo o2r_matrixtest.cmo
r2r_matrixtest.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo r2r_matrixtest.cmo
o2o_matrixtest.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo o2o_matrixtest.cmo
r2o_matrixtest.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo r2o_matrixtest.cmo
official2official_matrixtest.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo official2official_matrixtest.cmo
o2official_matrixtest.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo o2official_matrixtest.cmo
r2official_matrixtest.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo r2official_matrixtest.cmo
q_MLast_antiquottest.byte: testutil.cmo testutil2.cmo antiquotation_test.cmo q_MLast_antiquottest.cmo
revised_parser_antiquottest.byte: testutil.cmo testutil2.cmo antiquotation_test.cmo revised_parser_antiquottest.cmo
official_parser_antiquottest.byte: testutil.cmo testutil2.cmo antiquotation_test.cmo official_parser_antiquottest.cmo
extfun_test.byte: testutil.cmo extfun_test.cmo
reloc_test.byte: testutil.cmo reloc_test.cmo
little_lang_test.byte: testutil.cmo little_lang_test.cmo
o_lexer_test.byte: testutil.cmo o_lexer_test.cmo
r_lexer_test.byte: testutil.cmo r_lexer_test.cmo
grammar_bug_test.byte: alt_pa_o.cmo grammar_bug_test.cmo
quotedext_test.byte: testutil.cmo testutil2.cmo quotedext_test.cmo

r2sch_test.byte: testutil.cmo r2sch_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers,camlp5.pr_scheme.link -linkall -linkpkg testutil.cmo r2sch_test.cmo -o r2sch_test.byte

grammar_bug_test.TEST:: grammar_bug_test.byte
	$(NOVERBOSE) mkdir -p _build
	HAS_ARGLE=true ./grammar_bug_test.byte $(TESTARGS)

o_top_test.byte: testutil.cmo testutil2.cmo o_top_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_op.link,camlp5.pr_official.link,camlp5.toploop.link -linkall -linkpkg $^ -o o_top_test.byte

o_top_test2.byte: testutil.cmo testutil2.cmo o_top_test2.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_op.link,camlp5.pr_official.link,camlp5.toploop.link,camlp5.pr_o.link -linkall -linkpkg $^ -o o_top_test2.byte

r_top_test.byte: testutil.cmo testutil2.cmo r_top_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_r.link,camlp5.pr_official.link,camlp5.toploop.link -linkall -linkpkg $^ -o r_top_test.byte

sch2r_test.pa_scheme.byte: testutil.cmo testutil2.cmo sch2r_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.pa_scheme.link,camlp5.parsers,camlp5.printers -linkall -linkpkg $^ -o sch2r_test.pa_scheme.byte

sch2r_test.pa_schemer.byte: sch2r_test.cmo testutil.cmo testutil2.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.parsers,camlp5.printers -linkall -linkpkg pa_schemer.cmo testutil.cmo testutil2.cmo sch2r_test.cmo -o sch2r_test.pa_schemer.byte

tools/ROUNDTRIP-pa_r-pr_r.byte:
	$(MKCAMLP5) -package $(C5PACKAGES),camlp5.pa_r,camlp5.pr_r,camlp5.extend,camlp5.phony_quotations -o $@

tools/ROUNDTRIP-pa_r-pr_r.opt:
	$(MKCAMLP5OPT) -package $(C5PACKAGES),camlp5.pa_r,camlp5.pr_r,camlp5.extend,camlp5.phony_quotations -o $@

tools/ROUNDTRIP-pa_o-pr_o.byte:
	$(MKCAMLP5) -package $(C5PACKAGES),camlp5.pa_o,camlp5.pr_o -o $@

tools/ROUNDTRIP-pa_o-pr_o.opt:
	$(MKCAMLP5OPT) -package $(C5PACKAGES),camlp5.pa_o,camlp5.pr_o -o $@

setup-ocaml:
	opam install -y rresult fmt pcre2 ounit bos

setup: setup-ocaml
	sudo apt-get install libstring-shellquote-perl libdigest-md5-file-perl

toplevel::
	$(OCAMLTOPLEVEL) -nopromptcont

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo tools/*.byte tools/*.opt link*

realclean: clean

depend:
	cp .depend .depend.bak || true
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	echo $(OCAMLDEP) -package $(PACKAGES) $$i ; \
	$(OCAMLDEP) -package $(PACKAGES) $$i \
	  >> .depend; \
	done

-include .depend
