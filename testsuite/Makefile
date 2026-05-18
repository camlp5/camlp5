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

TESTS=official2official_test o2r_test o2o_test o2official_test r2r_test r2o_test r2official_test \
        r2sch_test q_MLast_test revised_parser_test official_parser_test \
	sch2r_test.pa_scheme sch2r_test.pa_schemer \
	extfun_test reloc_test o_top_test2 o_top_test r_top_test grammar_bug_test \
	little_lang_test o_lexer_test r_lexer_test quotedext_test

MATRIXTESTS=official2official_test.byte o2official_test.byte r2official_test.byte o2r_test.byte r2r_test.byte r2o_test.byte o2o_test.byte

ANTIQUOTATIONTESTS= \
	q_MLast_test.byte \
	revised_parser_test.byte \
	official_parser_test.byte \

export LC_ALL=C

all-tests:: all $(TESTS)
matrix-tests:: $(MATRIXTESTS)
	for t in $(MATRIXTESTS); do echo "==== $$t ====" ; ./$$t || true; done

antiquotation-tests:: $(ANTIQUOTATIONTESTS)
	for t in $(ANTIQUOTATIONTESTS); do echo "==== $$t ====" ; ./$$t || true; done

all: roundtrippers \
	o2r_test.byte \
	r2r_test.byte \
	r2o_test.byte \
	o2o_test.byte \
	official2official_test.byte \
	o2official_test.byte \
	r2official_test.byte \
	r2sch_test.byte \
	q_MLast_test.byte \
	revised_parser_test.byte \
	official_parser_test.byte \
	sch2r_test.pa_scheme.byte \
	sch2r_test.pa_schemer.byte \
	extfun_test.byte \
	reloc_test.byte \
	roundtrip_lexer.byte \
	o_top_test.byte \
	o_top_test2.byte \
	r_top_test.byte \
	tools/ROUNDTRIP-pa_r-pr_r.byte \
	tools/ROUNDTRIP-pa_r-pr_r.opt \
	tools/ROUNDTRIP-pa_o-pr_o.byte \
	tools/ROUNDTRIP-pa_o-pr_o.opt \
	grammar_bug_test \
	little_lang_test \
	o_lexer_test \
	r_lexer_test \
	quotedext_test \

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

roundtrip_lexer.byte: roundtrip_lexer.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg $^ -o roundtrip_lexer.byte

extfun_test:: extfun_test.byte
	./extfun_test.byte

extfun_test.byte: testutil.cmo extfun_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.extfun,camlp5.quotations,camlp5.parsers,camlp5.printers -syntax camlp5r -linkall -linkpkg $^ -o extfun_test.byte

reloc_test:: reloc_test.byte
	./reloc_test.byte

reloc_test.byte: testutil.cmo reloc_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers -syntax camlp5r -linkall -linkpkg $^ -o reloc_test.byte

o2r_test:: o2r_test.byte
	$(NOVERBOSE) mkdir -p _build
	./o2r_test.byte $(TESTARGS)

o2r_test.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo o2r_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers -syntax camlp5r -linkall -linkpkg $^ -o o2r_test.byte

r2r_test:: r2r_test.byte
	$(NOVERBOSE) mkdir -p _build
	./r2r_test.byte $(TESTARGS)

r2r_test.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo r2r_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers -syntax camlp5r -linkall -linkpkg $^ -o r2r_test.byte


r2o_test:: r2o_test.byte
	$(NOVERBOSE) mkdir -p _build
	./r2o_test.byte $(TESTARGS)

r2o_test.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo r2o_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers -syntax camlp5r -linkall -linkpkg $^ -o r2o_test.byte


o2o_test:: o2o_test.byte
	$(NOVERBOSE) mkdir -p _build
	./o2o_test.byte $(TESTARGS)

o2o_test.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo o2o_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers -syntax camlp5r -linkall -linkpkg $^ -o o2o_test.byte

o2official_test:: o2official_test.byte
	$(NOVERBOSE) mkdir -p _build
	./o2official_test.byte $(TESTARGS)

o2official_test.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo o2official_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers,camlp5.pr_official.link -syntax camlp5r -linkall -linkpkg -I ../etc $^ -o o2official_test.byte


r2official_test:: r2official_test.byte
	$(NOVERBOSE) mkdir -p _build
	./r2official_test.byte $(TESTARGS)

r2official_test.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo r2official_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers,camlp5.pr_official.link -syntax camlp5r -linkall -linkpkg -I ../etc $^ -o r2official_test.byte



official2official_test:: official2official_test.byte
	$(NOVERBOSE) mkdir -p _build
	./official2official_test.byte $(TESTARGS)

official2official_test.byte: testutil.cmo testutil2.cmo papr_test_matrix.cmo official2official_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg $^ -o official2official_test.byte

r2sch_test:: r2sch_test.byte
	./r2sch_test.byte

r2sch_test.byte: r2sch_test.cmo testutil.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.parsers,camlp5.printers,camlp5.pr_scheme.link -syntax camlp5r -linkall -linkpkg testutil.cmo r2sch_test.cmo -o r2sch_test.byte

q_MLast_test:: q_MLast_test.byte
	./q_MLast_test.byte

q_MLast_test.byte: testutil.cmo testutil2.cmo antiquotation_test.cmo q_MLast_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.printers,camlp5.quotations.link -syntax camlp5r -linkall -linkpkg $^ -o q_MLast_test.byte

revised_parser_test:: revised_parser_test.byte
	./revised_parser_test.byte

revised_parser_test.byte: testutil.cmo testutil2.cmo antiquotation_test.cmo revised_parser_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.printers,camlp5.parser_quotations.link -syntax camlp5r -linkall -linkpkg $^ -o revised_parser_test.byte

official_parser_test:: official_parser_test.byte
	./official_parser_test.byte

official_parser_test.byte: testutil.cmo testutil2.cmo antiquotation_test.cmo official_parser_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.pa_o.link,camlp5.printers,camlp5.parser_quotations.link -syntax camlp5r -linkall -linkpkg $^ -o official_parser_test.byte

grammar_bug_test:: grammar_bug_test.byte
	$(NOVERBOSE) mkdir -p _build
	HAS_ARGLE=true ./grammar_bug_test.byte $(TESTARGS)

grammar_bug_test.byte: grammar_bug_test.cmo alt_pa_o.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.quotations,camlp5.macro_gram -syntax camlp5r -I ../main -linkall -linkpkg alt_pa_o.cmo grammar_bug_test.cmo -o grammar_bug_test.byte

little_lang_test:: little_lang_test.byte
	$(NOVERBOSE) mkdir -p _build
	./little_lang_test.byte $(TESTARGS)

little_lang_test.byte: little_lang_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf -syntax camlp5r -I ../main -linkall -linkpkg testutil.cmo testutil2.cmo little_lang_test.cmo -o little_lang_test.byte

o_lexer_test:: o_lexer_test.byte
	$(NOVERBOSE) mkdir -p _build
	./o_lexer_test.byte $(TESTARGS)

o_lexer_test.byte: testutil.cmo testutil2.cmo o_lexer_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf,camlp5.pa_o.link,camlp5.quotations -syntax camlp5r -I ../main -linkall -linkpkg $^ -o o_lexer_test.byte

quotedext_test:: quotedext_test.byte
	$(NOVERBOSE) mkdir -p _build
	./quotedext_test.byte $(TESTARGS)

quotedext_test.byte: testutil.cmo testutil2.cmo quotedext_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf,camlp5.pa_o.link,camlp5.quotations -syntax camlp5r -I ../main -linkall -linkpkg $^ -o quotedext_test.byte

r_lexer_test:: r_lexer_test.byte
	$(NOVERBOSE) mkdir -p _build
	./r_lexer_test.byte $(TESTARGS)

r_lexer_test.byte: testutil.cmo testutil2.cmo r_lexer_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf,camlp5.pa_r.link,camlp5.quotations -syntax camlp5r -I ../main -linkall -linkpkg $^ -o r_lexer_test.byte

o_top_test:: o_top_test.byte
	./o_top_test.byte

o_top_test.byte: testutil.cmo testutil2.cmo o_top_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_op.link,camlp5.pr_official.link,camlp5.toploop.link -syntax camlp5r -linkall -linkpkg $^ -o o_top_test.byte

o_top_test2:: o_top_test2.byte
	./o_top_test2.byte

o_top_test2.byte: testutil.cmo testutil2.cmo o_top_test2.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_op.link,camlp5.pr_official.link,camlp5.toploop.link,camlp5.pr_o.link -I ../etc -syntax camlp5r -linkall -linkpkg $^ -o o_top_test2.byte

r_top_test:: r_top_test.byte
	./r_top_test.byte

r_top_test.byte: testutil.cmo testutil2.cmo r_top_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_r.link,camlp5.pr_official.link,camlp5.toploop.link -syntax camlp5r -linkall -linkpkg $^ -o r_top_test.byte

sch2r_test.pa_scheme:: sch2r_test.pa_scheme.byte
	./sch2r_test.pa_scheme.byte

sch2r_test.pa_scheme.byte: testutil.cmo testutil2.cmo sch2r_test.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.pa_scheme.link,camlp5.parsers,camlp5.printers -syntax camlp5r -linkall -linkpkg $^ -o sch2r_test.pa_scheme.byte

sch2r_test.pa_schemer:: sch2r_test.pa_schemer.byte
	./sch2r_test.pa_schemer.byte

sch2r_test.pa_schemer.byte: sch2r_test.cmo testutil.cmo testutil2.cmo
	$(OCAMLLINKC) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.parsers,camlp5.printers -syntax camlp5r -linkall -linkpkg pa_schemer.cmo testutil.cmo testutil2.cmo sch2r_test.cmo -o sch2r_test.pa_schemer.byte

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
