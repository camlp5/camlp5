# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

DIFF=diff -Bwi -u20
RM=rm

TESTS=official2official_test o2r_test o2o_test o2official_test r2r_test r2o_test r2official_test \
        r2sch_test q_MLast_test q_ast_test \
	sch2r_test.pa_scheme sch2r_test.pa_schemer \
	extfun_test reloc_test o_top_test r_top_test grammar_bug_test \
	little_lang_test o_lexer_test r_lexer_test

export LC_ALL=C

all-tests: all $(TESTS)

all: prereqs roundtrippers \
	o2r_test.byte \
	r2r_test.byte \
	r2o_test.byte \
	o2o_test.byte \
	o2official_test.byte \
	r2official_test.byte \
	official2official_test.byte \
	r2sch_test.byte \
	q_MLast_test.byte \
	q_ast_test.byte \
	sch2r_test.pa_scheme.byte \
	sch2r_test.pa_schemer.byte \
	extfun_test.byte \
	reloc_test.byte \
	roundtrip_lexer.byte \
	o_top_test.byte \
	r_top_test.byte \
	tools/ROUNDTRIP-pa_r-pr_r.byte \
	tools/ROUNDTRIP-pa_r-pr_r.opt \
	tools/ROUNDTRIP-pa_o-pr_o.byte \
	tools/ROUNDTRIP-pa_o-pr_o.opt \
	grammar_bug_test \
	little_lang_test \
	o_lexer_test \
	r_lexer_test \

prereqs:
	(perl -MIPC::System::Simple -e 1 > /dev/null 2>&1) || (echo "MUST install Perl module IPC::System::Simple" && exit -1)
	(perl -MString::ShellQuote -e 1 > /dev/null 2>&1) || (echo "MUST install Perl module String::ShellQuote" && exit -1)

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
PACKAGES_NOCAMLP5=rresult,fmt,pcre,ounit2,compiler-libs.common,$(C5PACKAGES)
PACKAGES=$(PACKAGES_NOCAMLP5),camlp5,camlp5.macro

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
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.extfun,camlp5.quotations,camlp5.pa_r.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo -impl extfun_test.ml -o extfun_test.byte

reloc_test:: reloc_test.byte
	./reloc_test.byte

reloc_test.byte: reloc_test.ml testutil.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo -impl reloc_test.ml -o reloc_test.byte

papr_test_matrix.cmo: papr_test_matrix.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl papr_test_matrix.ml

o2r_test:: o2r_test.byte
	$(NOVERBOSE) mkdir -p _build
	./o2r_test.byte $(TESTARGS)

o2r_test.byte: o2r_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo o2r_test.ml -o o2r_test.byte

r2r_test:: r2r_test.byte
	$(NOVERBOSE) mkdir -p _build
	./r2r_test.byte $(TESTARGS)

r2r_test.byte: r2r_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo r2r_test.ml -o r2r_test.byte


r2o_test:: r2o_test.byte
	$(NOVERBOSE) mkdir -p _build
	./r2o_test.byte $(TESTARGS)

r2o_test.byte: r2o_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_o.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo r2o_test.ml -o r2o_test.byte


o2o_test:: o2o_test.byte
	$(NOVERBOSE) mkdir -p _build
	./o2o_test.byte $(TESTARGS)

o2o_test.byte: o2o_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op.link,camlp5.pr_o.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo o2o_test.ml -o o2o_test.byte

o2official_test:: o2official_test.byte
	$(NOVERBOSE) mkdir -p _build
	./o2official_test.byte $(TESTARGS)

o2official_test.byte: o2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op.link,camlp5.pr_official.link -syntax camlp5r -linkall -linkpkg -I ../etc testutil.cmo testutil2.cmo papr_test_matrix.cmo o2official_test.ml -o o2official_test.byte


r2official_test:: r2official_test.byte
	$(NOVERBOSE) mkdir -p _build
	./r2official_test.byte $(TESTARGS)

r2official_test.byte: r2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_official.link -syntax camlp5r -linkall -linkpkg -I ../etc testutil.cmo testutil2.cmo papr_test_matrix.cmo r2official_test.ml -o r2official_test.byte



official2official_test:: official2official_test.byte
	$(NOVERBOSE) mkdir -p _build
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

q_ast_test:: q_ast_test.byte
	./q_ast_test.byte

q_ast_test.byte: q_MLast_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r.link,camlp5.pr_r.link,camlp5.parser_quotations.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo -impl q_MLast_test.ml -o q_ast_test.byte


grammar_bug_test:: grammar_bug_test.byte
	$(NOVERBOSE) mkdir -p _build
	HAS_ARGLE=true ./grammar_bug_test.byte $(TESTARGS)

grammar_bug_test.byte: grammar_bug_test.ml alt_pa_o.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.quotations,camlp5.macro_gram -syntax camlp5r -I ../main -linkall -linkpkg alt_pa_o.ml grammar_bug_test.ml -o grammar_bug_test.byte

little_lang_test:: little_lang_test.byte
	$(NOVERBOSE) mkdir -p _build
	./little_lang_test.byte $(TESTARGS)

little_lang_test.byte: little_lang_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf -syntax camlp5r -I ../main -linkall -linkpkg testutil.cmo testutil2.cmo little_lang_test.ml -o little_lang_test.byte

o_lexer_test:: o_lexer_test.byte
	$(NOVERBOSE) mkdir -p _build
	./o_lexer_test.byte $(TESTARGS)

o_lexer_test.byte: o_lexer_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf,camlp5.pa_o.link,camlp5.quotations -syntax camlp5r -I ../main -linkall -linkpkg testutil.cmo testutil2.cmo o_lexer_test.ml -o o_lexer_test.byte

r_lexer_test:: r_lexer_test.byte
	$(NOVERBOSE) mkdir -p _build
	./r_lexer_test.byte $(TESTARGS)

r_lexer_test.byte: r_lexer_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf,camlp5.pa_r.link,camlp5.quotations -syntax camlp5r -I ../main -linkall -linkpkg testutil.cmo testutil2.cmo r_lexer_test.ml -o r_lexer_test.byte

o_top_test:: o_top_test.byte
	./o_top_test.byte

o_top_test.byte: o_top_test.ml testutil.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_op.link,camlp5.pr_official.link,camlp5.toploop.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo -impl o_top_test.ml -o o_top_test.byte

r_top_test:: r_top_test.byte
	./r_top_test.byte

r_top_test.byte: r_top_test.ml testutil.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_r.link,camlp5.pr_official.link,camlp5.toploop.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo -impl r_top_test.ml -o r_top_test.byte

sch2r_test.pa_scheme:: sch2r_test.pa_scheme.byte
	./sch2r_test.pa_scheme.byte

sch2r_test.pa_scheme.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),camlp5.pa_scheme.link,camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo sch2r_test.ml -o sch2r_test.pa_scheme.byte

sch2r_test.pa_schemer:: sch2r_test.pa_schemer.byte
	./sch2r_test.pa_schemer.byte

sch2r_test.pa_schemer.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),camlp5.pr_r.link -syntax camlp5r -linkall -linkpkg pa_schemer.cmo testutil.cmo testutil2.cmo sch2r_test.ml -o sch2r_test.pa_schemer.byte

tools/ROUNDTRIP-pa_r-pr_r.byte:
	$(MKCAMLP5) -verbose -package $(C5PACKAGES),camlp5.pa_r,camlp5.pr_r,camlp5.extend,camlp5.phony_quotations -o $@

tools/ROUNDTRIP-pa_r-pr_r.opt:
	$(MKCAMLP5OPT) -verbose -package $(C5PACKAGES),camlp5.pa_r,camlp5.pr_r,camlp5.extend,camlp5.phony_quotations -o $@

tools/ROUNDTRIP-pa_o-pr_o.byte:
	$(MKCAMLP5) -verbose -package $(C5PACKAGES),camlp5.pa_o,camlp5.pr_o -o $@

tools/ROUNDTRIP-pa_o-pr_o.opt:
	$(MKCAMLP5OPT) -verbose -package $(C5PACKAGES),camlp5.pa_o,camlp5.pr_o -o $@

setup-ocaml:
	opam install -y rresult fmt pcre ounit bos

setup: setup-ocaml
	sudo apt-get install libstring-shellquote-perl libdigest-md5-file-perl

toplevel::
	$(OCAMLTOPLEVEL) -nopromptcont

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo tools/*.byte tools/*.opt

realclean: clean
