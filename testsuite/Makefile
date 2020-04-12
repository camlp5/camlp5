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

work:: q_MLast_test

all: \
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
	papr_official.byte \
	o_top_test.byte \
	tools/ROUNDTRIP-pa_r-pr_r.byte \
	tools/ROUNDTRIP-pa_r-pr_r.opt \
	tools/ROUNDTRIP-pa_o-pr_o.byte \
	tools/ROUNDTRIP-pa_o-pr_o.opt \
	grammar_bug_test \
	little_lang_test \


OCAMLFIND=tools/LAUNCH ocamlfind
OCAMLTOPLEVEL=tools/LAUNCH ocaml
CAMLP5LIB=$(shell $(OCAMLFIND) query camlp5)
MKCAMLP5=tools/LAUNCH mkcamlp5
CAMLP5R=tools/lAUNCH camlp5r -I $(CAMLP5LIB)
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

papr_official.cmo: papr_official.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES_NOCAMLP5) -warn-error A -c -o papr_official.cmo -impl papr_official.ppo.ml

.PRECIOUS: papr_official.ppo.ml

papr_official.ppo.ml: papr_official.ml
	$(CAMLP5R) pr_o.cmo -I . -mode S -o papr_official.ppo.ml papr_official.ml

papr_official.byte: papr_official.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES_NOCAMLP5),ounit2 -linkall -linkpkg papr_official.cmo -o papr_official.byte

extfun_test:: extfun_test.byte
	./extfun_test.byte

extfun_test.byte: extfun_test.ml testutil.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r,camlp5.pr_r -syntax camlp5r -linkall -linkpkg testutil.cmo -impl extfun_test.ml -o extfun_test.byte

papr_test_matrix.cmo: papr_test_matrix.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl papr_test_matrix.ml

o2r_test:: o2r_test.byte
	./o2r_test.byte $(TESTARGS)

o2r_test.byte: o2r_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op,camlp5.pr_r -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo o2r_test.ml -o o2r_test.byte

r2r_test:: r2r_test.byte
	./r2r_test.byte $(TESTARGS)

r2r_test.byte: r2r_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r,camlp5.pr_r -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo r2r_test.ml -o r2r_test.byte


r2o_test:: r2o_test.byte
	./r2o_test.byte $(TESTARGS)

r2o_test.byte: r2o_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r,camlp5.pr_o -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo r2o_test.ml -o r2o_test.byte


o2o_test:: o2o_test.byte
	./o2o_test.byte $(TESTARGS)

o2o_test.byte: o2o_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op,camlp5.pr_o -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo o2o_test.ml -o o2o_test.byte

o2official_test:: o2official_test.byte
	./o2official_test.byte $(TESTARGS)

o2official_test.byte: o2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_op,camlp5.pr_official -syntax camlp5r -I ../etc -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo o2official_test.ml -o o2official_test.byte


r2official_test:: r2official_test.byte
	./r2official_test.byte $(TESTARGS)

r2official_test.byte: r2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r,camlp5.pr_official -syntax camlp5r -I ../etc -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo r2official_test.ml -o r2official_test.byte



official2official_test:: official2official_test.byte
	./official2official_test.byte $(TESTARGS)

official2official_test.byte: official2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo papr_test_matrix.cmo official2official_test.ml -o official2official_test.byte

r2sch_test:: r2sch_test.byte
	./r2sch_test.byte

r2sch_test.byte: r2sch_test.ml testutil.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r,camlp5.pr_scheme -syntax camlp5r -linkall -linkpkg testutil.cmo -impl r2sch_test.ml -o r2sch_test.byte

q_MLast_test:: q_MLast_test.byte
	./q_MLast_test.byte

q_MLast_test.byte: q_MLast_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.pa_r,camlp5.pr_r,camlp5.quotations -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo -impl q_MLast_test.ml -o q_MLast_test.byte


pa_passthru.cmo: pa_passthru.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -c pa_passthru.ml

pa_deriving_show.cmo: pa_deriving_show.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -c pa_deriving_show.ml

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
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),compiler-libs.toplevel,camlp5.pa_op,camlp5.pr_official -syntax camlp5r -linkall -linkpkg -I ../top -I ../etc ../top/camlp5_top_funs.cmo testutil.cmo testutil2.cmo -impl o_top_test.ml -o o_top_test.byte

sch2r_test.pa_scheme:: sch2r_test.pa_scheme.byte
	./sch2r_test.pa_scheme.byte

sch2r_test.pa_scheme.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),camlp5.pa_scheme,camlp5.pr_r -syntax camlp5r -linkall -linkpkg testutil.cmo testutil2.cmo sch2r_test.ml -o sch2r_test.pa_scheme.byte

sch2r_test.pa_schemer:: sch2r_test.pa_schemer.byte
	./sch2r_test.pa_schemer.byte

sch2r_test.pa_schemer.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),camlp5.pr_r -syntax camlp5r -linkall -linkpkg pa_schemer.cmo testutil.cmo testutil2.cmo sch2r_test.ml -o sch2r_test.pa_schemer.byte

REVISED_KITS=pa_r.cmo pa_rp.cmo pa_macro.cmo pa_extend.cmo pa_extend_m.cmo pa_macro_gram.cmo q_phony.cmo pr_r.cmo pr_ro.cmo pr_rp.cmo pr_extend.cmo
tools/ROUNDTRIP-pa_r-pr_r.byte:
	$(MKCAMLP5) $(REVISED_KITS) -o $@

tools/ROUNDTRIP-pa_r-pr_r.opt:
	$(MKCAMLP5).opt $(REVISED_KITS:.cmo=.cmx) -o $@

tools/ROUNDTRIP-pa_o-pr_o.byte:
	$(MKCAMLP5) pa_o.cmo pr_o.cmo -o $@

tools/ROUNDTRIP-pa_o-pr_o.opt:
	$(MKCAMLP5).opt pa_o.cmx pr_o.cmx -o $@

setup-ocaml:
	opam install -y rresult fmt pcre ounit2 bos

setup: setup-ocaml
	sudo apt-get install libstring-shellquote-perl libdigest-md5-file-perl

toplevel::
	$(OCAMLTOPLEVEL) -nopromptcont

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo tools/*.byte tools/*.opt

realclean: clean
	$(RM) -f papr_official.ppo.ml
