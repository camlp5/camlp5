# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

DIFF=diff -Bwi -u20
RM=rm

TESTS=official2official_test o2r_test r2r_test r2o_test o2o_test o2official_test r2official_test r2sch_test \
	sch2r_test.pa_scheme sch2r_test.pa_schemer \
	extfun_test

all-tests: all $(TESTS)

all: \
	o2r_test.byte \
	r2r_test.byte \
	r2o_test.byte \
	o2o_test.byte \
	o2official_test.byte \
	r2official_test.byte \
	official2official_test.byte \
	r2sch_test.byte \
	sch2r_test.pa_scheme.byte \
	sch2r_test.pa_schemer.byte \
	extfun_test.byte \
	roundtrip_lexer.byte \
	papr_official.byte \
	tools/ROUNDTRIP-pa_r-pr_r.byte \
	tools/ROUNDTRIP-pa_r-pr_r.opt \
	tools/ROUNDTRIP-pa_o-pr_o.byte \
	tools/ROUNDTRIP-pa_o-pr_o.opt

OCAMLFIND=PATH=$(TOP)/local-install/bin:$(PATH) OCAMLPATH=$(TOP)/local-install/lib: ocamlfind
CAMLP5LIB=$(shell $(OCAMLFIND) query camlp5)
MKCAMLP5=PATH=$(TOP)/local-install/bin:$(PATH) OCAMLPATH=$(TOP)/local-install/lib: $(TOP)/local-install/bin/mkcamlp5
CAMLP5R=$(TOP)/local-install/bin/camlp5r -I $(CAMLP5LIB)
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

roundtrip_lexer.cmo: roundtrip_lexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl roundtrip_lexer.ml

roundtrip_lexer.byte: roundtrip_lexer.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -linkall -linkpkg gramlib.cma roundtrip_lexer.cmo -o roundtrip_lexer.byte

papr_official.cmo: papr_official.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES_NOCAMLP5) -warn-error A -c -o papr_official.cmo -impl papr_official.ppo.ml

.PRECIOUS: papr_official.ppo.ml

papr_official.ppo.ml: papr_official.ml
	$(CAMLP5R) pr_o.cmo -I . -mode S -o papr_official.ppo.ml papr_official.ml

papr_official.byte: papr_official.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES_NOCAMLP5),ounit2 -linkall -linkpkg papr_official.cmo -o papr_official.byte

extfun_test:: all
	./extfun_test.byte

extfun_test.byte: extfun_test.ml testutil.cmo
	$(CAMLP5R) -I . -mode S -o extfun_test.ppo extfun_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -linkall -linkpkg odyl.cma camlp5.cma pr_r.cmo testutil.cmo -impl extfun_test.ppo -o extfun_test.byte

papr_test_matrix.cmo: papr_test_matrix.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -warn-error A -c -impl papr_test_matrix.ml

o2r_test:: all
	./o2r_test.byte

o2r_test.byte: o2r_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg odyl.cma camlp5.cma pa_o.cmo pr_r.cmo pr_ro.cmo testutil.cmo testutil2.cmo papr_test_matrix.cmo o2r_test.ml -o o2r_test.byte

r2r_test:: all
	./r2r_test.byte

r2r_test.byte: r2r_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg odyl.cma camlp5.cma pa_r.cmo pr_r.cmo pr_ro.cmo testutil.cmo testutil2.cmo papr_test_matrix.cmo r2r_test.ml -o r2r_test.byte


r2o_test:: all
	./r2o_test.byte

r2o_test.byte: r2o_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg odyl.cma camlp5.cma pa_r.cmo pr_o.cmo testutil.cmo testutil2.cmo papr_test_matrix.cmo r2o_test.ml -o r2o_test.byte


o2o_test:: all
	./o2o_test.byte

o2o_test.byte: o2o_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -linkall -linkpkg odyl.cma camlp5.cma pa_o.cmo pr_o.cmo testutil.cmo testutil2.cmo papr_test_matrix.cmo o2o_test.ml -o o2o_test.byte

o2official_test:: all
	./o2official_test.byte

o2official_test.byte: o2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -I ../etc -linkall -linkpkg odyl.cma camlp5.cma pa_o.cmo pr_official.cmo testutil.cmo testutil2.cmo papr_test_matrix.cmo o2official_test.ml -o o2official_test.byte


r2official_test:: all
	./r2official_test.byte

r2official_test.byte: r2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -I ../etc -linkall -linkpkg odyl.cma camlp5.cma pa_r.cmo pr_official.cmo testutil.cmo testutil2.cmo papr_test_matrix.cmo r2official_test.ml -o r2official_test.byte



official2official_test:: all
	./official2official_test.byte

official2official_test.byte: official2official_test.ml testutil.cmo testutil2.cmo papr_test_matrix.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -I ../etc -linkall -linkpkg odyl.cma camlp5.cma testutil.cmo testutil2.cmo papr_test_matrix.cmo official2official_test.ml -o official2official_test.byte

r2sch_test:: all
	./r2sch_test.byte

r2sch_test.byte: r2sch_test.ml testutil.cmo
	$(CAMLP5R) -I . -mode S -o r2sch_test.ppo r2sch_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg odyl.cma camlp5.cma pa_r.cmo pr_scheme.cmo testutil.cmo -impl r2sch_test.ppo -o r2sch_test.byte

sch2r_test.cmo: sch2r_test.ml testutil.cmo testutil2.cmo
	$(CAMLP5R) -I . -mode S -o sch2r_test.ppo sch2r_test.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -c -impl sch2r_test.ppo

sch2r_test.pa_scheme:: all
	./sch2r_test.pa_scheme.byte

sch2r_test.pa_scheme.byte: sch2r_test.cmo testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg odyl.cma camlp5.cma pa_scheme.cmo pr_r.cmo testutil.cmo testutil2.cmo sch2r_test.cmo -o sch2r_test.pa_scheme.byte

sch2r_test.pa_schemer:: all
	./sch2r_test.pa_schemer.byte

sch2r_test.pa_schemer.byte: sch2r_test.cmo testutil.cmo testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg odyl.cma camlp5.cma ../etc/pa_schemer.cmo pr_r.cmo testutil.cmo testutil2.cmo sch2r_test.cmo -o sch2r_test.pa_schemer.byte

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

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo tools/*.byte tools/*.opt

realclean: clean
	$(RM) -f papr_official.ppo.ml
