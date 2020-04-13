# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

DIFF=diff -Bwi -u20
RM=rm

TESTS=test_deriving_show test_deriving_show.ppx \
      test_deriving_eq test_deriving_eq.ppx \
      test_deriving_ord test_deriving_ord.ppx \
      test_deriving_enum test_deriving_enum.ppx \

all-tests: all $(TESTS)

all: \
	test_deriving_show test_deriving_show.ppx \
	test_deriving_eq test_deriving_eq.ppx \
	test_deriving_ord test_deriving_ord.ppx \
	test_deriving_enum test_deriving_enum.ppx \


LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
OCAMLTOPLEVEL=$(LAUNCH) ocaml
CAMLP5LIB=$(shell $(OCAMLFIND) query camlp5)
MKCAMLP5=$(LAUNCH) mkcamlp5
CAMLP5R=$(LAUNCH) camlp5r -I $(CAMLP5LIB)
INCLUDES=-I $(CAMLP5LIB)
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)
COMPILERLIBS= -I +compiler-libs ocamlcommon.cma ocamlbytecomp.cma ocamltoplevel.cma
PACKAGES_NOCAMLP5=rresult,fmt,pcre,ounit2,compiler-libs.common
PACKAGES=$(PACKAGES_NOCAMLP5),camlp5

pa_passthru.cmo: pa_passthru.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -c pa_passthru.ml

ppxutil.cmo: ppxutil.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -c ppxutil.ml

pa_deriving_show.cmo: pa_deriving_show.ml pa_passthru.cmo ppxutil.cmo
	$(CAMLP5R) -nolib -I $(CAMLP5LIB) 'pa_r.cmo' 'pa_rp.cmo' 'pr_r.cmo' pr_ro.cmo 'pa_deriving_show.ml' > pa_deriving_show.ppo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -c pa_deriving_show.ml

test_deriving_show.ppx: test_deriving_show.ppx.byte
	./test_deriving_show.ppx.byte

test_deriving_show.ppx.byte: test_deriving_show.ml ../testsuite/testutil.cmo ../testsuite/testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,ppx_deriving.eq,ppx_deriving.show -linkall -linkpkg -I ../testsuite -dsource test_deriving_show.ml > test_deriving_show.ppx.ppo 2>&1 || true
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,ppx_deriving.eq,ppx_deriving.show -linkall -linkpkg -I ../testsuite ../testsuite/testutil.cmo ../testsuite/testutil2.cmo test_deriving_show.ml -o test_deriving_show.ppx.byte

test_deriving_show: test_deriving_show.byte
	./test_deriving_show.byte

test_deriving_show.byte: test_deriving_show.ml pa_passthru.cmo pa_deriving_show.cmo ../testsuite/testutil.cmo ../testsuite/testutil2.cmo ppxutil.cmo
	$(LAUNCH) camlp5 -nolib -I $(CAMLP5LIB) pa_o.cmo pa_op.cmo pr_o.cmo ./pa_passthru.cmo ./ppxutil.cmo ./pa_deriving_show.cmo test_deriving_show.ml > test_deriving_show.ppo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -linkall -linkpkg -I ../testsuite ../testsuite/testutil.cmo ../testsuite/testutil2.cmo -impl test_deriving_show.ppo -o test_deriving_show.byte

pa_deriving_eq.cmo: pa_deriving_eq.ml pa_passthru.cmo
	$(CAMLP5R) -nolib -I $(CAMLP5LIB) 'pa_r.cmo' 'pa_rp.cmo' 'pr_r.cmo' pr_ro.cmo 'pa_deriving_eq.ml' > pa_deriving_eq.ppo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -c pa_deriving_eq.ml

test_deriving_eq.ppx: test_deriving_eq.ppx.byte
	./test_deriving_eq.ppx.byte

test_deriving_eq.ppx.byte: test_deriving_eq.ml ../testsuite/testutil.cmo ../testsuite/testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,ppx_deriving.eq -linkall -linkpkg -I ../testsuite -dsource test_deriving_eq.ml > test_deriving_eq.ppx.ppo 2>&1 || true
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,ppx_deriving.eq -linkall -linkpkg -I ../testsuite ../testsuite/testutil.cmo ../testsuite/testutil2.cmo test_deriving_eq.ml -o test_deriving_eq.ppx.byte

test_deriving_eq: test_deriving_eq.byte
	./test_deriving_eq.byte

test_deriving_eq.byte: test_deriving_eq.ml pa_passthru.cmo pa_deriving_eq.cmo ../testsuite/testutil.cmo ../testsuite/testutil2.cmo
	$(LAUNCH) camlp5 -nolib -I $(CAMLP5LIB) pa_o.cmo pa_op.cmo pr_o.cmo ./pa_passthru.cmo ./ppxutil.cmo ./pa_deriving_eq.cmo test_deriving_eq.ml > test_deriving_eq.ppo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -linkall -linkpkg -I ../testsuite ../testsuite/testutil.cmo ../testsuite/testutil2.cmo -impl test_deriving_eq.ppo -o test_deriving_eq.byte


pa_deriving_ord.cmo: pa_deriving_ord.ml pa_passthru.cmo
	$(CAMLP5R) -nolib -I $(CAMLP5LIB) 'pa_r.cmo' 'pa_rp.cmo' 'pr_r.cmo' pr_ro.cmo 'pa_deriving_ord.ml' > pa_deriving_ord.ppo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -c pa_deriving_ord.ml

test_deriving_ord.ppx: test_deriving_ord.ppx.byte
	./test_deriving_ord.ppx.byte

test_deriving_ord.ppx.byte: test_deriving_ord.ml ../testsuite/testutil.cmo ../testsuite/testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,ppx_deriving.ord -linkall -linkpkg -I ../testsuite -dsource test_deriving_ord.ml > test_deriving_ord.ppx.ppo 2>&1 || true
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,ppx_deriving.ord -linkall -linkpkg -I ../testsuite ../testsuite/testutil.cmo ../testsuite/testutil2.cmo test_deriving_ord.ml -o test_deriving_ord.ppx.byte

test_deriving_ord: test_deriving_ord.byte
	./test_deriving_ord.byte

test_deriving_ord.byte: test_deriving_ord.ml pa_passthru.cmo pa_deriving_ord.cmo ../testsuite/testutil.cmo ../testsuite/testutil2.cmo
	$(LAUNCH) camlp5 -nolib -I $(CAMLP5LIB) pa_o.cmo pa_op.cmo pr_o.cmo ./pa_passthru.cmo ./ppxutil.cmo ./pa_deriving_ord.cmo test_deriving_ord.ml > test_deriving_ord.ppo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -linkall -linkpkg -I ../testsuite ../testsuite/testutil.cmo ../testsuite/testutil2.cmo -impl test_deriving_ord.ppo -o test_deriving_ord.byte


pa_deriving_enum.cmo: pa_deriving_enum.ml pa_passthru.cmo
	$(CAMLP5R) -nolib -I $(CAMLP5LIB) 'pa_r.cmo' 'pa_rp.cmo' 'pr_r.cmo' pr_ro.cmo 'pa_deriving_enum.ml' > pa_deriving_enum.ppo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -syntax camlp5r -c pa_deriving_enum.ml

test_deriving_enum.ppx: test_deriving_enum.ppx.byte
	./test_deriving_enum.ppx.byte

test_deriving_enum.ppx.byte: test_deriving_enum.ml ../testsuite/testutil.cmo ../testsuite/testutil2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,ppx_deriving.show,ppx_deriving.enum -linkall -linkpkg -I ../testsuite -dsource test_deriving_enum.ml > test_deriving_enum.ppx.ppo 2>&1 || true
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,ppx_deriving.show,ppx_deriving.enum -linkall -linkpkg -I ../testsuite ../testsuite/testutil.cmo ../testsuite/testutil2.cmo test_deriving_enum.ml -o test_deriving_enum.ppx.byte

test_deriving_enum: test_deriving_enum.byte
	./test_deriving_enum.byte

test_deriving_enum.byte: test_deriving_enum.ml pa_passthru.cmo pa_deriving_enum.cmo pa_deriving_show.cmo ../testsuite/testutil.cmo ../testsuite/testutil2.cmo
	$(LAUNCH) camlp5 -nolib -I $(CAMLP5LIB) pa_o.cmo pa_op.cmo pr_o.cmo ./pa_passthru.cmo ./ppxutil.cmo ./pa_deriving_show.cmo ./pa_deriving_enum.cmo test_deriving_enum.ml > test_deriving_enum.ppo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2 -linkall -linkpkg -I ../testsuite ../testsuite/testutil.cmo ../testsuite/testutil2.cmo -impl test_deriving_enum.ppo -o test_deriving_enum.byte

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo

realclean: clean
