# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile
OVERSION_NAME := $(shell ./make_version_name.sh $(OVERSION))

DIFF=diff -Bwi -u20
DEP=../etc/pr_r.cmo quot_r.out.ml
RM=rm

all: quot_r.mlt quot_r.mlu

clean:
	$(RM) -f *.ml[tu] tmp.* *.cm* *.byte *.log *.cache *.ppo

compare_quot:
	./mkquot.sh | $(DIFF) quot_r.out.ml -

quot:
	./mkquot.sh > quot_r.out.ml -

compare_quot_o:
	./mkquot_o.sh | $(DIFF) quot_o.ml -

quot_o:
	./mkquot_o.sh > tmp
	mv tmp quot_o.ml

quot_r.mlt: quot_r.ml ../meta/camlp5r ../meta/q_MLast.cmo $(DEP)
	cpp -E -DQMLAST -D$(OVERSION_NAME) quot_r.ml > tmp.quot_r.ml
	../meta/camlp5r ../meta/q_MLast.cmo ../etc/pr_r.cmo -sep '\n' tmp.quot_r.ml | \
	$(DIFF) -I '(\*' -B quot_r.out.ml -
	@touch $@

quot_r.mlu: quot_r.ml ../meta/camlp5r ../meta/q_ast.cmo $(DEP)
	cpp -E -DQAST -D$(OVERSION_NAME) quot_r.ml > tmp.quot_r.ml
	../meta/camlp5r ../meta/q_ast.cmo ../etc/pr_r.cmo -sep '\n' tmp.quot_r.ml | \
	$(DIFF) -I '(\*' -B quot_r.out.ml -
	@touch $@

#quot_o.mlu: quot_o.ml ../etc/camlp5o ../meta/q_ast.cmo $(DEP)
#	../etc/camlp5o ../meta/q_ast.cmo ../etc/pr_r.cmo quot_o.ml | $(DIFF) -I '(\*' -B quot_r.out.ml -
#	@touch $@

quot_sch.mlu: quot_sch.ml ../etc/camlp5sch ../meta/q_ast.cmo $(DEP)
	../etc/camlp5sch ../meta/q_ast.cmo ../etc/pr_r.cmo quot_sch.ml | $(DIFF) quot_r.out.ml -
	@touch $W


all-ounit-tests: o2r_test.byte r2sch_test.byte sch2r_test.byte
	./o2r_test.byte
	./r2sch_test.byte
	./sch2r_test.byte

INCLUDES=-I ../main -I ../lib -I ../meta -I ../etc -I ../top -I ../odyl
OCAMLCFLAGS=-g $(WARNERR) $(INCLUDES)
COMPILERLIBS= -I +compiler-libs ocamlcommon.cma ocamlbytecomp.cma ocamltoplevel.cma


testutil.cmo: testutil.ml

testutil2.cmo: testutil2.ml
	ocamlfind ocamlc -package rresult,fmt -c testutil2.ml

o2r_test.byte: o2r_test.ml testutil.cmo
	ocamlfind ocamlc -package ounit2 -linkall -linkpkg $(COMPILERLIBS) -I ../main ../odyl/odyl.cma ../main/camlp5.cma ../etc/pa_o.cmo ../etc/pr_r.cmo testutil.cmo o2r_test.ml -o o2r_test.byte

r2sch_test.byte: r2sch_test.ml testutil.cmo
	ocamlfind ocamlc -package ounit2 -linkall -linkpkg $(COMPILERLIBS) -I ../main ../odyl/odyl.cma ../main/camlp5.cma ../meta/pa_r.cmo ../etc/pr_scheme.cmo testutil.cmo r2sch_test.ml -o r2sch_test.byte

sch2r_test.byte: sch2r_test.ml testutil.cmo testutil2.cmo
	ocamlfind ocamlc -package ounit2,fmt,rresult -linkall -linkpkg $(COMPILERLIBS) -I ../main -I ../lib -I ../etc ../odyl/odyl.cma ../main/camlp5.cma ../etc/pa_schemer.cmo ../etc/pr_r.cmo testutil.cmo testutil2.cmo sch2r_test.ml -o sch2r_test.byte
