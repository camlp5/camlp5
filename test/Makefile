# Makefile,v
# Copyright (c) INRIA 2007-2017

DEP=../etc/pr_r.cmo quot_r.out.ml
RM=/bin/rm

all: quot_r.mlt quot_r.mlu quot_o.mlu

clean:
	$(RM) -f *.ml[tu]

compare_quot:
	./mkquot.sh | diff quot_r.out.ml -

quot:
	./mkquot.sh > quot_r.out.ml -

compare_quot_o:
	./mkquot_o.sh | diff quot_o.ml -

quot_o:
	./mkquot_o.sh > tmp
	mv tmp quot_o.ml

quot_r.mlt: quot_r.ml ../meta/camlp5r ../meta/q_MLast.cmo $(DEP)
	../meta/camlp5r ../meta/q_MLast.cmo ../etc/pr_r.cmo -sep '\n' quot_r.ml | diff -I '(\*' -B quot_r.out.ml -
	@touch $@

quot_r.mlu: quot_r.ml ../meta/camlp5r ../meta/q_ast.cmo $(DEP)
	../meta/camlp5r ../meta/q_ast.cmo ../etc/pr_r.cmo quot_r.ml | diff -I '(\*' -B quot_r.out.ml -
	@touch $@

quot_o.mlu: quot_o.ml ../etc/camlp5o ../meta/q_ast.cmo $(DEP)
	../etc/camlp5o ../meta/q_ast.cmo ../etc/pr_r.cmo quot_o.ml | diff -I '(\*' -B quot_r.out.ml -
	@touch $@

quot_sch.mlu: quot_sch.ml ../etc/camlp5sch ../meta/q_ast.cmo $(DEP)
	../etc/camlp5sch ../meta/q_ast.cmo ../etc/pr_r.cmo quot_sch.ml | diff quot_r.out.ml -
	@touch $W
