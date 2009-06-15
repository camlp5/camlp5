# $Id: Makefile,v 1.6 2007/10/09 02:53:07 deraugla Exp $
# Copyright (c) INRIA 2007

DEP=../etc/pr_r.cmo quot_r.out.ml

all: quot_r.mlt quot_r.mlu quot_o.mlu quot_sch.mlu

clean:
	rm -f *.ml[tu]

quot_r.mlt: quot_r.ml ../meta/camlp5r ../meta/q_MLast.cmo $(DEP)
	../meta/camlp5r ../meta/q_MLast.cmo ../etc/pr_r.cmo quot_r.ml | diff quot_r.out.ml -
	@touch $@

quot_r.mlu: quot_r.ml ../meta/camlp5r ../meta/q_ast.cmo $(DEP)
	../meta/camlp5r ../meta/q_ast.cmo ../etc/pr_r.cmo quot_r.ml | diff quot_r.out.ml -
	@touch $@

quot_o.mlu: quot_o.ml ../etc/camlp5o ../meta/q_ast.cmo $(DEP)
	../etc/camlp5o ../meta/q_ast.cmo ../etc/pr_r.cmo quot_o.ml | diff quot_r.out.ml -
	@touch $@

quot_sch.mlu: quot_sch.ml ../etc/camlp5sch ../meta/q_ast.cmo $(DEP)
	../etc/camlp5sch ../meta/q_ast.cmo ../etc/pr_r.cmo quot_sch.ml | diff quot_r.out.ml -
	@touch $W
