# $Id: Makefile,v 1.5 2007/10/08 00:55:25 deraugla Exp $
# Copyright (c) INRIA 2007

all: quot_r.mlt quot_r.mlu quot_o.mlu quot_sch.mlu

clean:
	rm -f *.ml[tu]

quot_r.mlt: quot_r.ml ../meta/camlp5r ../meta/q_MLast.cmo ../etc/pr_r.cmo
	../meta/camlp5r ../meta/q_MLast.cmo ../etc/pr_r.cmo quot_r.ml | diff quot_r.out.ml -
	@touch $@

quot_r.mlu: quot_r.ml ../meta/camlp5r ../meta/q_ast.cmo ../etc/pr_r.cmo
	../meta/camlp5r ../meta/q_ast.cmo ../etc/pr_r.cmo quot_r.ml | diff quot_r.out.ml -
	@touch $@

quot_o.mlu: quot_o.ml ../etc/camlp5o ../meta/q_ast.cmo ../etc/pr_r.cmo
	../etc/camlp5o ../meta/q_ast.cmo ../etc/pr_r.cmo quot_o.ml | diff quot_r.out.ml -
	@touch $@

quot_sch.mlu: quot_sch.ml ../etc/camlp5sch ../meta/q_ast.cmo ../etc/pr_r.cmo
	../etc/camlp5sch ../meta/q_ast.cmo ../etc/pr_r.cmo quot_sch.ml | diff quot_r.out.ml -
	@touch $W
