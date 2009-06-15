# $Id: Makefile,v 1.4 2007/10/07 08:23:21 deraugla Exp $
# Copyright (c) INRIA 2007

all: check_r_q_ML check_r_q check_o_q check_sch_q

check_r_q_ML:
	../meta/camlp5r ../meta/q_MLast.cmo ../etc/pr_r.cmo quot_r.ml | diff quot_r.out.ml -

check_r_q:
	../meta/camlp5r ../meta/q_ast.cmo ../etc/pr_r.cmo quot_r.ml | diff quot_r.out.ml -

check_o_q:
	../etc/camlp5o ../meta/q_ast.cmo ../etc/pr_r.cmo quot_o.ml | diff quot_r.out.ml -

check_sch_q:
	../etc/camlp5sch ../meta/q_ast.cmo ../etc/pr_r.cmo quot_sch.ml | diff quot_r.out.ml -
