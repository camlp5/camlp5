# $Id: Makefile,v 1.2 2007/09/24 08:34:40 deraugla Exp $
# Copyright (c) INRIA 2007

all: check_r_q_ML check_r_q check_o_q

check_r_q_ML:
	../meta/camlp5r ../meta/q_MLast.cmo ../etc/pr_r.cmo quot_r.ml 2>&1 | diff quot_r.out.ml -

check_r_q:
	../meta/camlp5r ../meta/q_ast.cmo ../etc/pr_r.cmo quot_r.ml 2>&1 | diff quot_r.out.ml -

check_o_q:
	../etc/camlp5o ../meta/q_ast.cmo ../etc/pr_r.cmo quot_o.ml 2>&1 | diff quot_r.out.ml -
