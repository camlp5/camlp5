# $Id: Makefile,v 1.1 2007/09/23 07:27:29 deraugla Exp $
# Copyright (c) INRIA 2007

all: check_r_q_ML check_r_q check_o_q

check_r_q_ML:
	../meta/camlp5r ../meta/q_MLast.cmo ../etc/pr_r.cmo quot_r.ml | diff quot_r.out.ml -

check_r_q:
	../meta/camlp5r ../meta/q_ast.cmo ../etc/pr_r.cmo quot_r.ml | diff quot_r.out.ml -

check_o_q:
	../etc/camlp5o ../meta/q_ast.cmo ../etc/pr_r.cmo quot_o.ml | diff quot_r.out.ml -
