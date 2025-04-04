# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile
include $(TOP)/config/Makefile.tools
OVERSION_NAME := $(shell ./make_version_name.sh $(OVERSION))

DIFF:=$(DIFF) -Bwi -U 10
DEP=../etc/r_keywords.cmo ../etc/pr_r.cmo quot_r.out.ml
RM=rm

all: quot_r.mlt quot_r.mlu quot_o.mlu

clean:
	$(RM) -f *.ml[tu] tmp.* *.cm* *.log *.cache *.ppo

compare_quot:
	./mkquot.sh | $(DIFF) quot_r.out.ml -

quot:
	./mkquot.sh > quot_r.out.ml

quot_o:
	./mkquot_o.sh > quot_o.out.ml

compare_quot_o:
	./mkquot_o.sh | $(DIFF) quot_o.out.ml -

quot_r.mlt: quot_r.ml ../meta/camlp5r ../meta/q_MLast.cmo $(DEP)
	cpp -E -DQMLAST -D$(OVERSION_NAME) quot_r.ml > tmp.quot_r.ml
	../meta/camlp5r ../meta/q_MLast.cmo ../etc/r_keywords.cmo ../etc/pr_r.cmo -l 400 -sep '\n' tmp.quot_r.ml | \
	$(DIFF) -I '(\*' -B quot_r.out.ml -

quot_r.mlu: quot_r.ml ../meta/camlp5r ../meta/q_ast_base.cmo ../meta/q_ast.cmo $(DEP)
	cpp -E -DQAST -D$(OVERSION_NAME) quot_r.ml > tmp.quot_r.ml
	../meta/camlp5r ../meta/q_ast_base.cmo ../meta/q_ast.cmo ../etc/r_keywords.cmo ../etc/pr_r.cmo -l 400 -sep '\n' tmp.quot_r.ml | \
	$(DIFF) -I '(\*' -B quot_r.out.ml -

quot_o.mlu: quot_o.ml ../etc/camlp5o ../meta/q_ast_base.cmo ../meta/q_ast.cmo $(DEP)
	../etc/camlp5o ../meta/q_ast_base.cmo ../meta/q_ast.cmo ../etc/o_keywords.cmo ../etc/pr_o.cmo -l 400 -flag M -sep '\n' quot_o.ml | \
	$(DIFF) -I '(\*' -B quot_o.out.ml -

quot_sch.mlu: quot_sch.ml ../etc/camlp5sch ../meta/q_ast_base.cmo ../meta/q_ast.cmo $(DEP)
	../etc/camlp5sch ../meta/q_ast_base.cmo ../meta/q_ast.cmo ../etc/r_keywords.cmo ../etc/pr_r.cmo quot_sch.ml | $(DIFF) quot_r.out.ml -
