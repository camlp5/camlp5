# $Id: Makefile,v 1.13 2007/08/16 04:11:44 deraugla Exp $

TOP=..
include $(TOP)/config/Makefile

INCLUDES=-I ../main -I $(TOP)/boot -I $(OTOP)/utils
OCAMLCFLAGS=-warn-error A $(INCLUDES)
OBJS=q_MLast.cmo pa_r.cmo pa_rp.cmo pa_extend.cmo pa_extend_m.cmo pa_macro.cmo pr_dump.cmo pa_lex.cmo
CAMLP5RM=pa_r.cmo pa_rp.cmo pr_dump.cmo
CAMLP5RMX=pa_r.cmx pa_rp.cmx pr_dump.cmx
SHELL=/bin/sh
COUT=$(OBJS) $(NAME)r$(EXE)
COPT=$(NAME)r.opt

all: $(COUT)
opt: $(COPT)

$(NAME)r$(EXE): ../main/$(NAME)$(EXE) $(CAMLP5RM)
	rm -f $(NAME)r$(EXE)
	cd ../main; $(MAKE) OTOP=$(OTOP) CAMLP5=../meta/$(NAME)r$(EXE) CAMLP5M="-I ../meta $(CAMLP5RM)"

$(NAME)r.opt: $(CAMLP5RMX)
	rm -f $(NAME)r.opt
	cd ../main; $(MAKE) optp5 OTOP=$(OTOP) CAMLP5OPT=../meta/$(NAME)r.opt CAMLP5M="-I ../meta $(CAMLP5RMX)"

clean::
	rm -f *.cm* *.pp[io] *.o *.bak .*.bak $(COUT) $(COPT)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.ml); do \
	  NAME=$(NAME) ../tools/depend.sh $(INCLUDES) $$i | \
	  sed -e 's| $(OTOP)| $$(OTOP)|g' >> .depend; \
	done

promote:
	cp $(COUT) pa_extend.cmi $(TOP)/boot/.

compare:
	@for j in $(COUT); do \
		if cmp $$j $(TOP)/boot/$$j; then :; else exit 1; fi; \
	done

bootstrap_q_MLast:
	cd ../etc; $(MAKE) pr_r.cmo pr_extend.cmo
	NAME=$(NAME) ./mk_q_MLast.sh > tmp
	mv tmp q_MLast.ml

compare_q_MLast:
	cd ../etc; $(MAKE) pr_r.cmo pr_extend.cmo
	NAME=$(NAME) ./mk_q_MLast.sh | diff -c q_MLast.ml -

install:
	-$(MKDIR) "$(LIBDIR)/$(NAME)" "$(BINDIR)"
	cp $(OBJS) "$(LIBDIR)/$(NAME)/."
	cp pa_macro.cmi pa_extend.cmi "$(LIBDIR)/$(NAME)/."
	cp $(NAME)r$(EXE) "$(BINDIR)/."
	if test -f $(COPT); then cp $(COPT) "$(BINDIR)/."; fi

include .depend
