# $Id: Makefile,v 1.28 2007/11/27 19:18:24 deraugla Exp $

TOP=..
include $(TOP)/config/Makefile

INCLUDES=-I ../main -I $(TOP)/boot -I $(OTOP)/utils
OCAMLCFLAGS=-warn-error A $(INCLUDES)
OBJS=q_MLast.cmo q_ast.cmo pa_r.cmo pa_rp.cmo pa_macro.cmo pa_fstream.cmo pa_extend.cmo pa_extend_m.cmo pr_dump.cmo pa_lexer.cmo
CAMLP5RM=pa_r.cmo pa_rp.cmo pr_dump.cmo
CAMLP5RMX=pa_r.cmx pa_rp.cmx pr_dump.cmx
SHELL=/bin/sh
COUT=$(OBJS) $(NAME)r$(EXE)
COPT=$(OBJS:.cmo=.cmx) $(NAME)r.opt

all: $(COUT)
opt: $(COPT)

$(NAME)r$(EXE): ../main/$(NAME)$(EXE) $(CAMLP5RM)
	rm -f $(NAME)r$(EXE)
	cd ../main; $(MAKE) OTOP=$(OTOP) CAMLP5=../meta/$(NAME)r$(EXE) CAMLP5M="-I ../meta $(CAMLP5RM)"

$(NAME)r.opt: $(CAMLP5RMX)
	rm -f $(NAME)r.opt
	cd ../main; $(MAKE) optp5 OTOP=$(OTOP) CAMLP5OPT=../meta/$(NAME)r.opt CAMLP5M="-I ../meta $(CAMLP5RMX)"

clean::
	rm -f *.cm* *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak $(COUT) $(COPT)

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
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(NAME)" "$(DESTDIR)$(BINDIR)"
	cp $(OBJS) "$(DESTDIR)$(LIBDIR)/$(NAME)/."
	cp pa_macro.cmi pa_extend.cmi "$(DESTDIR)$(LIBDIR)/$(NAME)/."
	cp $(NAME)r$(EXE) "$(DESTDIR)$(BINDIR)/."
	if test -f $(NAME)r.opt; then \
	  cp $(NAME)r.opt "$(DESTDIR)$(BINDIR)/."; \
	fi
	if test -f pa_r.cmx; then \
	  cp $(OBJS:.cmo=.cmx) "$(DESTDIR)$(LIBDIR)/$(NAME)/."; \
	  cp $(OBJS:.cmo=$(EXT_OBJ)) "$(DESTDIR)$(LIBDIR)/$(NAME)/."; \
	fi

include .depend
