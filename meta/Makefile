# $Id: Makefile,v 1.31 2010/08/24 15:26:53 deraugla Exp $

TOP=..
include $(TOP)/config/Makefile

INCLUDES=-I ../main -I $(TOP)/boot -I $(OTOP)/utils
OCAMLCFLAGS=-warn-error A $(INCLUDES)
OBJS=q_MLast.cmo q_ast.cmo pa_r.cmo pa_rp.cmo pa_macro.cmo pa_fstream.cmo pa_extend.cmo pa_extend_m.cmo pr_dump.cmo pa_lexer.cmo
CAMLP5RM=pa_r.cmo pa_rp.cmo pr_dump.cmo
CAMLP5RMX=pa_r.cmx pa_rp.cmx pr_dump.cmx
SHELL=/bin/sh
COUT=$(OBJS) camlp5r$(EXE)
COPT=$(OBJS:.cmo=.cmx) camlp5r.opt

all: $(COUT)
opt: $(COPT)

camlp5r$(EXE): ../main/camlp5$(EXE) $(CAMLP5RM)
	rm -f camlp5r$(EXE)
	cd ../main; $(MAKE) CAMLP5=../meta/camlp5r$(EXE) CAMLP5M="-I ../meta $(CAMLP5RM)"

camlp5r.opt: $(CAMLP5RMX)
	rm -f camlp5r.opt
	cd ../main; $(MAKE) optp5 CAMLP5OPT=../meta/camlp5r.opt CAMLP5M="-I ../meta $(CAMLP5RMX)"

clean::
	rm -f *.cm* *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak $(COUT) $(COPT)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.ml); do \
	  ../tools/depend.sh $(INCLUDES) $$i | \
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
	./mk_q_MLast.sh > tmp
	mv tmp q_MLast.ml

compare_q_MLast:
	cd ../etc; $(MAKE) pr_r.cmo pr_extend.cmo
	./mk_q_MLast.sh | diff -c q_MLast.ml -

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/camlp5" "$(DESTDIR)$(BINDIR)"
	cp $(OBJS) "$(DESTDIR)$(LIBDIR)/camlp5/."
	cp pa_macro.cmi pa_extend.cmi "$(DESTDIR)$(LIBDIR)/camlp5/."
	cp camlp5r$(EXE) "$(DESTDIR)$(BINDIR)/."
	if test -f camlp5r.opt; then \
	  cp camlp5r.opt "$(DESTDIR)$(BINDIR)/."; \
	fi
	if test -f pa_r.cmx; then \
	  cp $(OBJS:.cmo=.cmx) "$(DESTDIR)$(LIBDIR)/camlp5/."; \
	  for i in $(OBJS:.cmo=); do \
	     cp $$i$(EXT_OBJ) "$(DESTDIR)$(LIBDIR)/camlp5/."; \
	  done; \
	fi

include .depend
