# Makefile,v

TOP=../..
include $(TOP)/config/Makefile

INCLUDES=-I ../main -I $(TOP)/boot -I $(TOP)/lib
OCAMLCFLAGS=$(WARNERR) $(INCLUDES) -I $(OTOPU)
OBJS=q_MLast.cmo q_ast.cmo pa_r.cmo pa_rp.cmo pa_macro.cmo pa_fstream.cmo pa_extend.cmo pa_extend_m.cmo pr_dump.cmo pa_lexer.cmo
CAMLP5RM=pa_r.cmo pa_rp.cmo pr_dump.cmo
CAMLP5RMX=pa_r.cmx pa_rp.cmx pr_dump.cmx
SHELL=/bin/sh
COUT=$(OBJS) $(CAMLP5N)r$(EXE)
COPT=$(OBJS:.cmo=.cmx) $(CAMLP5N)r.opt

all: $(COUT)
opt: $(COPT)

$(CAMLP5N)r$(EXE): ../main/$(CAMLP5N)$(EXE) $(CAMLP5RM)
	$(RM) -f $(CAMLP5N)r$(EXE)
	cd ../main; $(MAKE) CAMLP5=../meta/$(CAMLP5N)r$(EXE) CAMLP5M="-I ../meta $(CAMLP5RM)"

$(CAMLP5N)r.opt: $(CAMLP5RMX)
	$(RM) -f $(CAMLP5N)r.opt
	cd ../main; $(MAKE) optp5 CAMLP5OPT=../meta/$(CAMLP5N)r.opt CAMLP5M="-I ../meta $(CAMLP5RMX)"

clean::
	$(RM) -f *.cm* *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak $(COUT) $(COPT)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.ml); do \
	  ../tools/depend.sh $(INCLUDES) -name $(CAMLP5N) $$i \
	  >> .depend; \
	done

promote:
	cp $(COUT) pa_extend.cmi $(TOP)/boot/.

compare:
	@for j in $(COUT); do \
		if cmp $$j $(TOP)/boot/$$j; then :; else exit 1; fi; \
	done

bootstrap_q_MLast:
	cd ../etc; $(MAKE) pr_r.cmo pr_extend.cmo
	OCAMLN=$(OCAMLN) ./mk_q_MLast.sh > tmp
	mv tmp q_MLast.ml

compare_q_MLast:
	cd ../etc; $(MAKE) pr_r.cmo pr_extend.cmo
	OCAMLN=$(OCAMLN) ./mk_q_MLast.sh | diff -c q_MLast.ml -

bootstrap_q_ast:
	cd ../etc; $(MAKE) pr_r.cmo pa_mkast.cmo
	OCAMLN=$(OCAMLN) ./mk_q_ast.sh > tmp
	mv tmp q_ast.ml

compare_q_ast:
	cd ../etc; $(MAKE) pr_r.cmo pa_mkast.cmo
	OCAMLN=$(OCAMLN) ./mk_q_ast.sh | diff -c q_ast.ml -

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)" "$(DESTDIR)$(BINDIR)"
	cp $(OBJS) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp pa_macro.cmi pa_extend.cmi "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp $(CAMLP5N)r$(EXE) "$(DESTDIR)$(BINDIR)/."
	if test -f $(CAMLP5N)r.opt; then \
	  cp $(CAMLP5N)r.opt "$(DESTDIR)$(BINDIR)/."; \
	fi
	if test -f pa_r.cmx; then \
	  cp $(OBJS:.cmo=.cmx) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	  for i in $(OBJS:.cmo=); do \
	     cp $$i$(EXT_OBJ) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	  done; \
	fi

include .depend
