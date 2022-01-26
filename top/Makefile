# Makefile,v

TOP=..
include ../config/Makefile

ifeq ($(BOOTSTRAPPED),1)
FMTDIR=$(shell ocamlfind query fmt)
FMTINCLUDES=-I $(FMTDIR)
else
FMTINCLUDES=
endif
INCLUDES=-I ../main -I ../boot $(FMTINCLUDES)
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)

CAMLP5_OBJS=$(OTOPU)/pconfig.cmo ../boot/versdep.cmo ../boot/ploc.cmo ../boot/plexing.cmo ../boot/plexer.cmo ../boot/fstream.cmo ../boot/gramext.cmo ../boot/grammar.cmo ../boot/diff.cmo ../boot/extfold.cmo ../boot/extfun.cmo ../boot/pretty.cmo ../boot/pprintf.cmo ../boot/eprinter.cmo ../main/asttools.cmo ../main/mlsyntax.cmo ../main/quotation.cmo ../main/reloc.cmo ../main/pp_debug.cmo ../main/prtools.cmo ../main/ast2pt.cmo ../main/pcaml.cmo ../main/parserify.cmo ../main/exparser.cmo ../boot/stdpp.cmo ../boot/token.cmo

CTOP=camlp5_top_funs.cmo camlp5_top.cmo
ROBJS=$(CAMLP5_OBJS) ../meta/pa_r.cmo ../meta/pa_rp.cmo rprint.cmo $(CTOP)
OOBJS=$(CAMLP5_OBJS) ../etc/pa_o.cmo ../etc/pa_op.cmo $(CTOP)
SOBJS=$(CAMLP5_OBJS) ../etc/pa_scheme.cmo $(CTOP)
OOOBJS=$(CAMLP5_OBJS) ../etc/pa_o.cmo ../etc/pa_oop.cmo $(CTOP)
OBJS=$(OTOPU)/pconfig.cmo ../main/quotation.cmo ../main/reloc.cmo ../main/prtools.cmo ../main/pcaml.cmo ../main/ast2pt.cmo camlp5_top_funs.cmo camlp5_top.cmo

TARGET=$(CAMLP5N)o.cma $(CAMLP5N)r.cma $(CAMLP5N)sch.cma $(CAMLP5N)_top.cma

all: $(TARGET)

$(CAMLP5N)oo.cma: $(OOOBJS)
	$(OCAMLC) $(OOOBJS) $(DEBUG) -linkall -a -o $(CAMLP5N)oo.cma

$(CAMLP5N)o.cma: $(OOBJS)
	$(OCAMLC) $(OOBJS) $(DEBUG) -linkall -a -o $(CAMLP5N)o.cma

$(CAMLP5N)r.cma: $(ROBJS)
	$(OCAMLC) $(ROBJS) $(DEBUG) -linkall -a -o $(CAMLP5N)r.cma

$(CAMLP5N)sch.cma: $(SOBJS)
	$(OCAMLC) $(SOBJS) $(DEBUG) -linkall -a -o $(CAMLP5N)sch.cma

$(CAMLP5N)_top.cma: $(OBJS)
	$(OCAMLC) $(OBJS) $(DEBUG) -linkall -a -o $(CAMLP5N)_top.cma

clean::
	$(RM) -f *.cm[ioa] *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak $(TARGET)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  ../tools/depend.sh $(INCLUDES) -name $(CAMLP5N) $$i \
	  >> .depend; \
	done

get_promote:

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)"
	cp $(TARGET) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp camlp5_top_funs.cmi camlp5_top_funs.cmo "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."

include .depend
