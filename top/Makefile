# $Id: Makefile,v 1.8 2007/06/08 01:59:33 deraugla Exp $

TOP=..
include ../config/Makefile

INCLUDES=-I ../camlp4 -I ../boot -I $(OTOP)/utils -I $(OTOP)/parsing -I $(OTOP)/typing -I $(OTOP)/toplevel
OCAMLCFLAGS=-warn-error A $(INCLUDES)

CAMLP4_OBJS=$(OTOP)/utils/pconfig.cmo ../boot/stdpp.cmo ../boot/token.cmo ../boot/plexer.cmo ../boot/gramext.cmo ../boot/grammar.cmo ../boot/extfold.cmo ../boot/extfun.cmo ../boot/fstream.cmo ../camlp4/quotation.cmo ../camlp4/ast2pt.cmo ../camlp4/reloc.cmo ../camlp4/exparser.cmo ../camlp4/spretty.cmo ../camlp4/pcaml.cmo
CTOP=camlp4_top.cmo
ROBJS=$(CAMLP4_OBJS) ../meta/pa_r.cmo ../meta/pa_rp.cmo rprint.cmo $(CTOP)
OOBJS=$(CAMLP4_OBJS) ../etc/pa_o.cmo ../etc/pa_op.cmo $(CTOP)
SOBJS=$(CAMLP4_OBJS) ../etc/pa_scheme.cmo $(CTOP)
OOOBJS=$(CAMLP4_OBJS) ../etc/pa_o.cmo ../etc/pa_oop.cmo $(CTOP)
OBJS=$(OTOP)/utils/pconfig.cmo ../camlp4/quotation.cmo ../camlp4/reloc.cmo ../camlp4/ast2pt.cmo ../camlp4/spretty.cmo ../camlp4/pcaml.cmo camlp4_top.cmo

TARGET=camlp4o.cma camlp4r.cma camlp4sch.cma camlp4_top.cma

all: $(TARGET)

camlp4oo.cma: $(OOOBJS)
	$(OCAMLC) $(OOOBJS) -linkall -a -o camlp4oo.cma

camlp4o.cma: $(OOBJS)
	$(OCAMLC) $(OOBJS) -linkall -a -o camlp4o.cma

camlp4r.cma: $(ROBJS)
	$(OCAMLC) $(ROBJS) -linkall -a -o camlp4r.cma

camlp4sch.cma: $(SOBJS)
	$(OCAMLC) $(SOBJS) -linkall -a -o camlp4sch.cma

camlp4_top.cma: $(OBJS)
	$(OCAMLC) $(OBJS) -a -o camlp4_top.cma

clean::
	rm -f *.cm[ioa] *.pp[io] *.o *.bak .*.bak $(TARGET)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  ../tools/apply.sh pr_depend.cmo -- $(INCLUDES) $$i | \
	  sed -e 's| \.\./\.\.| $$(OTOP)|g' >> .depend; \
	done

get_promote:

install:
	-$(MKDIR) "$(LIBDIR)/camlp4"
	cp $(TARGET) "$(LIBDIR)/camlp4/."

include .depend
