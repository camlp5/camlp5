# $Id: Makefile,v 6.2 2010/11/08 18:07:02 deraugla Exp $

TOP=..
include ../config/Makefile

INCLUDES=-I ../main -I ../boot -I $(OTOP)/utils -I $(OTOP)/parsing -I $(OTOP)/typing -I $(OTOP)/toplevel
OCAMLCFLAGS=$(WARNERR) $(INCLUDES)

CAMLP5_OBJS=$(OTOP)/utils/pconfig.cmo ../boot/versdep.cmo ../boot/ploc.cmo ../boot/plexing.cmo ../boot/plexer.cmo ../boot/fstream.cmo ../boot/gramext.cmo ../boot/grammar.cmo ../boot/diff.cmo ../boot/extfold.cmo ../boot/extfun.cmo ../boot/pretty.cmo ../boot/pprintf.cmo ../boot/eprinter.cmo ../main/quotation.cmo ../main/reloc.cmo ../main/exparser.cmo ../main/prtools.cmo ../main/ast2pt.cmo ../main/pcaml.cmo ../boot/stdpp.cmo ../boot/token.cmo
CTOP=camlp5_top.cmo
ROBJS=$(CAMLP5_OBJS) ../meta/pa_r.cmo ../meta/pa_rp.cmo rprint.cmo $(CTOP)
OOBJS=$(CAMLP5_OBJS) ../etc/pa_o.cmo ../etc/pa_op.cmo $(CTOP)
SOBJS=$(CAMLP5_OBJS) ../etc/pa_scheme.cmo $(CTOP)
OOOBJS=$(CAMLP5_OBJS) ../etc/pa_o.cmo ../etc/pa_oop.cmo $(CTOP)
OBJS=$(OTOP)/utils/pconfig.cmo ../main/quotation.cmo ../main/reloc.cmo ../main/prtools.cmo ../main/pcaml.cmo ../main/ast2pt.cmo camlp5_top.cmo

TARGET=camlp5o.cma camlp5r.cma camlp5sch.cma camlp5_top.cma

all: $(TARGET)

camlp5oo.cma: $(OOOBJS)
	$(OCAMLC) $(OOOBJS) -linkall -a -o camlp5oo.cma

camlp5o.cma: $(OOBJS)
	$(OCAMLC) $(OOBJS) -linkall -a -o camlp5o.cma

camlp5r.cma: $(ROBJS)
	$(OCAMLC) $(ROBJS) -linkall -a -o camlp5r.cma

camlp5sch.cma: $(SOBJS)
	$(OCAMLC) $(SOBJS) -linkall -a -o camlp5sch.cma

camlp5_top.cma: $(OBJS)
	$(OCAMLC) $(OBJS) -a -o camlp5_top.cma

clean::
	rm -f *.cm[ioa] *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak $(TARGET)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  ../tools/depend.sh $(INCLUDES) $$i | \
	  sed -e 's| $(OTOP)| $$(OTOP)|g' >> .depend; \
	done

get_promote:

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/camlp5"
	cp $(TARGET) "$(DESTDIR)$(LIBDIR)/camlp5/."

include .depend
