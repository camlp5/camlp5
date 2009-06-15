# $Id: Makefile,v 1.23 2007/12/16 21:46:19 deraugla Exp $

TOP=..
include ../config/Makefile

INCLUDES=-I ../main -I ../boot -I $(OTOP)/utils -I $(OTOP)/parsing -I $(OTOP)/typing -I $(OTOP)/toplevel
OCAMLCFLAGS=-warn-error A $(INCLUDES)

CAMLP5_OBJS=$(OTOP)/utils/pconfig.cmo ../boot/ploc.cmo ../boot/plexing.cmo ../boot/plexer.cmo ../boot/fstream.cmo ../boot/gramext.cmo ../boot/grammar.cmo ../boot/extfold.cmo ../boot/extfun.cmo ../boot/pretty.cmo ../boot/eprinter.cmo ../main/quotation.cmo ../main/ast2pt.cmo ../main/reloc.cmo ../main/exparser.cmo ../main/pcaml.cmo ../main/prtools.cmo ../boot/stdpp.cmo ../boot/token.cmo
CTOP=camlp5_top.cmo
ROBJS=$(CAMLP5_OBJS) ../meta/pa_r.cmo ../meta/pa_rp.cmo rprint.cmo $(CTOP)
OOBJS=$(CAMLP5_OBJS) ../etc/pa_o.cmo ../etc/pa_op.cmo $(CTOP)
SOBJS=$(CAMLP5_OBJS) ../etc/pa_scheme.cmo $(CTOP)
OOOBJS=$(CAMLP5_OBJS) ../etc/pa_o.cmo ../etc/pa_oop.cmo $(CTOP)
OBJS=$(OTOP)/utils/pconfig.cmo ../main/quotation.cmo ../main/reloc.cmo ../main/ast2pt.cmo ../main/pcaml.cmo camlp5_top.cmo

TARGET=$(NAME)o.cma $(NAME)r.cma $(NAME)sch.cma $(NAME)_top.cma

all: $(TARGET)

$(NAME)oo.cma: $(OOOBJS)
	$(OCAMLC) $(OOOBJS) -linkall -a -o $(NAME)oo.cma

$(NAME)o.cma: $(OOBJS)
	$(OCAMLC) $(OOBJS) -linkall -a -o $(NAME)o.cma

$(NAME)r.cma: $(ROBJS)
	$(OCAMLC) $(ROBJS) -linkall -a -o $(NAME)r.cma

$(NAME)sch.cma: $(SOBJS)
	$(OCAMLC) $(SOBJS) -linkall -a -o $(NAME)sch.cma

$(NAME)_top.cma: $(OBJS)
	$(OCAMLC) $(OBJS) -a -o $(NAME)_top.cma

clean::
	rm -f *.cm[ioa] *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak $(TARGET)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  NAME=$(NAME) ../tools/depend.sh $(INCLUDES) $$i | \
	  sed -e 's| $(OTOP)| $$(OTOP)|g' >> .depend; \
	done

get_promote:

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(NAME)"
	cp $(TARGET) "$(DESTDIR)$(LIBDIR)/$(NAME)/."

include .depend
