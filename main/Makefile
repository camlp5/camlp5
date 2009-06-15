# $Id: Makefile,v 1.2 2007/07/11 12:01:39 deraugla Exp $

TOP=..
include $(TOP)/config/Makefile

SHELL=/bin/sh

INCLUDES=-I ../odyl -I $(TOP)/boot -I $(OTOP)/utils -I $(OTOP)/parsing
OCAMLCFLAGS=-warn-error A $(INCLUDES)
LINKFLAGS=$(INCLUDES)
CAMLP5_OBJS=$(TOP)/boot/stdpp.cmo $(TOP)/boot/token.cmo $(TOP)/boot/plexer.cmo $(TOP)/boot/gramext.cmo $(TOP)/boot/grammar.cmo $(TOP)/boot/extfold.cmo $(TOP)/boot/extfun.cmo $(TOP)/boot/fstream.cmo $(TOP)/boot/pretty.cmo $(OTOP)/utils/pconfig.cmo quotation.cmo ast2pt.cmo exparser.cmo spretty.cmo reloc.cmo pcaml.cmo prtools.cmo argl.cmo main.cmo
CAMLP5_XOBJS=../lib/stdpp.cmx ../lib/token.cmx ../lib/plexer.cmx ../lib/gramext.cmx ../lib/grammar.cmx ../lib/extfold.cmx ../lib/extfun.cmx ../lib/fstream.cmx ../lib/pretty.cmx $(OTOP)/utils/pconfig.cmx quotation.cmx ast2pt.cmx exparser.cmx spretty.cmx reloc.cmx pcaml.cmx prtools.cmx argl.cmx main.cmx
OBJS=../odyl/odyl.cma $(NAME).cma
CAMLP5M=

CAMLP5=$(NAME)$(EXE)
CAMLP5OPT=phony

all: $(CAMLP5)
opt: $(OBJS:.cma=.cmxa)
optp4: $(CAMLP5OPT)

$(CAMLP5): $(OBJS) ../odyl/odyl.cmo
	$(OCAMLC) $(OBJS) $(CAMLP5M) ../odyl/odyl.cmo -linkall -o $(CAMLP5)

$(CAMLP5OPT): $(OBJS:.cma=.cmxa) ../odyl/odyl.cmx
	$(OCAMLOPT) $(OBJS:.cma=.cmxa) $(CAMLP5M) ../odyl/odyl.cmx -linkall -o $(CAMLP5OPT)

$(NAME).cma: $(CAMLP5_OBJS)
	$(OCAMLC) $(LINKFLAGS) $(CAMLP5_OBJS) -a -o $(NAME).cma

$(NAME).cmxa: $(CAMLP5_XOBJS)
	$(OCAMLOPT) $(LINKFLAGS) $(CAMLP5_XOBJS) -a -o $(NAME).cmxa

clean::
	rm -f *.cm* *.pp[io] *.o *.bak .*.bak *.out *.opt
	rm -f $(CAMLP5)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  NAME=$(NAME) ../tools/depend.sh $(INCLUDES) $$i | \
	  sed -e 's| $(OTOP)| $$(OTOP)|g' >> .depend; \
	done

promote:
	cp $(CAMLP5) $(TOP)/boot/.

compare:
	@for j in $(CAMLP5); do \
		if cmp $$j $(TOP)/boot/$$j; then :; else exit 1; fi; \
	done

install:
	-$(MKDIR) "$(BINDIR)"
	-$(MKDIR) "$(LIBDIR)/$(NAME)"
	cp $(CAMLP5) "$(BINDIR)/."
	cp mLast.mli quotation.mli ast2pt.mli pcaml.mli prtools.mli "$(LIBDIR)/$(NAME)/."
	cp mLast.cmi quotation.cmi ast2pt.cmi pcaml.cmi prtools.cmi "$(LIBDIR)/$(NAME)/."
	cp $(NAME).cma "$(LIBDIR)/$(NAME)/."

include .depend
