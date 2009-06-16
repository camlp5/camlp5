# $Id: Makefile,v 1.21 2007/12/28 12:58:30 deraugla Exp $

TOP=..
include $(TOP)/config/Makefile

SHELL=/bin/sh

INCLUDES=-I ../odyl -I $(TOP)/boot -I $(OTOP)/utils -I $(OTOP)/parsing
OCAMLCFLAGS=-warn-error A $(INCLUDES)
LINKFLAGS=$(INCLUDES)
CAMLP5_OBJS=$(TOP)/boot/ploc.cmo $(TOP)/boot/plexing.cmo $(TOP)/boot/plexer.cmo $(TOP)/boot/fstream.cmo $(TOP)/boot/gramext.cmo $(TOP)/boot/grammar.cmo $(TOP)/boot/diff.cmo $(TOP)/boot/extfold.cmo $(TOP)/boot/extfun.cmo $(TOP)/boot/pretty.cmo $(TOP)/boot/pprintf.cmo $(TOP)/boot/eprinter.cmo $(OTOP)/utils/pconfig.cmo quotation.cmo ast2pt.cmo reloc.cmo pcaml.cmo exparser.cmo prtools.cmo parserify.cmo argl.cmo $(TOP)/boot/stdpp.cmo $(TOP)/boot/token.cmo main.cmo
CAMLP5_XOBJS=../lib/ploc.cmx ../lib/plexing.cmx ../lib/plexer.cmx ../lib/fstream.cmx ../lib/gramext.cmx ../lib/grammar.cmx ../lib/diff.cmx ../lib/extfold.cmx ../lib/extfun.cmx ../lib/pretty.cmx ../lib/pprintf.cmx ../lib/eprinter.cmx $(OTOP)/utils/pconfig.cmx quotation.cmx ast2pt.cmx reloc.cmx pcaml.cmx exparser.cmx prtools.cmx parserify.cmx argl.cmx ../lib/stdpp.cmx ../lib/token.cmx main.cmx
OBJS=../odyl/odyl.cma $(NAME).cma
CAMLP5M=

CAMLP5=$(NAME)$(EXE)
CAMLP5OPT=phony

all: $(CAMLP5)
opt: $(OBJS:.cma=.cmxa)
optp5: $(CAMLP5OPT)

$(CAMLP5): $(OBJS) ../odyl/odyl.cmo
	$(OCAMLC) $(OBJS) $(CAMLP5M) ../odyl/odyl.cmo -linkall -o $(CAMLP5)

$(CAMLP5OPT): $(OBJS:.cma=.cmxa) ../odyl/odyl.cmx
	$(OCAMLOPT) $(OBJS:.cma=.cmxa) $(CAMLP5M) ../odyl/odyl.cmx -linkall -o $(CAMLP5OPT)

$(NAME).cma: $(CAMLP5_OBJS)
	$(OCAMLC) $(LINKFLAGS) $(CAMLP5_OBJS) -a -o $(NAME).cma

$(NAME).cmxa: $(CAMLP5_XOBJS)
	$(OCAMLOPT) $(LINKFLAGS) $(CAMLP5_XOBJS) -a -o $(NAME).cmxa

clean::
	rm -f *.cm* *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak *.out *.opt
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
	-$(MKDIR) "$(DESTDIR)$(BINDIR)"
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(NAME)"
	cp $(CAMLP5) "$(DESTDIR)$(BINDIR)/."
	cp mLast.mli quotation.mli ast2pt.mli pcaml.mli prtools.mli "$(DESTDIR)$(LIBDIR)/$(NAME)/."
	cp mLast.cmi quotation.cmi ast2pt.cmi pcaml.cmi prtools.cmi "$(DESTDIR)$(LIBDIR)/$(NAME)/."
	cp $(NAME).cma "$(DESTDIR)$(LIBDIR)/$(NAME)/."
	if test -f $(NAME).cmxa; then \
	  cp $(NAME).cmxa "$(DESTDIR)$(LIBDIR)/$(NAME)/."; \
	  cp $(NAME)$(EXT_LIB) "$(DESTDIR)$(LIBDIR)/$(NAME)/."; \
	fi

include .depend
