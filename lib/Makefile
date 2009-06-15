# $Id: Makefile,v 1.9 2007/07/11 09:46:18 deraugla Exp $

TOP=..
include $(TOP)/config/Makefile

INCLUDES=
OCAMLCFLAGS=-warn-error A $(INCLUDES)
OBJS=stdpp.cmo token.cmo plexer.cmo gramext.cmo grammar.cmo extfold.cmo extfun.cmo fstream.cmo pretty.cmo
SHELL=/bin/sh
TARGET=gramlib.cma

all: $(TARGET)
opt: $(TARGET:.cma=.cmxa)

$(TARGET): $(OBJS)
	$(OCAMLC) $(OBJS) -a -o $(TARGET)

$(TARGET:.cma=.cmxa): $(OBJS:.cmo=.cmx)
	$(OCAMLOPT) $(OBJS:.cmo=.cmx) -a -o $(TARGET:.cma=.cmxa)

clean::
	rm -f *.cm[ioax] *.cmxa *.pp[io] *.o *.a *.bak .*.bak $(TARGET)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  NAME=$(NAME) ../tools/depend.sh $(INCLUDES) $$i | \
	  sed -e 's| $(OTOP)| $$(OTOP)|g' >> .depend; \
	done

promote:
	cp $(OBJS) $(OBJS:.cmo=.cmi) $(TOP)/boot/.

compare:
	@for j in $(OBJS) $(OBJS:.cmo=.cmi); do \
		if cmp $$j $(TOP)/boot/$$j; then :; else exit 1; fi; \
	done

install:
	-$(MKDIR) "$(LIBDIR)/$(NAME)"
	cp $(TARGET) *.mli "$(LIBDIR)/$(NAME)/."
	cp *.cmi "$(LIBDIR)/$(NAME)/."
	if test -f $(TARGET:.cma=.cmxa); then $(MAKE) installopt LIBDIR="$(LIBDIR)"; fi

installopt:
	cp $(TARGET:.cma=.cmxa) *.cmx "$(LIBDIR)/$(NAME)/."
	if test -f $(TARGET:.cma=.lib); then \
	  cp $(TARGET:.cma=.lib) "$(LIBDIR)/$(NAME)/."; \
	else \
	  tar cf - $(TARGET:.cma=.a) | (cd "$(LIBDIR)/$(NAME)/."; tar xf -); \
	fi

include .depend
