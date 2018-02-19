# Makefile,v

TOP=..
include $(TOP)/config/Makefile

OCAMLCFLAGS=$(WARNERR) -I $(OTOPP)
OBJS=versdep.cmo ploc.cmo plexing.cmo plexer.cmo fstream.cmo gramext.cmo grammar.cmo diff.cmo extfold.cmo extfun.cmo pretty.cmo pprintf.cmo eprinter.cmo stdpp.cmo token.cmo
SHELL=/bin/sh
TARGET=gramlib.cma

all: $(TARGET)
opt: $(TARGET:.cma=.cmxa)

$(TARGET): $(OBJS)
	$(OCAMLC) $(OBJS) -a -o $(TARGET)

$(TARGET:.cma=.cmxa): $(OBJS:.cmo=.cmx)
	$(OCAMLOPT) $(OBJS:.cmo=.cmx) -a -o $(TARGET:.cma=.cmxa)

clean::
	$(RM) -f *.cm[ioax] *.cmxa *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak
	$(RM) -f $(TARGET)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  ../tools/depend.sh -name $(CAMLP5N) $$i >> .depend; \
	done

promote:
	cp $(OBJS) $(OBJS:.cmo=.cmi) $(TOP)/boot/.

compare:
	@for j in $(OBJS) $(OBJS:.cmo=.cmi); do \
		if cmp $$j $(TOP)/boot/$$j; then :; else exit 1; fi; \
	done

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)"
	cp $(TARGET) *.mli "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp *.cmi "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	if test -f $(TARGET:.cma=.cmxa); then \
	  $(MAKE) installopt LIBDIR="$(LIBDIR)" DESTDIR=$(DESTDIR); \
	fi

installopt:
	cp $(TARGET:.cma=.cmxa) *.cmx "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	if test -f $(TARGET:.cma=.lib); then \
	  cp $(TARGET:.cma=.lib) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	else \
	  tar cf - $(TARGET:.cma="")$(EXT_LIB) | \
	  (cd "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; tar xf -); \
	fi

include .depend
