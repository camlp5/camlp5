# Makefile,v

TOP=../..
include $(TOP)/config/Makefile

SHELL=/bin/sh

INCLUDES=
OCAMLCFLAGS=$(WARNERR) $(INCLUDES)
LINKFLAGS=$(INCLUDES)

OBJS=odyl_config.cmo odyl_main.cmo

all: odyl$(EXE)

opt: odyl.cmxa odyl.cmx

odyl$(EXE): odyl.cma odyl.cmo
	$(OCAMLC) odyl.cma odyl.cmo -o odyl$(EXE)

odyl.cma: $(OBJS)
	$(OCAMLC) $(LINKFLAGS) dynlink.cma $(OBJS) -a -o odyl.cma

odyl.cmxa: $(OBJS:.cmo=.cmx)
	$(OCAMLOPT) $(LINKFLAGS) $(OBJS:.cmo=.cmx) -a -o odyl.cmxa

odyl_main.cmx: odyl_main.ml
	$(CAMLP5_COMM) -DOPT -o odyl_main.ppo odyl_main.ml
	$(OCAMLOPT) -c -impl odyl_main.ppo
	$(RM) -f odyl_main.ppo

odyl_config.ml:
	echo "let standard_library =" > odyl_config.ml
	echo "  try Sys.getenv \"CAMLP5LIB\" with" >> odyl_config.ml
	echo "    Not_found -> \"$(LIBDIR)/$(CAMLP5N)\"" | \
	sed -e 's|\\|/|g' >> odyl_config.ml

clean::
	$(RM) -f *.cm* *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak *.out *.opt
	$(RM) -f odyl_config.ml odyl$(EXE)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  ../tools/depend.sh $(INCLUDES) -name $(CAMLP5N) $$i \
	  >> .depend; \
	done

promote:

compare:

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)" "$(DESTDIR)$(BINDIR)"
	cp odyl.cmo odyl.cma "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	if test -f odyl.cmxa; then \
	  cp odyl.cmxa odyl.cmx "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	  cp odyl$(EXT_LIB) odyl$(EXT_OBJ) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	fi

include .depend
