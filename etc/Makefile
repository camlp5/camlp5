# Makefile,v

include ../config/Makefile

INCLUDES=-I ../main -I ../boot -I ../lib -I ../meta
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)
OTHERLANGS=pa_sml.cmo pa_lisp.cmo pa_scheme.cmo pa_schemer.cmo pa_lefteval.cmo  pr_scheme.cmo pr_schemep.cmo
OBJS=pa_o.cmo pa_op.cmo pa_oop.cmo pa_extfold.cmo pa_extfun.cmo pa_extprint.cmo pa_macro_print.cmo pa_mkast.cmo pa_mktest.cmo pa_pprintf.cmo pa_pragma.cmo pa_reloc.cmo r_keywords.cmo pr_r.cmo pr_ro.cmo pr_rp.cmo o_keywords.cmo pr_o.cmo pr_op.cmo pr_extend.cmo pr_extfun.cmo pr_extprint.cmo pr_depend.cmo pr_null.cmo q_phony.cmo  papr_phony_macro.cmo pr_official.cmo  $(OTHERLANGS)
INSTALL_CMI=pr_o.cmi pr_r.cmi
CAMLP5OM=pa_o.cmo pa_op.cmo ../meta/pr_dump.cmo
CAMLP5SCHM=pa_scheme.cmo ../meta/pr_dump.cmo
CAMLP5OMX=pa_o.cmx pa_op.cmx ../meta/pr_dump.cmx
SHELL=/bin/bash
OTHEROUT=$(CAMLP5N)sch$(EXE)
COUT=$(OBJS) $(CAMLP5N)o$(EXE) $(OTHEROUT)
COPT=$(OBJS:.cmo=.cmx) $(CAMLP5N)o.opt$(EXE)

all: $(COUT) META mkcamlp5$(EXE)
opt: $(COPT)

mkcamlp5$(EXE): mkcamlp5.cmo
	ocamlfind ocamlc -linkall -linkpkg -package bos,re,pcre2,rresult mkcamlp5.ml -o $@

# these ones must be compiled with new created camlp5:

pa_lisp.cmo pa_lisp.cmx: pa_lisp.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pa_scheme.cmo pa_scheme.cmx: pa_scheme.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pa_extfold.cmo pa_extfold.cmx: pa_extfold.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_r.cmo pr_r.cmx: pr_r.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_ro.cmo pr_ro.cmx: pr_ro.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_rp.cmo pr_rp.cmx: pr_rp.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_o.cmo pr_o.cmx: pr_o.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_op.cmo pr_op.cmx: pr_op.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_scheme.cmo pr_scheme.cmx: pr_scheme.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_schemep.cmo pr_schemep.cmx: pr_schemep.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_extend.cmo pr_extend.cmx: pr_extend.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_extfun.cmo pr_extfun.cmx: pr_extfun.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_extprint.cmo pr_extprint.cmx: pr_extprint.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
q_phony.cmo q_phony.cmx: q_phony.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
papr_phony_macro.cmo papr_phony_macro.cmx: papr_phony_macro.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@
pr_official.cmo pr_official.cmx: pr_official.ml
	$(MAKE) $(NO_PR_DIR) -f Makefile.withnew $@

META:: META.pl
	OVERSION=$(OVERSION) VERSION=$(VERSION) CAMLP5N="$(CAMLP5N)" ./META.pl > META

$(CAMLP5N)o$(EXE): ../main/$(CAMLP5N)$(EXE) $(CAMLP5OM)
	$(RM) -f $@
	cd ../main; $(MAKE) CAMLP5=../etc/$@ CAMLP5M="-I ../etc $(CAMLP5OM)"

$(CAMLP5N)sch$(EXE): ../main/$(CAMLP5N)$(EXE) $(CAMLP5SCHM)
	$(RM) -f $@
	cd ../main; $(MAKE) CAMLP5=../etc/$@ CAMLP5M="-I ../etc $(CAMLP5SCHM)"

$(CAMLP5N)o.opt$(EXE): $(CAMLP5OMX)
	$(RM) -f $@
	cd ../main; $(MAKE) optp5 CAMLP5OPT=../etc/$@ CAMLP5M="-I ../etc $(CAMLP5OMX)"

bootstrap_scheme:
	@$(MAKE) $(NO_PR_DIR) bootstrap_l L=scheme
compare_scheme:
	@$(MAKE) $(NO_PR_DIR) compare_l L=scheme
bootstrap_lisp:
	@$(MAKE) $(NO_PR_DIR) bootstrap_l L=lisp
compare_lisp:
	@$(MAKE) $(NO_PR_DIR) compare_l L=lisp

bootstrap_l:
	ocamlrun$(EXE) ../boot/$(CAMLP5N) ./pa_$Lr.cmo -I ../boot pa_extend.cmo ./pr_r.cmo ./pr_extend.cmo ./pr_rp.cmo ./q_phony.cmo pa_$L.ml > tmp
	mv pa_$Lr.ml pa_$Lr.ml.old
	sed -e 's/^;; \(.*\)$$/(* \1 *)/' -e 's/^; \(.*\)$$/(* \1 *)/' -e 's|./pa_$Lr.cmo|pa_r.cmo pa_rp.cmo|' -e 's/$$Id.*\$$/File generated by pretty print; do not edit!/' tmp > pa_$Lr.ml
	$(RM) -f tmp

compare_l:
	ocamlrun$(EXE) ../boot/$(CAMLP5N) ./pa_$Lr.cmo -I ../boot pa_extend.cmo ./pr_r.cmo ./pr_extend.cmo ./pr_rp.cmo ./q_phony.cmo pa_$L.ml | sed -e 's/^;; \(.*\)$$/(* \1 *)/' -e 's/^; \(.*\)$$/(* \1 *)/' -e 's|./pa_$Lr.cmo|pa_r.cmo pa_rp.cmo|' -e 's/$$Id.*\$$/File generated by pretty print; do not edit!/' | diff -Bwiu pa_$Lr.ml -

clean::
	$(RM) -f *.cm* *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak *.out *.opt$(EXE)
	$(RM) -f $(CAMLP5N)o$(EXE) $(CAMLP5N)sch$(EXE) mkcamlp5$(EXE)
	$(RM) -f META

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  ../tools/depend.sh $(INCLUDES) -name $(CAMLP5N) $$i \
	  >> .depend; \
	done

get_promote:

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)" "$(DESTDIR)$(BINDIR)"
	$(RM) -f "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/pa_lex.cmo"
	cp $(OBJS) $(INSTALL_CMI) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	OVERSION=$(OVERSION) VERSION=$(VERSION) CAMLP5N="$(CAMLP5N)" ./META.pl > META
	cp META "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp lib.sml "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp $(CAMLP5N)o$(EXE) $(CAMLP5N)sch$(EXE) "$(DESTDIR)$(BINDIR)/."
	cp mk$(CAMLP5N) "$(DESTDIR)$(BINDIR)/mk$(CAMLP5N)"
	chmod a+x "$(DESTDIR)$(BINDIR)/mk$(CAMLP5N)"
	if test -f pa_o.cmx; then \
	  cp $(OBJS:.cmo=.cmx) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	  for i in $(OBJS:.cmo=); do \
	    cp $$i$(EXT_OBJ) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	  done; \
	  cp $(CAMLP5N)o.opt "$(DESTDIR)$(BINDIR)/."; \
	  cp mk$(CAMLP5N) "$(DESTDIR)$(BINDIR)/mk$(CAMLP5N).opt"; \
	  chmod a+x "$(DESTDIR)$(BINDIR)/mk$(CAMLP5N).opt"; \
	fi

pa_lisp.cmo: pa_lispr.cmo
pa_scheme.cmo: pa_schemer.cmo
pr_extend.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
pr_extfun.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
pr_extprint.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
pr_o.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo pa_macro_print.cmo
pr_op.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
pr_r.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo pa_macro_print.cmo
pr_ro.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
pr_rp.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
pr_scheme.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
pr_schemep.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
q_phony.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo
papr_phony_macro.cmo: pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo

include .depend
