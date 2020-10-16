# Makefile,v

TOP=..
include ../config/Makefile

INCLUDES=-I ../main -I ../boot -I ../lib
OCAMLCFLAGS=$(DEBUG) $(OCAMLC_W_Y) $(WARNERR) $(INCLUDES)
D=o
SRC=../etc/pa_$(D).ml ../etc/pa_$(D)p.ml
COMP_OPT=-strict_parsing
COMP_OPT=-e "Grammar.Entry.obj Pcaml.interf" \
         -e "Grammar.Entry.obj Pcaml.implem" \
         -e "Grammar.Entry.obj Pcaml.top_phrase" \
         -e "Grammar.Entry.obj Pcaml.use_file" \


RM=rm

all: out

out: $(CAMLP5N)$D.fast
opt: $(CAMLP5N)$D.fast.opt

$(CAMLP5N)$D.fast: pa_$D_fast.cmo
	$(RM) -f $(CAMLP5N)$D.fast
	cd ../main; $(MAKE) CAMLP5=../compile/$(CAMLP5N)$D.fast CAMLP5M="../compile/pa_$D_fast.cmo ../meta/pr_dump.cmo"

$(CAMLP5N)$D.fast.opt: pa_$D_fast.cmx
	$(RM) -f $(CAMLP5N)$D.fast.opt
	cd ../main; $(MAKE) optp5 CAMLP5OPT=../compile/$(CAMLP5N)$D.fast.opt CAMLP5M="../compile/pa_$D_fast.cmx ../meta/pr_dump.cmx"

pa_$D_fast.ml: compile.cmo comp_head.ml.tpl comp_trail.ml.tpl $(SRC)
	cat $(SRC) | perl -n -e 'print unless /#load/' > tmp.$D_concat.ml
	../meta/camlp5r -I ../meta -I ../etc pa_extend.cmo q_MLast.cmo pa_macro.cmo pa_macro_gram.cmo pr_r.cmo pr_ro.cmo pr_extend.cmo tmp.$D_concat.ml > tmp.$D_postprocessed.ml.ppo.TMP && mv tmp.$D_postprocessed.ml.ppo.TMP tmp.$D_postprocessed.ml.ppo
	./strip-parser.pl tmp.$D_postprocessed.ml.ppo > $D_stripped.tmp
	OCAMLN=$(OCAMLN) CAMLP5N=$(CAMLP5N) EXE=$(EXE) RM=$(RM) ./compile.sh $(COMP_OPT) $(SRC) > $D_fast.ml.tmp
	cat comp_head.ml.tpl $D_stripped.tmp $D_fast.ml.tmp comp_trail.ml.tpl > pa_$D_fast.ml

install:
	if test -f $(CAMLP5N)o.fast.opt; then \
	  cp $(CAMLP5N)o.fast.opt "$(DESTDIR)$(BINDIR)/$(CAMLP5N)o.opt"; \
	fi
	if test -f pa_o_fast.cmx; then \
	  cp pa_o_fast.cmx pa_o_fast.o "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	fi

clean::
	$(RM) -f *.cm* *.pp[io] *.[oa] *.lib *.obj *.bak .*.bak *.out *.opt
	$(RM) -f *.fast tmp.* pa_*_fast.ml *.tmp *.ppo

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in *.ml; do \
	  ../tools/depend.sh $(INCLUDES) -name $(CAMLP5N) $$i \
	  >> .depend; \
	done

include .depend
