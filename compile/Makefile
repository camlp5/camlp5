# Makefile,v

TOP=..
include ../config/Makefile

INCLUDES=-I ../main -I ../boot -I ../lib
OCAMLCFLAGS=$(OCAMLC_W_Y) $(WARNERR) $(INCLUDES)
SRC=../etc/pa_o.ml ../etc/pa_op.ml
D=o
COMP_OPT=-strict_parsing
COMP_OPT=-e "Grammar.Entry.obj Pcaml.interf" -e "Grammar.Entry.obj Pcaml.implem" -e "Grammar.Entry.obj Pcaml.top_phrase" -e "Grammar.Entry.obj Pcaml.use_file"

all: out

out: $(CAMLP5N)$D.fast
opt: $(CAMLP5N)$D.fast.opt

$(CAMLP5N)$D.fast: pa_$D_fast.cmo
	$(RM) -f $(CAMLP5N)$D.fast
	cd ../main; $(MAKE) CAMLP5=../compile/$(CAMLP5N)$D.fast CAMLP5M="../compile/pa_$D_fast.cmo ../meta/pr_dump.cmo"

$(CAMLP5N)$D.fast.opt: pa_$D_fast.cmx
	$(RM) -f $(CAMLP5N)$D.fast.opt
	cd ../main; $(MAKE) optp5 CAMLP5OPT=../compile/$(CAMLP5N)$D.fast.opt CAMLP5M="../compile/pa_$D_fast.cmx ../meta/pr_dump.cmx"

pa_$D_fast.ml: comp_head.ml.tpl $D_fast.ml.tmp comp_trail.ml.tpl
	cat $(SRC) | sed -e "s/Plexer.gmake ()/Lazy.force P.lexer/" -e "/EXTEND/,/END/d" -e "/Grammar.Entry.of_parser/d" -e "/Grammar.Entry.gcreate/d" -e "/Grammar.Entry.create/d" | grep -v '#load' | grep -v "^IFDEF" | grep -v "^END" | grep -v DELETE_RULE | cat comp_head.ml.tpl - $D_fast.ml.tmp comp_trail.ml.tpl > pa_$D_fast.ml

$D_fast.ml.tmp: compile.cmo $(SRC)
	OCAMLN=$(OCAMLN) CAMLP5N=$(CAMLP5N) EXE=$(EXE) ./compile.sh $(COMP_OPT)  $(SRC) > $D_fast.ml.tmp

install:
	if test -f $(CAMLP5N)o.fast.opt; then \
	  cp $(CAMLP5N)o.fast.opt "$(DESTDIR)$(BINDIR)/$(CAMLP5N)o.opt"; \
	fi
	if test -f pa_o_fast.cmx; then \
	  cp pa_o_fast.cmx pa_o_fast.o "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	fi

clean::
	$(RM) -f *.cm* *.pp[io] *.[oa] *.lib *.obj *.bak .*.bak *.out *.opt
	$(RM) -f *.fast tmp.* pa_*_fast.ml *_fast.ml.tmp

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in *.ml; do \
	  ../tools/depend.sh $(INCLUDES) -name $(CAMLP5N) $$i \
	  >> .depend; \
	done

include .depend
