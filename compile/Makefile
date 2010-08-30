# $Id: Makefile,v 1.23 2010/08/29 23:59:53 deraugla Exp $

TOP=..
include ../config/Makefile

INCLUDES=-I ../main -I ../boot
OCAMLCFLAGS=$(OCAMLC_W_Y) $(WARNERR) $(INCLUDES)
SRC=../etc/pa_o.ml ../etc/pa_op.ml
D=o
COMP_OPT=-strict_parsing
COMP_OPT=-e "Grammar.Entry.obj Pcaml.interf" -e "Grammar.Entry.obj Pcaml.implem" -e "Grammar.Entry.obj Pcaml.top_phrase" -e "Grammar.Entry.obj Pcaml.use_file"

all: out

out: camlp5$D.fast
opt: camlp5$D.fast.opt

camlp5$D.fast: pa_$D_fast.cmo
	rm -f camlp5$D.fast
	cd ../main; $(MAKE) CAMLP5=../compile/camlp5$D.fast CAMLP5M="../compile/pa_$D_fast.cmo ../meta/pr_dump.cmo"

camlp5$D.fast.opt: pa_$D_fast.cmx
	rm -f camlp5$D.fast.opt
	cd ../main; $(MAKE) optp5 CAMLP5OPT=../compile/camlp5$D.fast.opt CAMLP5M="../compile/pa_$D_fast.cmx ../meta/pr_dump.cmx"

pa_$D_fast.ml: comp_head.ml.tpl $D_fast.ml.tmp comp_trail.ml.tpl
	cat $(SRC) | sed -e "s/Plexer.gmake ()/P.lexer/" -e "/EXTEND/,/END/d" -e "/Grammar.Entry.of_parser/d" -e "/Grammar.Entry.gcreate/d" -e "/Grammar.Entry.create/d" | grep -v '#load' | cat comp_head.ml.tpl - $D_fast.ml.tmp comp_trail.ml.tpl > pa_$D_fast.ml

$D_fast.ml.tmp: compile.cmo $(SRC)
	EXE=$(EXE) ./compile.sh $(COMP_OPT) $(SRC) > $D_fast.ml.tmp

install:
	if test -f camlp5o.fast.opt; then \
	  cp camlp5o.fast.opt "$(DESTDIR)$(BINDIR)/camlp5o.opt"; \
	fi
	if test -f pa_o_fast.cmx; then \
	  cp pa_o_fast.cmx pa_o_fast.o "$(DESTDIR)$(LIBDIR)/camlp5/."; \
	fi

clean::
	rm -f *.cm* *.pp[io] *.[oa] *.lib *.obj *.bak .*.bak *.out *.opt
	rm -f *.fast tmp.* pa_*_fast.ml *_fast.ml.tmp

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in *.ml; do \
	  ../tools/depend.sh $(INCLUDES) $$i | \
	  sed -e 's| $(OTOP)| $$(OTOP)|g' >> .depend; \
	done

include .depend
