# $Id: Makefile,v 1.17 2007/08/16 16:38:54 deraugla Exp $

OBJS=../html/index.html ../html/extfun.html ../html/fparsers.html ../html/grammars.html ../html/lexers.html ../html/locations.html ../html/macros.html ../html/ml_ast.html ../html/opretty.html ../html/parsers.html ../html/pcaml.html ../html/pragma.html ../html/pretty.html ../html/printers.html ../html/ptools.html ../html/quot.html ../html/revsynt.html ../html/scheme.html ../html/sources.html ../html/syntext.html

INDEX=index.html

all: $(OBJS)

clean:
	rm -f $(OBJS)

../html/%.html: %.html menu.html trailer.html
	@rm -f $@
	./htmlp2html $< > $@
	@chmod 444 $@
