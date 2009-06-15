# $Id: Makefile,v 1.12 2007/07/26 08:34:12 deraugla Exp $

OBJS=../html/index.html ../html/extfun.html ../html/fparsers.html ../html/grammars.html ../html/lexers.html ../html/locations.html ../html/ml_ast.html ../html/opretty.html ../html/parsers.html ../html/pragma.html ../html/pretty.html ../html/ptools.html ../html/quot.html ../html/revsynt.html ../html/syntext.html

INDEX=index.html

all: $(OBJS)

clean:
	rm -f $(OBJS)

../html/%.html: %.html menu.html trailer.html
	@rm -f $@
	./htmlp2html $< > $@
	@chmod 444 $@
