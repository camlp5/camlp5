# $Id: Makefile,v 1.8 2007/07/16 01:39:50 deraugla Exp $

# $Id: Makefile,v 1.8 2007/07/16 01:39:50 deraugla Exp $

OBJS=../html/index.html ../html/extfun.html ../html/fparsers.html ../html/grammars.html ../html/lexers.html ../html/ml_ast.html ../html/opretty.html ../html/parsers.html ../html/pragma.html ../html/pretty.html ../html/ptools.html

INDEX=index.html

all: $(OBJS)

clean:
	rm -f $(OBJS)

../html/%.html: %.html menu.html trailer.html
	@rm -f $@
	./htmlp2html $< > $@
	@chmod 444 $@
