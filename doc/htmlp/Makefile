# $Id: Makefile,v 1.4 2007/07/12 17:52:21 deraugla Exp $

# $Id: Makefile,v 1.4 2007/07/12 17:52:21 deraugla Exp $

OBJS=../html/index.html ../html/extfun.html ../html/fparsers.html ../html/lexers.html ../html/ml_ast.html ../html/opretty.html ../html/parsers.html ../html/patools.html ../html/pragma.html ../html/pretty.html

INDEX=index.html

all: $(OBJS)

clean:
	rm -f $(OBJS)

../html/%.html: %.html menu.html
	@rm -f $@
	@(sed -e '/<div id="menu">/,$$d' $<; \
	 sed 's/index.html/$(INDEX)/' menu.html; \
	 sed -e '1,/<\/div>/d' $<) > tmp
	@mv tmp $@
	@chmod 444 $@
	@echo $@ done
