# $Id: Makefile,v 1.3 2007/07/12 09:18:35 deraugla Exp $

# $Id: Makefile,v 1.3 2007/07/12 09:18:35 deraugla Exp $

OBJS=../html/index.html ../html/extfun.html ../html/lexers.html ../html/opretty.html ../html/pragma.html ../html/fparsers.html ../html/ml_ast.html ../html/parsers.html ../html/pretty.html
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
