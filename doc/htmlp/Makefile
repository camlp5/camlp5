# Makefile,v

H=../html
OBJS=$H/index.html $H/about.html $H/ast_strict.html $H/ast_transi.html $H/bparsers.html $H/commands.html $H/conclusion.html $H/directives.html $H/extfun.html $H/fparsers.html $H/grammars.html $H/lexers.html $H/library.html $H/locations.html $H/macros.html $H/ml_ast.html $H/opretty.html $H/parsers.html $H/pcaml.html $H/pprintf.html $H/pragma.html $H/pretty.html $H/printers.html $H/ptools.html $H/q_ast.html $H/quot.html $H/redef.html $H/revsynt.html $H/scheme.html $H/sources.html $H/strict.html $H/syntext.html
RSS=$H/rss/camlp5.rss
INDEX=index.html
NO_PR_DIR=--no-print-directory

all: $(OBJS) $(RSS)

info:
	@$(MAKE) $(NO_PR_DIR) camlp5.info H=.

tex:
	@$(MAKE) $(NO_PR_DIR) camlp5.dvi H=.

ps:
	@$(MAKE) $(NO_PR_DIR) camlp5.ps H=.

pdf:
	@$(MAKE) $(NO_PR_DIR) camlp5.pdf H=.

camlp5.info: html2texi $(OBJS)
	./html2texi > camlp5.texi
	makeinfo --force camlp5.texi

camlp5.dvi: camlp5.tex
	latex camlp5.tex
	latex camlp5.tex
	latex camlp5.tex

camlp5.tex: html2latex $(OBJS)
	./html2latex > camlp5.tex

camlp5.ps: camlp5.dvi
	dvips -f- camlp5.dvi > camlp5.ps

camlp5.pdf: camlp5.tex
	pdflatex camlp5.tex

clean:
	rm -f $(OBJS) $(RSS)
	rm -f camlp5.texi camlp5.info* camlp5.ps
	rm -f camlp5.tex camlp5.dvi camlp5.log camlp5.toc camlp5.aux

../html/%.html: %.html menu.html trailer.html
	@mkdir -p ../html
	@rm -f $@
	./htmlp2html $< > $@
	@chmod 444 $@

../html/rss/%.rss: %.rss
	@mkdir -p ../html/rss
	@rm -f $@
	cp $< $@
	@chmod 444 $@
