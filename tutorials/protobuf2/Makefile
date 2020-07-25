
OCAMLFIND=ocamlfind
NOT_OCAMLFIND=not-ocamlfind
PACKAGES=fmt,camlp5.extprint,camlp5.extend,camlp5.pa_lexer,camlp5.pprintf,pcre

all: pb0 pb0.opt

pb0: clexer.cmo pb0.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

pb0.opt: clexer.cmx pb0.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

.SUFFIXES: .ml .cmo .cmx

pb0.cmo: pb0.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

pb0.cmx: pb0.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

clexer.cmo: clexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

clexer.cmx: clexer.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

test:

clean:
	rm -f calc calc.opt *.cm* *.o *.ppo.ml

depend::
	$(OCAMLFIND) ocamldep $(DEBUG) -package $(PACKAGES) -syntax camlp5r clexer.ml calc.ml >> .depend.NEW \
		&& mv .depend.NEW .depend

-include .depend
