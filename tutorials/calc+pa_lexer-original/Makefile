
OCAMLFIND=ocamlfind
NOT_OCAMLFIND=not-ocamlfind
PACKAGES=fmt,camlp5.extprint,camlp5.extend,camlp5.pa_lexer,camlp5.pprintf,pcre

all: calc calc.opt

calc: calc.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5o $^ -o $@

calc.opt: calc.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5o $^ -o $@

.SUFFIXES: .ml .cmo .cmx

calc.cmo: calc.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_r -syntax camlp5o $< > calc.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

calc.cmx: calc.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

test:: all
	echo '1+1 ; 1 - 1; 1 + (2 * 3)' | ./calc

clean:
	rm -f calc calc.opt *.cm* *.o *.ppo.ml

