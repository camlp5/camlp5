TOP=..
include $(TOP)/config/Makefile

OCAMLFIND=ocamlfind
YAWRAP=ocamlfind camlp5-buildscripts/ya-wrap-ocamlfind
PACKAGES=pa_ppx_regexp,camlp5,bos,fmt,ocaml-version

EXE=bin/mkcamlp5 bin/mkcamlp5.opt

all: $(EXE)

test: all mkcamlp5_test.asciidoc.TEST

alt-test:
	SCRIPTDIR=bin/ $(LAUNCH) ocaml-mdx test -o mkcamlp5_test.asciidoc.camlp5.corrected mkcamlp5_test.asciidoc

bin/mkcamlp5: mkcamlp5.cmo
	mkdir -p bin
	$(LAUNCH) $(OCAMLFIND) ocamlc -linkall -linkpkg -package $(PACKAGES) $^ -o $@

bin/mkcamlp5.opt: mkcamlp5.cmx
	mkdir -p bin
	$(LAUNCH) $(OCAMLFIND) ocamlopt -linkall -linkpkg -package $(PACKAGES) $^ -o $@

toplevel::
	$(LAUNCH) ocaml -nopromptcont

.SUFFIXES: .ml .cmo .cmi .cmx

.ml.cmo:
#	$(LAUNCH) $(YAWRAP) $(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(PACKAGES),$(PRPACKAGE) $< > $*_ppo.ml
#	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5o -c $*_ppo.ml
	$(LAUNCH) $(YAWRAP) $(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) -package $(PACKAGES) -c $<

.ml.cmx:
	$(LAUNCH) $(YAWRAP) $(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) -package $(PACKAGES) -c $<

clean::
	rm -f *.cm* $(EXE) *.corrected

