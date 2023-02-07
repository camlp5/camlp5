TOP=..
include $(TOP)/config/Makefile

OCAMLFIND=ocamlfind
NOT_OCAMLFIND=not-ocamlfind
YAWRAP=ocamlfind camlp5-buildscripts/ya-wrap-ocamlfind
PACKAGES=pa_ppx_regexp,camlp5,bos,fmt,ocaml-version

EXE=bin/mkcamlp5 bin/mkcamlp5.opt

all: $(EXE)

bootstrap:: all
	$(LAUNCH) $(YAWRAP) $(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.pr_o mkcamlp5.ml > $(TOP)/etc/mkcamlp5.ml

test: all mkcamlp5_test.asciidoc.TEST

alt-test:
	SCRIPTDIR=bin/ $(LAUNCH) ocaml-mdx test -o mkcamlp5_test.asciidoc.camlp5.corrected mkcamlp5_test.asciidoc
	diff -Bwiu  mkcamlp5_test.asciidoc.camlp5.corrected mkcamlp5_test.asciidoc

bin/mkcamlp5 bin/mkcamlp5.opt: mkcamlp5.cmo
	mkdir -p bin
	$(LAUNCH) $(OCAMLFIND) ocamlc -linkall -linkpkg -package $(PACKAGES) $^ -o $@
	cp bin/mkcamlp5 bin/mkcamlp5.opt

toplevel::
	$(LAUNCH) ocaml -nopromptcont

.SUFFIXES: .ml .cmo .cmi .cmx

.ml.cmo:
#	$(LAUNCH) $(YAWRAP) $(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(PACKAGES),$(PRPACKAGE) $< > $*_ppo.ml
#	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5o -c $*_ppo.ml
	$(LAUNCH) $(YAWRAP) $(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) -package $(PACKAGES) -c $<

clean::
	rm -f *.cm* $(EXE) *.corrected *.o link*

