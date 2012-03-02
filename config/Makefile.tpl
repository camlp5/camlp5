# $Id: Makefile.tpl,v 6.4 2012/03/02 18:49:56 deraugla Exp $

CAMLP5_COMM=OPT=$(OPT) EXE=$(EXE) OCAMLN=$(OCAMLN) MODE=$(MODE) COMPWITH=$(COMPWITH) CAMLP5N=$(CAMLP5N) ../tools/camlp5_comm.sh
OCAMLC=@OPT=$(OPT) EXE=$(EXE) OCAMLN=$(OCAMLN) ../tools/ocamlc.sh
OCAMLOPT=@OPT=$(OPT) EXE=$(EXE) OCAMLN=$(OCAMLN) ../tools/ocamlopt.sh
OCAMLCFLAGS=
MKDIR=mkdir -p
TEST_DIR=test `basename "$<"` = "$<" || { echo "File \"$<\" needs to be recompiled."; echo "Please run 'make' in directory '$$(dirname "$<")' first."; exit 1; }
COMPWITH=old

.SUFFIXES: .cmx .cmo .cmi .ml .mli

.mli.cmi:
	@$(TEST_DIR)
	@$(CAMLP5_COMM) $< -o $*.ppi
	$(OCAMLC) $(OCAMLCFLAGS) -c -intf $*.ppi
	rm -f $*.ppi

.ml.cmo:
	@$(TEST_DIR)
	@$(CAMLP5_COMM) $< -o $*.ppo
	$(OCAMLC) $(OCAMLCFLAGS) -c -impl $*.ppo
	rm -f $*.ppo

.ml.cmx:
	@$(TEST_DIR)
	@$(CAMLP5_COMM) $< -o $*.ppo
	$(OCAMLOPT) $(OCAMLCFLAGS) -c -impl $*.ppo
	rm -f $*.ppo
