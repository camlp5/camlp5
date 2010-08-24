# $Id: Makefile.tpl,v 1.11 2010/08/24 15:26:53 deraugla Exp $

CAMLP5_COMM=OPT=$(OPT) EXE=$(EXE) MODE=$(MODE) COMPWITH=$(COMPWITH) ../tools/camlp5_comm.sh
OCAMLC=@OPT=$(OPT) EXE=$(EXE) ../tools/ocamlc.sh
OCAMLOPT=@OPT=$(OPT) EXE=$(EXE) ../tools/ocamlopt.sh
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
