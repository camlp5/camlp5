# $Id: Makefile.tpl,v 1.4 2007/07/10 14:09:06 deraugla Exp $

CAMLP4_COMM=OTOP=$(OTOP) NAME=$(NAME) OPT=$(OPT) EXE=$(EXE) ../tools/camlp4_comm.sh
OCAMLC=@OTOP=$(OTOP) OPT=$(OPT) EXE=$(EXE) ../tools/ocamlc.sh
OCAMLOPT=@OTOP=$(OTOP) OPT=$(OPT) EXE=$(EXE) ../tools/ocamlopt.sh
OCAMLCFLAGS=
MKDIR=mkdir -p
TEST_DIR=test `basename "$<"` = "$<" || { echo "Please run 'make' in directory '$$(dirname "$<")' first"; exit 1; }

.SUFFIXES: .cmx .cmo .cmi .ml .mli

.mli.cmi:
	@$(TEST_DIR)
	@$(CAMLP4_COMM) $< -o $*.ppi
	$(OCAMLC) $(OCAMLCFLAGS) -c -intf $*.ppi
	rm -f $*.ppi

.ml.cmo:
	@$(TEST_DIR)
	@$(CAMLP4_COMM) $< -o $*.ppo
	$(OCAMLC) $(OCAMLCFLAGS) -c -impl $*.ppo
	rm -f $*.ppo

.ml.cmx:
	@$(TEST_DIR)
	@$(CAMLP4_COMM) $< -o $*.ppo
	$(OCAMLOPT) $(OCAMLCFLAGS) -c -impl $*.ppo
	rm -f $*.ppo

