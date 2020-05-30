# Makefile.tpl,v

NOVERBOSE=@
CAMLP5_COMM=OPT=$(OPT) EXE=$(EXE) OCAMLN=$(OCAMLN) MODE=$(MODE) COMPWITH=$(COMPWITH) CAMLP5N=$(CAMLP5N) ../tools/camlp5_comm.sh
OCAMLC=@OPT=$(OPT) EXE=$(EXE) OCAMLN=$(OCAMLN) ../tools/ocamlc.sh
OCAMLOPT=@OPT=$(OPT) EXE=$(EXE) OCAMLN=$(OCAMLN) ../tools/ocamlopt.sh
DEBUG=
OCAMLCFLAGS=$(DEBUG)
MKDIR=mkdir -p
RM=rm
TEST_DIR=test `basename "$<"` = "$<" || { echo "File \"$<\" needs to be recompiled."; echo "Please run 'make' in directory '$$(dirname "$<")' first."; exit 1; }
COMPWITH=old

.SUFFIXES: .cmx .cmo .cmi .ml .mli

.mli.cmi:
	$(NOVERBOSE) $(TEST_DIR)
	$(NOVERBOSE) $(CAMLP5_COMM) $< -o $*.ppi
	$(OCAMLC) $(OCAMLCFLAGS) -c -intf $*.ppi
	$(RM) -f $*.ppi

.ml.cmo:
	$(NOVERBOSE) $(TEST_DIR)
	$(NOVERBOSE) $(CAMLP5_COMM) $< -o $*.ppo
	$(OCAMLC) $(OCAMLCFLAGS) -c -impl $*.ppo
	$(RM) -f $*.ppo

.ml.cmx:
	$(NOVERBOSE) $(TEST_DIR)
	$(NOVERBOSE) $(CAMLP5_COMM) $< -o $*.ppo
	$(OCAMLOPT) $(OCAMLCFLAGS) -c -impl $*.ppo
	$(RM) -f $*.ppo
