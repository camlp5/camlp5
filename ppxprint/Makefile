# Makefile,v

TOP=..
include ../config/Makefile

FMTDIR=$(shell ocamlfind query fmt)
INCLUDES=-I ../main -I ../boot
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES) -I $(FMTDIR) -I "$(OCLIBDIR)" -I $(OTOPU) -I $(OTOPP)

NOT_OCAMLFIND=not-ocamlfind
PREPROCESS_PACKAGES := unix,compiler-libs.common,camlp5.quotations,camlp5.extfun,rresult,fmt

CMO=ppxprint_runtime.cmo pp_MLast.cmo pp_parsetree.cmo
CMI=$(CMO:.cmo=.cmi)
OBJ=$(CMO)

TARGET=ppxprint.cma

all: $(TARGET)

ppxprint.cma: $(OBJ)
	$(OCAMLC) $(OBJ) $(DEBUG) -linkall -a -o ppxprint.cma

bootstrap: bootstrap-pp-MLast-i bootstrap-pp-MLast bootstrap-pp-parsetree-i bootstrap-pp-parsetree

initialize-pp-MLast-i:: pp_MLast.ORIG.mli
	echo "(* camlp5r *)" > $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW pp_MLast.mli

bootstrap-pp-MLast-i: pp_MLast.ORIG.mli
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  pp_MLast.mli

initialize-pp-MLast:: pp_MLast.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW pp_MLast.ml

bootstrap-pp-MLast: pp_MLast.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  pp_MLast.ml

initialize-pp-parsetree-i:: pp_parsetree.ORIG.mli
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW pp_parsetree.mli

bootstrap-pp-parsetree-i: pp_parsetree.ORIG.mli
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  pp_parsetree.mli

initialize-pp-parsetree:: pp_parsetree.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW pp_parsetree.ml

bootstrap-pp-parsetree: pp_parsetree.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  pp_parsetree.ml

clean::
	$(RM) -f *.cm[ioa] *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak $(TARGET)

pp_MLast.cmo: pp_MLast.cmi ppxprint_runtime.cmo
pp_parsetree.cmo: pp_parsetree.cmi ppxprint_runtime.cmo

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)"
	cp $(TARGET) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp $(CMI) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."

