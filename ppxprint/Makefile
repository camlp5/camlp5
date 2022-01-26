# Makefile,v

TOP=..
include ../config/Makefile


ifeq ($(BOOTSTRAPPED),1)
FMTDIR=$(shell ocamlfind query fmt)
FMTINCLUDES=-I $(FMTDIR)
else
FMTINCLUDES=
endif
INCLUDES=-I ../main -I ../boot
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES) $(FMTINCLUDES)

NOT_OCAMLFIND=not-ocamlfind
PREPROCESS_PACKAGES := unix,compiler-libs.common,camlp5.quotations,camlp5.extfun,rresult,fmt

CMO=ppxprint_runtime.cmo exceptions.cmo pp_MLast.cmo pp_parsetree.cmo pp_outcometree.cmo
CMI=$(CMO:.cmo=.cmi)
CMX=$(CMO:.cmo=.cmx)
OBJ=$(CMO)

TARGET=ppxprint.cma

all: $(TARGET)
opt: $(TARGET:.cma=.cmxa)

ppxprint.cma: $(CMO)
	$(OCAMLC) $(CMO) $(DEBUG) -linkall -a -o ppxprint.cma

ppxprint.cmxa: $(CMX)
	$(OCAMLOPT) $(CMX) $(DEBUG) -linkall -a -o ppxprint.cmxa

bootstrap: bootstrap-ppxprint-runtime \
	bootstrap-pp-MLast-i bootstrap-pp-MLast \
	bootstrap-exceptions-i bootstrap-exceptions \
	bootstrap-pp-parsetree-i bootstrap-pp-parsetree \
	bootstrap-pp-outcometree-i bootstrap-pp-outcometree \

initialize: initialize-ppxprint-runtime \
	initialize-pp-MLast-i initialize-pp-MLast \
	initialize-exceptions-i initialize-exceptions \
	initialize-pp-parsetree-i initialize-pp-parsetree \
	initialize-pp-outcometree-i initialize-pp-outcometree \

initialize-ppxprint-runtime:: ppxprint_runtime.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW ppxprint_runtime.ml

bootstrap-ppxprint-runtime: ppxprint_runtime.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  ppxprint_runtime.ml


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

initialize-exceptions-i:: exceptions.ORIG.mli
	echo "(* camlp5r *)" > $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW exceptions.mli

bootstrap-exceptions-i: exceptions.ORIG.mli
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  exceptions.mli

initialize-exceptions:: exceptions.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW exceptions.ml

bootstrap-exceptions: exceptions.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  exceptions.ml


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

initialize-pp-outcometree-i:: pp_outcometree.ORIG.mli
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW pp_outcometree.mli

bootstrap-pp-outcometree-i: pp_outcometree.ORIG.mli
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  pp_outcometree.mli

initialize-pp-outcometree:: pp_outcometree.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package camlp5.macro,camlp5.pr_r -syntax camlp5o $< >> $@.NEW
	mv $@.NEW pp_outcometree.ml

bootstrap-pp-outcometree: pp_outcometree.ORIG.ml
	echo "(* camlp5r *)" >> $@.NEW
	$(NOT_OCAMLFIND) preprocess $(DEBUG) -package $(PREPROCESS_PACKAGES),camlp5.macro,camlp5.pr_r,pa_ppx.import,pa_ppx.deriving_plugins.std \
	-syntax camlp5o -ppopt -D -ppopt BOOTSTRAP \
	-ppopt -pa_ppx-runtime -ppopt "Ppxprint_runtime" \
	-ppopt -pa_import-package -ppopt $(PREPROCESS_PACKAGES) \
	-ppopt -pa_import-I -ppopt . \
	-ppopt -sep -ppopt "\n" \
	$< >> $@.NEW
	mv $@.NEW  pp_outcometree.ml


clean::
	$(RM) -f *.cm[ioax] *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak $(TARGET)

ppxprint.cma: $(CMO)
ppxprint.cmxa: $(CMX)
pp_MLast.cmo pp_MLast.cmx: pp_MLast.cmi ppxprint_runtime.cmo
pp_parsetree.cmo pp_parsetree.cmx: pp_parsetree.cmi ppxprint_runtime.cmo
pp_outcometree.cmo pp_outcometree.cmx: pp_parsetree.cmi pp_outcometree.cmi ppxprint_runtime.cmo
pp_outcometree.cmi: pp_parsetree.cmi
exceptions.cmo exceptions.cmx: exceptions.cmi ppxprint_runtime.cmo

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)"
	cp $(TARGET) $(TARGET:.cma=.cmxa) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp $(CMI) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."

