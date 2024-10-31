MAKEFILEPATH=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))
SLACPATH=$(shell dirname ${MAKEFILEPATH})

THISDIR=satcheck
THISPATH=$(SLACPATH)/$(THISDIR)
THISNAME=satcheck
THISML=$(addsuffix .ml,$(THISNAME))
THISCMX=$(addsuffix .cmx,$(THISNAME))

PARSER=satcheck_parser
LEXER=satcheck_lexer

TOOLSDIR=tools
TOOLSPATH=$(SLACPATH)/$(TOOLSDIR)
TOOLSNAME=notations printTools tools ftools
TOOLSML=$(addsuffix .ml,$(TOOLSNAME))
TOOLSCMX=$(addsuffix .cmx,$(TOOLSNAME))

SLLANGDIR=sllang
SLLANGPATH=$(SLACPATH)/$(SLLANGDIR)
SLLANGNAME=slsyntax
SLLANGML=$(addsuffix .ml,$(SLLANGNAME))
SLLANGCMX=$(addsuffix .cmx,$(SLLANGNAME))

SMTDIR=smtlang
SMTPATH=$(SLACPATH)/$(SMTDIR)
SMTNAME=smtsyntax smttoz3 sltosmt 
SMTML=$(addsuffix .ml,$(SMTNAME))
SMTCMX=$(addsuffix .cmx,$(SMTNAME))

PKGS=-package z3,ANSITerminal -thread

INCLUDES=-I $(SLACPATH) -I $(TOOLSPATH) -I $(SLLANGPATH) -I $(SMTPATH)

vpath %.ml $(TOOLSPATH) $(SLLANGPATH) $(SMTPATH) $(SLACPATH)
vpath %.cmx $(TOOLSPATH) $(SLLANGPATH) $(SMTPATH) $(SLACPATH)
vpath %.mll $(SLLANGPATH)
vpath %.mly $(SLLANGPATH)

MAIN=satcheck_main.ml
TARGET=satcheck

$(TARGET): $(TOOLSCMX) $(SLLANGCMX) $(SMTCMX) $(THISCMX) $(MAIN)
	ocamllex $(LEXER).mll
	ocamlyacc $(PARSER).mly
	@FILES="$(PARSER).mli $(LEXER).ml $(PARSER).ml";\
	for FILE in $$FILES; do\
		echo "Compiling $$FILE";\
		ocamlfind opt $(INCLUDES) -c $$FILE;\
	done
	@echo "Compiling $(MAIN)"
	@ocamlfind opt -o $(TARGET) $(PKGS) -linkpkg $(INCLUDES)\
		$(TOOLSCMX) $(SLLANGCMX) $(SMTCMX) $(THISCMX) $(PARSER).cmx $(LEXER).cmx\
		$(MAIN)
	@echo "--> $(TARGET) is produced"

$(TOOLSCMX): $(TOOLSML)
	@echo "Compiling $(TOOLSDIR)/$(basename $@).ml"
	@cd $(TOOLSPATH); ocamlfind opt $(PKGS) -thread -c $(basename $@).ml

$(SLLANGCMX): $(SLLANGML)
	@echo "Compiling $(SLLANGDIR)/$(basename $@).ml"
	@cd $(SLLANGPATH); ocamlfind opt $(INCLUDES) $(PKGS) -c $(basename $@).ml

$(SMTCMX): $(SMTML)
	@echo "Compiling $(SMTDIR)/$(basename $@).ml"
	@cd $(SMTPATH); ocamlfind opt $(INCLUDES) $(PKGS) -thread -c $(basename $@).ml

$(THISCMX): $(THISML)
	@echo "Compiling $(THISDIR)/$(basename $@).ml"
	@cd $(THISPATH); ocamlfind opt $(INCLUDES) $(PKGS) -thread -c $(basename $@).ml

.PHONY: clean fresh
clean:
	@echo "Removing $(PARSER).ml and $(LEXER).ml"
	@rm -f $(PARSER).ml $(LEXER).ml
	@DIRS="$(SLACPATH) $(TOOLSPATH) $(SLLANGPATH) $(SMTPATH) $(SATPATH) $(THISPATH)";\
	for DIR in $$DIRS; do\
		echo "Cleaning $$DIR";\
		cd $$DIR;\
		rm -f *~ *.mli *.cmx *.cmo *.cmi *.cmt *.o;\
	done

fresh: clean $(TARGET)

