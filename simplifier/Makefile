THISDIR=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))

PARSER=simplifier_parser
LEXER=simplifier_lexer

TOOLSDIR=tools
TOOLSPATH=$(THISDIR)$(TOOLSDIR)
TOOLSNAME=notations printTools tools ftools
TOOLSML=$(addsuffix .ml,$(TOOLSNAME))
TOOLSCMX=$(addsuffix .cmx,$(TOOLSNAME))

SLLANGDIR=sllang
SLLANGPATH=$(THISDIR)$(SLLANGDIR)
SLLANGNAME=slsyntax
SLLANGML=$(addsuffix .ml,$(SLLANGNAME))
SLLANGCMX=$(addsuffix .cmx,$(SLLANGNAME))

SMTDIR=smtlang
SMTPATH=$(THISDIR)$(SMTDIR)
SMTNAME=smtsyntax smttoz3 sltosmt 
SMTML=$(addsuffix .ml,$(SMTNAME))
SMTCMX=$(addsuffix .cmx,$(SMTNAME))

PKGS=-package z3,ANSITerminal -thread

INCLUDES=-I $(TOOLSPATH) -I $(SLLANGPATH) -I $(SMTPATH)

vpath %.ml $(TOOLSPATH) $(SLLANGPATH) $(SMTPATH)
vpath %.cmx $(TOOLSPATH) $(SLLANGPATH) $(SMTPATH)
vpath %.mll $(SLLANGPATH)
vpath %.mly $(SLLANGPATH)

MAIN=simplifier_main.ml
TARGET=simplifier

$(TARGET): $(TOOLSCMX) $(SLLANGCMX) $(SMTCMX) $(MAIN)
	ocamllex $(LEXER).mll
	ocamlyacc $(PARSER).mly
	@FILES="$(PARSER).mli $(LEXER).ml $(PARSER).ml";\
	for FILE in $$FILES; do\
		echo "Compiling $$FILE";\
		ocamlfind opt $(INCLUDES) -c $$FILE;\
	done
	@echo "Compiling $(MAIN)"
	@ocamlfind opt -o $(TARGET) $(PKGS) -linkpkg $(INCLUDES)\
		$(TOOLSCMX) $(SLLANGCMX) $(SMTCMX) $(THISCMX) $(PARSER).cmx $(LEXER).cmx \
		simplifier.ml \
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
	@DIRS="$(TOOLSPATH) $(SLLANGPATH) $(SMTPATH) $(THISDIR)";\
	for DIR in $$DIRS; do\
		echo "Cleaning $$DIR";\
		cd $$DIR;\
		rm -f *~ *.mli *.cmx *.cmo *.cmi *.cmt *.o;\
	done

fresh: clean $(TARGET)

