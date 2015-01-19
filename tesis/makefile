TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error
BIB = bibtex

MAIN = main
PROT = protocol
BIBL = bibliography

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(BIBL).bbl
	$(TEX) $(MAIN).tex
	$(TEX) $(PROT).tex

$(BIBL).bbl : $(BIBL).bib
	$(BIB) $(MAIN)
	$(BIB) $(PROT)

$(BIBL).bib : $(MAIN).tex $(PROT).tex
	$(TEX) $(MAIN).tex
	$(TEX) $(PROT).tex

clean:
	rm -fv *.log $(MAIN).pdf $(PROT).pdf *~
