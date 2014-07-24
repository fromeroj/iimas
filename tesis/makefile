TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error
BIB = bibtex

MAIN = main
BIBL = bibliography

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(BIBL).bbl
	$(TEX) $(MAIN).tex

$(BIBL).bbl : $(BIBL).bib
	$(BIB) $(MAIN)

$(BIBL).bib : $(MAIN).tex
	$(TEX) $(MAIN).tex

clean:: 
	rm -fv *.log $(MAIN).pdf
