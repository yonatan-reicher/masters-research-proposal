ltx_files = $(wildcard *.tex)

LATEX = lualatex -output-format pdf

main.pdf : $(ltx_files)
	$(LATEX) main.tex
	bibtex main
	$(LATEX) main.tex
	$(LATEX) main.tex
