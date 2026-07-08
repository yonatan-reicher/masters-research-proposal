ltx_files = $(wildcard *.tex)

LATEX = lualatex -output-format pdf

main.pdf : $(ltx_files)
	$(LATEX) main.tex
	bibtex main
	$(LATEX) main.tex
	$(LATEX) main.tex

.PHONY: clean
clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc *.lof *.lot
	rm -f main.pdf
