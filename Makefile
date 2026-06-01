ltx_files = $(wildcard *.tex)

main.pdf : $(ltx_files)
	lualatex -output-format pdf main.tex
