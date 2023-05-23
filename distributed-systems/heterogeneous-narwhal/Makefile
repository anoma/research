all: pdf refs pdf

refs: pdf
	biber HeterogeneousNarwhal

pdf:
	lualatex -shell-escape HeterogeneousNarwhal

veryminimal:
	dvilualatex veryminimal.tex
	./dvisvgm --font-format=ttf,ah --linkmark=box:Melon veryminimal.dvi
