all : pdf refs pdf

refs : pdf
	biber HeterogeneousNarwhal

pdf :
	lualatex -shell-escape HeterogeneousNarwhal

veryminimal :
	dvilualatex veryminimal.tex
	./dvisvgm --font-format=ttf,ah --linkmark=box:Melon veryminimal.dvi

svgs : dvis svg-convert

dvis :
	sed 's/%‼%/%‼%\n/g' HeterogeneousNarwhal.tex > HeterogeneousNarwhalDVI.tex
	dvilualatex -shell-escape -interaction=batchmode HeterogeneousNarwhalDVI

svg-convert :
	bash svg-convert.bash



