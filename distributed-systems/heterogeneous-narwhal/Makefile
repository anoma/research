all: pdf refs pdf

refs: pdf
	biber HeterogeneousNarwhal

pdf:
	lualatex -shell-escape HeterogeneousNarwhal
