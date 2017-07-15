ESH2TEX := $(realpath ../bin/esh2tex)
ESH2HTML := $(realpath ../bin/esh2html)
ARGS ?=

ifeq ($(OS),Windows_NT)
CASK := $(shell cask --version 2> NUL)
else
CASK := $(shell command -v cask 2> /dev/null)
endif

# Ensure some amount of reproducibility on TexLive 2016:
export SOURCE_DATE_EPOCH=1483228800

.PHONY: all xelatex pdflatex dep clean reference

all: xelatex

html: dep example.html
	${ESH2HTML} --debug-on-error ${ARGS} example.html

xelatex: dep example.tex
	${ESH2TEX} --debug-on-error ${ARGS} example.tex
	xelatex -jobname=example example.esh.tex

pdflatex: dep example.tex
	$(eval export ESH_PDFLATEX=true)
	${ESH2TEX} --debug-on-error ${ARGS} example.tex
	pdflatex -jobname=example example.esh.tex

dep:
ifndef CASK
	$(warning >> Cask not found; some languages will not be available <<)\
	$(warning > You can install Cask from https://github.com/cask/cask <)
else
	$(info >>        Fetching or updating Cask dependencies.         <<)
	$(info > In real life, you would run make dep by hand when needed <)
	cask install
	cask update
endif

clean:
	git clean -Xf

reference: xelatex
	cp example.pdf reference.pdf
