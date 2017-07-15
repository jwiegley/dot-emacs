ifeq ($(OS),Windows_NT)
CASK := $(shell cask --version 2> NUL)
else
CASK := $(shell command -v cask 2> /dev/null)
endif

# Disable builtin rules
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

# Don't delete intermediate files
.SECONDARY:

.PHONY: default dep clean git-clean

%.esh.tex: %.tex esh-init.el Cask
	${ESH2TEX} "$<"

# %.pdf: %.esh.tex
# 	rubber --module xelatex --jobname="$*" "$<"

%.pdf: %.esh.tex
	xelatex -jobname="$*" "$<"

default: main.pdf

dep:
ifndef CASK
    $(error >> Cask not found; You can install Cask from https://github.com/cask/cask <<)
else
	cask install
	cask update
endif

clean:
	rm -f *.esh.* main.pdf

git-clean:
	git clean -Xf
