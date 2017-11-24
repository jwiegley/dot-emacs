emacs ?= emacs
CASK = ~/.cask/bin/cask
BEMACS = $(emacs) -batch -l targets/elpa.el

all: compile

cask:
	$(CASK)

compile:
	$(BEMACS) -l targets/compile.el

.PHONY: all compile clean cask

clean:
	rm -f *.elc
