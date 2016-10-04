emacs ?= emacs
CASK = ~/.cask/bin/cask
BEMACS = $(emacs) -batch -l targets/elpa.el

all: compile test

cask:
	$(shell EMACS=$(emacs) $(CASK) --verbose --debug)

compile:
	$(BEMACS) -l targets/compile.el
clean:
	rm -f *.elc

.PHONY: all clean cask
