.PHONY: all clean test

EMACS = emacs

ELCFILES = $(addsuffix .elc, $(basename $(wildcard *.el)))

all: $(ELCFILES)

%.elc : %.el
	@echo Compiling $<
	@${EMACS} -batch -q -no-site-file -L . -f batch-byte-compile $<

clean:
	@rm -f *.elc

test: all
	@${EMACS} -batch -L . -l test.el -f ert-run-tests-batch-and-exit
