emacs ?= emacs

LOAD = -l dired-du.el

all: test

test:
	$(emacs) -batch $(LOAD) -l dired-du-tests.el -f ert-run-tests-batch-and-exit

compile:
	$(emacs) -batch --eval "(progn (add-to-list 'load-path default-directory) (byte-compile-file \"dired-du.el\"))"

clean:
	rm -f *.elc

.PHONY: all compile clean test
