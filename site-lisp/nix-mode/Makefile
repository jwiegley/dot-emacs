emacs ?= emacs

LOAD = -l nix-mode.el

all: test

test:
	$(emacs) -Q -batch $(LOAD) -l tests/nix-mode-tests.el -l tests/nix-font-lock-tests.el -f ert-run-tests-batch-and-exit

compile:
	$(emacs) -batch --eval "(progn (add-to-list 'load-path default-directory) (mapc #'byte-compile-file '(\"nix-mode.el\")))"

clean:
	rm -f *.elc

.PHONY: all compile clean test
