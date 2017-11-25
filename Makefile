emacs ?= emacs

.PHONY: all clean

all: test

test:
	$(emacs) -batch -l auto-yasnippet.el -l auto-yasnippet-test.el -f ert-run-tests-batch-and-exit

clean:
	rm -f *.elc
