# I have no idea how Makefiles work, and cribbed from the internet
# just enough so I had something I could use for automating testing.

EMACS=emacs

.PHONY: all test clean

all:
	${EMACS} -Q --batch -L . -f batch-byte-compile *.el

test:
	${EMACS} -Q --batch -L . -l ert -l ebdb-test.el -f ert-run-tests-batch-and-exit

clean:
	rm *.elc
