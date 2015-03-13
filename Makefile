EMACS ?= emacs
CASK_EXEC ?= cask exec

all: test

test: clean-elc
	${MAKE} unit

unit:
	${CASK_EXEC} ${EMACS} -Q -batch -l tiny-test.el -l tiny.el --eval "(ert t)"

compile:
	${CASK_EXEC} ${EMACS} -Q -batch -f batch-byte-compile tiny.el

clean-elc:
	rm -f f.elc

.PHONY:	all test
