EMACS ?= emacs
CASK ?= cask

all: test

test: clean
	${MAKE} unit
	${MAKE} compile
	${MAKE} clean

unit:
	${CASK} exec ert-runner

compile:
	${CASK} exec ${EMACS} -Q -batch -f batch-byte-compile helm-company.el

clean:
	rm -f helm-company.elc

.PHONY:        all test unit compile clean
