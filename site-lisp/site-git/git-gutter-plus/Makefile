EMACS ?= emacs
CASK ?= cask

all: test

test: clean-elc
	${MAKE} unittest
	${MAKE} compile
	${MAKE} unittest
	${MAKE} clean-elc

unittest:
	${CASK} exec ert-runner

compile:
	${CASK} build

clean-elc:
	rm -f *.elc

.PHONY:	all test unittest compile
