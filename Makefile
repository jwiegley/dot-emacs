EMACS ?= emacs
CASK ?= cask

all: test

test: clean-elc
	${MAKE} ecukes
	${MAKE} compile
	${MAKE} ecukes
	${MAKE} clean-elc

ecukes:
	${CASK} exec ecukes

compile:
	${CASK} exec ${EMACS} -Q -batch -f batch-byte-compile prodigy.el

clean-elc:
	rm -f prodigy.elc

.PHONY:	all test ecukes compile
