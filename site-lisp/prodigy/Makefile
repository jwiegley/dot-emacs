EMACS ?= emacs
CASK ?= cask

all: test

test: clean-elc
	${MAKE} unit
	${MAKE} ecukes
	${MAKE} compile
	${MAKE} unit
	${MAKE} ecukes
	${MAKE} clean-elc

unit:
	${CASK} exec ert-runner

ecukes:
	${CASK} exec ecukes

compile:
	${CASK} build

clean-elc:
	rm -f prodigy.elc

.PHONY:	all test unit ecukes compile
