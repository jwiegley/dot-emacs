EMACS ?= emacs
CASK ?= cask

all:
	${MAKE} clean
	${MAKE} test
	${MAKE} compile
	${MAKE} test
	${MAKE} clean

compile:
	${CASK} exec ${EMACS} -Q -batch -L . -eval \
	"(progn \
	(setq byte-compile-error-on-warn t) \
	(batch-byte-compile))" guide-key.el
test:
	${CASK} exec ert-runner
clean:
	rm -f guide-key.elc

.PHONY: all compile test clean
