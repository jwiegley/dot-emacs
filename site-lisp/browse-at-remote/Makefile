EMACS ?= emacs
CASK ?= cask

.PHONY: test compile install clean

install:
	${CASK} install

test: clean
	${CASK} exec ert-runner

compile:
	${CASK} build

clean:
	rm -f browse-at-remote.elc
