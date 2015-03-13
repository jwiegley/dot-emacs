PACKAGE-NAME:=esup
VERSION:=$(shell perl -ne 'print $$1 if /;; Version: +(.*)/' esup.el)
PACKAGE:=${PACKAGE-NAME}-${VERSION}
EMACS ?= emacs
CASK ?= cask

ELPA_DIR = \
	.cask/$(shell $(EMACS) -Q --batch --eval '(princ emacs-version)')/elpa

test: elpa
	$(CASK) exec ert-runner

byte-compile: elpa
	$(CASK) exec $(EMACS) -Q -L . -batch -f batch-byte-compile \
	  esup.el esup-child.el

clean:
	rm -f *.elc
	rm -rf ${PACKAGE}
	rm -f ${PACKAGE}.zip ${PACKAGE}.tar ${PACKAGE}.tar.bz2

package: clean
	mkdir ${PACKAGE}
	cp -r *.el Makefile *.md ${PACKAGE}

package.tar: package
	tar cf ${PACKAGE}.tar ${PACKAGE}

package.tar.bz2: tar
	bzip2 ${PACKAGE}.tar

package.zip: package
	zip -r ${PACKAGE}.zip ${PACKAGE}

elpa: $(ELPA_DIR)
$(ELPA_DIR): Cask
	$(CASK) install
	touch $@
