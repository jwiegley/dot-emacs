EMACS=emacs

PACKAGE=deft

SOURCE=deft.el
COMPILED=deft.elc

VERSION=$(shell cat $(SOURCE) | sed -n 's/^;;; Version: \(.*\)/\1/p')

.el.elc:
	$(EMACS) -q -no-site-file -no-init-file -batch -f batch-byte-compile $<

all: $(COMPILED) README.md

.PHONY: dist

README.md: $(SOURCE) readme.sh
	./readme.sh

dist:
	DIR=$$(mktemp -d -t "$(PACKAGE)"); \
	DESTDIR="$$DIR/$(PACKAGE)-$(VERSION)"; \
	mkdir -p $$DESTDIR; \
	cp -a $(SOURCE) README.md $$DESTDIR; \
	tar zcf $(CURDIR)/$(PACKAGE)-$(VERSION).tar.gz -C $$DIR "$(PACKAGE)-$(VERSION)"; \
	rm -r $$DIR; \
	echo "$(PACKAGE)-$(VERSION).tar.gz has been created"

update: $(COMPILED)
	cp -a $(SOURCE) $(COMPILED) $(HOME)/.emacs.d/site-lisp

clean:
	rm -f $(COMPILED) index.text
