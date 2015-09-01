.PHONY: all lisp contrib autoloads examples experimental doc info-only
.PHONY: clean realclean distclean fullclean install-info install-bin install
.PHONY: test dist release upload elpa

DEFS = $(shell test -f Makefile.defs && echo Makefile.defs \
	|| echo Makefile.defs.default)

include $(DEFS)

SUBDIRS = lisp contrib examples experimental texi

all: autoloads lisp contrib info-only

lisp:
	(cd lisp && $(MAKE))

contrib:
	(cd contrib && $(MAKE))

autoloads:
	(cd lisp && $(MAKE) autoloads)

examples:
	(cd examples && $(MAKE))

experimental:
	(cd experimental && $(MAKE))

info-only:
	(cd texi && $(MAKE) info-only)

doc texi:
	(cd texi && $(MAKE))

clean:
	for i in $(SUBDIRS); do \
	 (cd $$i && $(MAKE) clean); done

realclean fullclean: clean
	for i in $(SUBDIRS); do \
	 (cd $$i && $(MAKE) realclean); done

install-info:
	(cd texi && $(MAKE) install)

install-bin: autoloads lisp contrib
	(cd lisp && $(MAKE) install)
	(cd contrib && $(MAKE) install)
	(cd experimental && $(MAKE) install-uncompiled)

install: install-bin install-info

test: 
	(cd lisp && $(MAKE) test)

distclean:
	for i in $(SUBDIRS); do \
	 (cd $$i && $(MAKE) distclean); done
	-rm -fr ../$(PROJECT)-$(VERSION)

dist: autoloads distclean
	git archive --format=tar --prefix=$(PROJECT)-$(VERSION)/ HEAD | \
	  (cd .. && tar xf -)
	rm -f ../$(PROJECT)-$(VERSION)/.gitignore
	cp lisp/$(PROJECT)-autoloads.el ../$(PROJECT)-$(VERSION)/lisp

release: dist
	(cd .. && tar -czf $(PROJECT)-$(VERSION).tar.gz \
	    $(PROJECT)-$(VERSION) ; \
	  zip -r $(PROJECT)-$(VERSION).zip $(PROJECT)-$(VERSION) && \
	  gpg --detach $(PROJECT)-$(VERSION).tar.gz && \
	  gpg --detach $(PROJECT)-$(VERSION).zip)

upload:
	(cd .. && \
	  scp $(PROJECT)-$(VERSION).zip* $(PROJECT)-$(VERSION).tar.gz* \
	    mwolson@download.gna.org:/upload/muse-el)

elpa: realclean info-only
	rm -fR $(ELPADIR)/$(PROJECT)-$(VERSION)
	rm -f $(ELPADIR)/$(PROJECT)-$(VERSION).tar
	mkdir -p $(ELPADIR)/$(PROJECT)-$(VERSION)
	cp lisp/*.el $(ELPADIR)/$(PROJECT)-$(VERSION)
	cp contrib/*.el $(ELPADIR)/$(PROJECT)-$(VERSION)
	echo '(define-package "$(PROJECT)" "$(VERSION)"' > \
	  $(ELPADIR)/$(PROJECT)-$(VERSION)/$(PROJECT)-pkg.el
	echo '  "$(ELPADESC)")' >> \
	  $(ELPADIR)/$(PROJECT)-$(VERSION)/$(PROJECT)-pkg.el
	cp texi/$(MANUAL).info $(ELPADIR)/$(PROJECT)-$(VERSION)
	cp texi/dir-template $(ELPADIR)/$(PROJECT)-$(VERSION)/dir
	install-info --section "Emacs" "Emacs" \
	  --info-dir=$(ELPADIR)/$(PROJECT)-$(VERSION) \
	  $(ELPADIR)/$(PROJECT)-$(VERSION)/$(MANUAL).info
	rm -f $(ELPADIR)/$(PROJECT)-$(VERSION)/dir.old
	(cd $(ELPADIR) && tar cf $(PROJECT)-$(VERSION).tar \
	  $(PROJECT)-$(VERSION))
