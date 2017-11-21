EMACS ?= emacs
CASK ?= cask

EMACSES=there-is-no-sensible-default-here

-include makefile-local

ifdef EMACS
EMACS_ENV=EMACS=$(EMACS)
endif


all: test

install:
	$(EMACS_ENV) $(CASK) install

just-test:
	$(EMACS_ENV) $(CASK) emacs --batch -q \
	--directory=. \
	--load "dev/fudge-discover" \
	--funcall fudge-discover-run-and-exit-batch

test: install just-test

package:
	$(EMACS_ENV) $(CASK) package

doc-gen:
	$(EMACS_ENV) $(CASK) emacs \
	--directory=. \
	--script dev/doc-gen.el -f doc-gen

publish-doc: ../m-buffer-pages/index.html ../m-buffer-pages/m-buffer-doc.css

../m-buffer-pages/m-buffer-doc.css: m-buffer-doc.css
	cp $< $@

../m-buffer-pages/index.html: m-buffer-doc.html
	perl -p -e 's#["]http://orgmode.org/org-info.js#"./org-info.js#' \
	$< > $@

m-buffer-doc.html: m-buffer-doc.org m-buffer.el m-buffer-at.el m-buffer-macro.el
	$(MAKE) doc-gen

clean:
	find . -name "m-buffer*org" -not -name "m-buffer-doc.org" \
	   -exec rm {} \;
	- rm m-buffer-doc.html

multi-test:
	make EMACS=$(EMACSES)/master/src/emacs test
	make EMACS=$(EMACSES)/emacs-25/src/emacs test
	make EMACS=$(EMACSES)/emacs-25.1/src/emacs test
	make EMACS=$(EMACSES)/emacs-24.5/src/emacs test
	make EMACS=$(EMACSES)/emacs-24.4/src/emacs test
	make EMACS=$(EMACSES)/emacs-24.3/src/emacs test
	make EMACS=$(EMACSES)/emacs-24.2/src/emacs test
	make EMACS=$(EMACSES)/emacs-24.1/src/emacs test

.PHONY: test
