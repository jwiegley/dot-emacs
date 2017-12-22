GZIP=gzip
MAN1PAGES=emms-print-metadata.1
DOCDIR=doc/
LISPDIR=lisp
SRCDIR=src

ALLSOURCE=$(wildcard $(LISPDIR)/*.el)
ALLCOMPILED=$(wildcard $(LISPDIR)/*.elc)

DESTDIR=
PREFIX=$(DESTDIR)/usr/local
INFODIR=$(PREFIX)/info
MAN1DIR=$(PREFIX)/share/man/man1
BINDIR=$(PREFIX)/bin
SITELISP=$(PREFIX)/share/emacs/site-lisp/emms

GINSTALLINFO = /usr/bin/ginstall-info --info-dir=$(INFODIR)
# For systems without ginstall-info
INSTALLINFO = /usr/bin/install-info --info-dir=$(INFODIR)
CHANGELOG_CMD = git log --pretty=medium --no-merges

# The currently released version of EMMS
VERSION=4.4

.PHONY: all install lisp docs deb-install clean
.PRECIOUS: %.elc
all: lisp docs

autoloads:
	$(MAKE) -C $(LISPDIR) emms-auto.el

lisp:
	$(MAKE) -C $(LISPDIR)

docs:
	$(MAKE) -C $(DOCDIR)

emms-print-metadata: $(SRCDIR)/emms-print-metadata.cpp
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(LDFLAGS) -o $(SRCDIR)/$@ $< `taglib-config --cflags --libs`

install:
	test -d $(SITELISP) || mkdir -p $(SITELISP)
	test -d $(INFODIR) || install -d $(INFODIR)
	install -m 644 $(ALLSOURCE) $(SITELISP)
	install -m 644 $(ALLCOMPILED) $(SITELISP)
	install -m 0644 $(DOCDIR)emms.info $(INFODIR)/emms.info
	for p in $(MAN1PAGES) ; do $(GZIP) -9c $$p > $(MAN1DIR)/$$p.gz ; done
	if [ -x /usr/bin/ginstall-info ]; then \
		$(GINSTALLINFO) $(DOCDIR)emms.info; \
	else \
		$(INSTALLINFO) $(DOCDIR)emms.info; \
	fi
	if [ -x  $(SRCDIR)/emms-print-metadata ]; then \
		echo "emms-print-metadata found, installing"; \
		install -m 755 $(SRCDIR)/emms-print-metadata $(BINDIR)/emms-print-metadata; \
	else \
		echo "skipping emms-print-metadata install"; \
	fi

remove-info:
	if [ -x /usr/bin/ginstall-info ]; then \
		$(GINSTALLINFO) --remove $(DOCDIR)emms.info; \
	else \
		$(INSTALLINFO) --remove $(DOCDIR)emms.info; \
	fi

ChangeLog:
	$(CHANGELOG_CMD) > $@

clean:
	-rm -f *~ $(DOCDIR)emms.info $(DOCDIR)emms.html $(SRCDIR)/emms-print-metadata
	$(MAKE) -C $(LISPDIR) clean

dist: clean autoloads
	git archive --format=tar --prefix=emms-$(VERSION)/ HEAD | \
	  (cd .. && tar xf -)
	rm -f ../emms-$(VERSION)/.gitignore
	cp lisp/emms-auto.el ../emms-$(VERSION)/lisp
	$(CHANGELOG_CMD) > ../emms-$(VERSION)/ChangeLog

release: dist
	(cd .. && tar -czf emms-$(VERSION).tar.gz \
	    emms-$(VERSION) ; \
	  gpg --detach emms-$(VERSION).tar.gz)

upload:
	(cd .. && echo "version: 1.2\ndirectory: emms\nfilename: "emms-$(VERSION).tar.gz"\ncomment: version 4.0 of Emms" | gpg --clearsign > emms-$(VERSION).tar.gz.directive.asc && echo open ftp://ftp-upload.gnu.org > upload.lftp ; echo cd /incoming/ftp >> upload.lftp ; echo mput emms-$(VERSION).tar.gz* >> upload.lftp ; echo close >> upload.lftp ; lftp -f upload.lftp ; rm -f upload.lftp)
