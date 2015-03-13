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
SITELISP=$(PREFIX)/share/emacs/site-lisp/emms

INSTALLINFO = /usr/sbin/install-info --info-dir=$(INFODIR)
CHANGELOG_CMD = git log --pretty=medium --no-merges

# The currently released version of EMMS
VERSION=3.0

.PHONY: all install lisp docs deb-install clean
.PRECIOUS: %.elc
all: lisp docs

autoloads:
	$(MAKE) -C $(LISPDIR) emms-auto.el

lisp:
	$(MAKE) -C $(LISPDIR)

docs:
	$(MAKE) -C $(DOCDIR)

emms-print-metadata: $(SRCDIR)/emms-print-metadata.c
	$(CC) $(CFLAGS) $(LDFLAGS) -o $(SRCDIR)/$@ $< `taglib-config --cflags --libs` -ltag_c

install:
	test -d $(SITELISP) || mkdir -p $(SITELISP)
	test -d $(INFODIR) || install -d $(INFODIR)
	install -m 644 $(ALLSOURCE) $(SITELISP)
	install -m 644 $(ALLCOMPILED) $(SITELISP)
	install -m 0644 $(DOCDIR)emms.info $(INFODIR)/emms
	for p in $(MAN1PAGES) ; do $(GZIP) -9c $$p > $(MAN1DIR)/$$p.gz ; done
	$(INSTALLINFO) emms.info

remove-info:
	$(INSTALLINFO) --remove emms.info

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
	  zip -r emms-$(VERSION).zip emms-$(VERSION) && \
	  gpg --detach emms-$(VERSION).tar.gz && \
	  gpg --detach emms-$(VERSION).zip)

upload:
	(cd .. && echo "Directory: emms" | gpg --clearsign > \
	    emms-$(VERSION).tar.gz.directive.asc && \
	  cp emms-$(VERSION).tar.gz.directive.asc \
	    emms-$(VERSION).zip.directive.asc && \
	  echo open ftp://ftp-upload.gnu.org > upload.lftp ; \
	  echo cd /incoming/ftp >> upload.lftp ; \
	  echo mput emms-$(VERSION).zip* >> upload.lftp ; \
	  echo mput emms-$(VERSION).tar.gz* >> upload.lftp ; \
	  echo close >> upload.lftp ; \
	  lftp -f upload.lftp ; \
	  rm -f upload.lftp)
