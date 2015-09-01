# Copyright (C) 2002, 2003  Juri Linkov <juri@jurta.org>
# This file is distributed under the terms of the GNU GPL.

VERSION = 0.1.0

EMACS    = emacs -no-site-file -no-init-file
MAKEINFO = makeinfo --no-split
RM       = rm -f
TAR      = tar

ELFILES  = \
	ee.el \
	ee-autoloads.el \
	ee-bbdb.el \
	ee-buffers.el \
	ee-commands.el \
	ee-customize.el \
	ee-datafile.el \
	ee-dired.el \
	ee-dselect.el \
	ee-edb.el \
	ee-ell.el \
	ee-example.el \
	ee-fields.el \
	ee-finder.el \
	ee-gnus.el \
	ee-history.el \
	ee-imenu.el \
	ee-info.el \
	ee-marks.el \
	ee-menubar.el \
	ee-outline.el \
	ee-processes.el \
	ee-programs.el \
	ee-ps.el \
	ee-tags.el \
	ee-textfile.el \
	ee-variables.el \
	ee-views.el \
	ee-windows.el

ELCFILES = $(ELFILES:.el=.elc)

EEDATAFILES  = \
	NEWS.ee \
	TODO.ee \
	ee.ee

EEVIEWFILES  = \
	view/NEWS.ee \
	view/TODO.ee \
	view/apachelog.ee \
	view/bbdb.ee \
	view/buffers.ee \
	view/changelog.ee \
	view/commands.ee \
	view/customize.ee \
	view/dired.ee \
	view/dselect.ee \
	view/edb.ee \
	view/ell.ee \
	view/example.ee \
	view/fields.ee \
	view/finder.ee \
	view/gnus.ee \
	view/history.ee \
	view/imenu.ee \
	view/info-dir.ee \
	view/info.ee \
	view/links.ee \
	view/marks.ee \
	view/menubar.ee \
	view/outline.ee \
	view/processes.ee \
	view/programs.ee \
	view/ps.ee \
	view/tags.ee \
	view/variables.ee \
	view/views.ee \
	view/windows.ee

TEXIFILES = ee.texi
INFOFILES = $(TEXIFILES:.texi=.info)
HTMLFILES = $(TEXIFILES:.texi=.html)

DISTFILES = ChangeLog COPYING Makefile README \
            $(ELFILES) \
            $(EEDATAFILES) \
            $(TEXIFILES) $(INFOFILES)
DISTVIEWFILES = $(EEVIEWFILES)
DISTNAME = emacs-ee-$(VERSION)

.SUFFIXES:
.SUFFIXES: .el .elc .ee .texi .info .html

all: elc info

elc: ee.elc ee-autoloads.elc $(ELCFILES)

ee.elc: ee.el
	$(EMACS) -batch -q $(PUSHPATH) -f batch-byte-compile $<

ee-autoloads.elc: ee-autoloads.el
	$(EMACS) -batch -q $(PUSHPATH) -f batch-byte-compile $<

.el.elc:
	$(EMACS) -batch -q $(PUSHPATH) -l ./ee.elc -l ./ee-autoloads.elc -f batch-byte-compile $<

ee-autoloads.el: $(ELFILES)
	@$(RM) $@;
	@echo "(provide 'ee-autoloads)" > $@;
	@echo "" >> $@;
	$(EMACS) -batch -q -l autoload \
		--eval '(setq generated-autoload-file "'`pwd`'/$@")' \
		--eval "(if (featurep 'xemacs) (delete-file generated-autoload-file))" \
		--eval '(setq make-backup-files nil)' \
		--eval '(setq autoload-package-name "ee")' \
		-f batch-update-autoloads `pwd`

info: $(INFOFILES)

html: $(HTMLFILES)

.texi.info:
	$(MAKEINFO) -o $@ $<

.texi.html:
	$(MAKEINFO) --html -o $@ $<

clean:
	$(RM) *.elc *.info* *.html *.dvi *.ps

check-versions:
	grep -in -e "version.*[0-9]\.[0-9]" $(DISTFILES)

$(DISTNAME).tar.gz: $(DISTFILES)
	rm -rf $(DISTNAME)
	mkdir -p $(DISTNAME)
	mkdir -p $(DISTNAME)/view
	cp -p $(DISTFILES) $(DISTNAME)
	cp -p $(DISTVIEWFILES) $(DISTNAME)/view
	tar -cvzf $(DISTNAME).tar.gz --owner=0 --group=0 $(DISTNAME)
	rm -rf $(DISTNAME)
	ls -l emacs-ee-*.tar.gz

dist: $(DISTNAME).tar.gz
