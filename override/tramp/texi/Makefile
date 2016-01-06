# -*- coding: utf-8; -*-
# Emacs Makefile for TRAMP
# texi/Makefile.  Generated from Makefile.in by configure.

# Copyright (C) 1998-2015 Free Software Foundation, Inc.

# Author: Kai Großjohann <kai.grossjohann@gmx.net>
#         Michael Albinus <michael.albinus@gmx.de>
# Keywords: comm, processes

# This file is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This file is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

# This Makefile requires GNU make and GNU texinfo.  If there is an
# insufficient version of makeinfo, autoconf refuses to generate
# Makefile.  Problems of texi2dvi or install-info result in a warning.

EMACS		= emacs
EMACS_GVFS	= $(if $(findstring yes, no), emacsgvfs, noemacsgvfs)
EMACS_GW	= $(if $(findstring yes, yes), emacsgw, noemacsgw)
EMACS_INFO	= emacs
INSTALL_CHAPTER	= $(if $(findstring yes, yes), \
			installchapter, noinstallchapter)
MAKEINFO	= makeinfo --no-split
TEXI2DVI	= texi2dvi
INSTALL		= install -m644
INSTALL_INFO	= install-info --quiet
CP		= cp
MKDIR		= @mkdir -p
RM		= -rm -f

prefix		= /usr/local
datarootdir	= ${prefix}/share
datadir		= ${datarootdir}
infodir		= ${prefix}/share/info
localinfodir	= ../info
DESTDIR		=

TEXI_FILES	= tramp.texi trampver.texi doclicense.texi docstyle.texi \
		  $(if $(findstring yes, yes), trampinst.texi)
INFO_FILES	= $(localinfodir)/tramp
INSTALL_FILES	= $(DESTDIR)$(infodir)/tramp
CLEAN_FILES	= .\\\#* \\\#* .*~ *~ *.aux *.cp *.cps *.diff *.dvi *.elc *.fn *.fns *.html *.info *.ky *.log *.pg *.tmp *.toc *.tp *.vr *.vrs $(wildcard $(localinfodir)/*)

# To be used by maintainer only.
NONGNU		= ../../tramp-web

.PHONY: all install clean distclean tramp dvi html savannah \
	$(INSTALL_FILES) $(localinfodir)/dir $(DESTDIR)$(infodir)/dir

all: tramp dvi html

tramp: $(INFO_FILES) $(localinfodir)/dir

install: tramp $(INSTALL_FILES) $(DESTDIR)$(infodir)/dir

clean:
	$(RM) $(CLEAN_FILES)

distclean: clean

$(localinfodir)/tramp: $(TEXI_FILES)
	$(MKDIR) $(dir $@)
	$(MAKEINFO) --footnote-style=end -D $(EMACS_GVFS) -D $(EMACS_GW) \
		-D $(EMACS_INFO) -D $(INSTALL_CHAPTER) -o $@ $(notdir $@).texi

$(DESTDIR)$(infodir)/tramp:
	$(MKDIR) $(dir $@)
	$(INSTALL) $(INFO_FILES) $(DESTDIR)$(infodir)

# Don't call install-info if it failed in configure.
$(localinfodir)/dir $(DESTDIR)$(infodir)/dir: $(INFO_FILES)
	$(MKDIR) $(dir $@)
	$(if $(findstring dir, $(shell find $(dir $@) -name dir)),, \
		$(CP) dir_sample $@)
	$(if $(findstring no, $(INSTALL_INFO)),, \
		$(foreach file, $(INFO_FILES), \
			$(if $(shell grep -q -s "($(notdir $(file)))\." $@),, \
			    $(INSTALL_INFO) --info-dir=$(dir $@) \
				$(subst $(dir $(file)), $(dir $@), $(file)))))

dvi: tramp.dvi

# Don't call texi2dvi if it failed in configure.
%.dvi: $(TEXI_FILES)
	$(if $(findstring no, $(TEXI2DVI)),, \
		$(TEXI2DVI) -b -c \
		-t "@set $(EMACS_GVFS)" -t "@set $(EMACS_GW)" \
		-t "@set $(EMACS_INFO)" -t "@set $(INSTALL_CHAPTER)" $*.texi)

html: tramp.html

tramp.html: tramp-emacs.html tramp-xemacs.html
	$(RM) tramp.html
	ln -s tramp-emacs.html tramp.html

tramp-%.html: $(TEXI_FILES)
	$(MAKEINFO) --html -D $* -D $(EMACS_GVFS) -D $(EMACS_GW) \
		-D $(INSTALL_CHAPTER) -o $@ $<

# Maintainer targets.

savannah: html
	cp tramp*emacs.html $(NONGNU)
	cp tramp-emacs.html $(NONGNU)/index.html
	@echo ""
	@echo "Now use cvs checkin in $(NONGNU)"
	@echo ""
