### Makefile.emacs --- Emacs makefile for X-Symbol

## Copyright (C) 2002 Free Software Foundation, Inc.

## Author: Masayuki Ataka <ataka@milk.freemail.ne.jp>
## Version: 4.5
## Keywords: fonts, WYSIWYG, LaTeX, HTML, wp, math
## X-URL: http://x-symbol.sourceforge.net/
## X-URL: http://isweb22.infoseek.co.jp/computer/pop-club/emacs/TeX.html

# Minor changes by Christoph Wedler <wedler@users.sourceforge.net>

# This software is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the
# Free Software Foundation; either version 2, or (at your option) any
# later version.

# This software is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# for more details.

# You should have received a copy of the GNU General Public License
# along with This software; see the file COPYING.  If not, write to
# the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
# Boston, MA 02111-1307, USA.

PACKAGE = x-symbol

EMACS   = emacs
EFLAG   = -q --no-site-file --batch
PREFIX  = /usr/local
LISPDIR = $(PREFIX)/share/emacs/site-lisp/$(PACKAGE)
DATADIR = $(PREFIX)/share/emacs/etc/$(PACKAGE)
INFODIR = $(PREFIX)/info

RM    = rm -f
CP    = cp
MKDIR = mkdir -p

all: elc
install: install-el install-etc install-info

install-el:
	if test ! -d $(LISPDIR); then \
		$(MKDIR) $(LISPDIR); \
	fi
	$(CP) lisp/$(PACKAGE)/* $(LISPDIR)

install-etc:
	if test ! -d $(DATADIR); then \
		$(MKDIR) $(DATADIR); \
	fi
	$(CP) -r etc/$(PACKAGE)/* $(DATADIR);

install-info:
	if test ! -d $(INFODIR); then \
		$(MKDIR) $(INFODIR); \
	fi
	$(CP) -r info/* $(INFODIR);

elc: clean
	cd lisp/$(PACKAGE)/; $(EMACS) $(EFLAG) --directory "./" -l "auto-autoloads.el" -f batch-byte-compile *.el

clean:
	$(RM) *~
	cd lisp/$(PACKAGE)/; $(RM) *.elc

distclean: clean
