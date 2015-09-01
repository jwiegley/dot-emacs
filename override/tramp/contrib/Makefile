# -*- coding: utf-8; -*-
# Emacs Makefile for TRAMP
# contrib/Makefile.  Generated from Makefile.in by configure.

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

# This Makefile requires GNU make.

# For compiling the add-on packages.

EMACS		= emacs
INSTALL		= install -m644
MKDIR		= @mkdir -p
RM		= -rm -f

prefix		= /usr/local
datarootdir	= ${prefix}/share
datadir		= ${datarootdir}
lispdir		= ${datadir}/emacs/site-lisp
DESTDIR		=

CLEAN_FILES	= .\\\#* \\\#* .*~ *~ *.aux *.cp *.cps *.diff *.dvi *.elc *.fn *.fns *.html *.info *.ky *.log *.pg *.tmp *.toc *.tp *.vr *.vrs

all: $(addsuffix .elc, $(basename $(wildcard *.el)))

%.elc: %.el
	$(EMACS) --no-site-file -batch -f batch-byte-compile $?

install: $(wildcard *.el *.elc)
	$(MKDIR) $(DESTDIR)$(lispdir)
	$(INSTALL) $? $(DESTDIR)$(lispdir)

clean:
	$(RM) $(CLEAN_FILES)

distclean: clean
