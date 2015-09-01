# -*- coding: utf-8; -*-
# Emacs Makefile for TRAMP
# test/Makefile.  Generated from Makefile.in by configure.

# Copyright (C) 2013-2015 Free Software Foundation, Inc.

# Author: Michael Albinus <michael.albinus@gmx.de>
# Keywords: comm, processes

EMACS		= emacs
CLEAN_FILES	= .\\\#* \\\#* .*~ *~ *.aux *.cp *.cps *.diff *.dvi *.elc *.fn *.fns *.html *.info *.ky *.log *.pg *.tmp *.toc *.tp *.vr *.vrs

EM = $(EMACS) -Q -batch -L `pwd`/../lisp

.PHONY: all check clean distclean test

.SUFFIXES: .elc .el

all: check

check test: tramp-tests.elc
	$(EM) -L `pwd` -l tramp-tests -f ert-run-tests-batch-and-exit

%.elc: %.el
	$(EM) -l bytecomp -f batch-byte-compile $?

clean:
	$(RM) $(CLEAN_FILES)

distclean: clean
