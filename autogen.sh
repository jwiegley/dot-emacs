#!/bin/sh

# Bootstrap script for AUCTeX

# Maintainer: auctex-devel@gnu.org

# Copyright (C) 2003, 2004, 2005, 2006 Free Software Foundation, Inc.

# This file is part of AUCTeX.

# AUCTeX is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3, or (at your option)
# any later version.

# AUCTeX is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with AUCTeX; see the file COPYING.  If not, write to the Free
# Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
# MA 02110-1301, USA.

test "x${AUTOCONF}" != x || AUTOCONF=autoconf
test "x${MAKEINFO}" != x || MAKEINFO=makeinfo
test "x${PDFTEX}" != x || PDFTEX=pdftex
test "x${PERL}" != x || PERL=perl
test "x${MAKE}" != x || MAKE=make
${AUTOCONF} || { echo "Error running ${AUTOCONF} in ." >&2 ; exit 1; }
rm -rf autom4te.cache
if test "x${AUCTEXDATE}" = x
then
    AUCTEXDATE=`LC_ALL=C sed -n '1s/^\([-0-9][-0-9]*\).*/\1/p' ChangeLog`
    test "X${AUCTEXDATE}" != X || { echo "Can't find date in ChangeLog" >&2 ; exit 1; }
fi

if test "x${AUCTEXVERSION}" = x
then
    AUCTEXVERSION=`sed -n '2,/^[0-9]/s/.*Version \(.*\) released\..*/\1/p' ChangeLog`
    test "X${AUCTEXVERSION}" != X || AUCTEXVERSION=${AUCTEXDATE}
fi

cd doc
rm -f version.texi
${MAKE} -f Makefile.in MAKEINFO="${MAKEINFO}" PDFTEX="${PDFTEX}" PERL="$PERL" AUCTEXDATE="$AUCTEXDATE" AUCTEXVERSION="$AUCTEXVERSION" dist || { echo "Error running ${MAKE} in doc" >&2 ; exit 1; }
cd ..


