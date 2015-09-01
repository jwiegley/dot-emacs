# configure.ac --- configuration setup for BBDB

# Copyright (C) 2000-2001 Didier Verna <didier@xemacs.org>
# Copyright (C) 2011-2014 Roland Winkler <winkler@gnu.org>
# 
# Author:        Didier Verna <didier@xemacs.org>
# Maintainer:    Roland Winkler <winkler@gnu.org>
#
# BBDB is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
# 
# BBDB is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with BBDB.  If not, see <http://www.gnu.org/licenses/>.
# 
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.69])

AC_INIT([bbdb],[3.1.2],[bbdb-info@lists.sourceforge.net],[],[http://savannah.nongnu.org/projects/bbdb/]) 
AC_CONFIG_SRCDIR([lisp/bbdb.el])
AC_CONFIG_MACRO_DIR([m4])
# We need GNU Automake 1.13 for AM_ELCFLAGS.
AM_INIT_AUTOMAKE([1.13 -Wall gnu])

AC_PACKAGE_DATE

# Checks for programs.
AC_PROG_INSTALL

# Search for Emacs
AM_PATH_LISPDIR
AS_IF([test "$EMACS" = no], [AC_MSG_ERROR([cannot find Emacs])])

# Checks for libraries.
EMACS_VM
AC_SUBST([AM_ELCFLAGS])

# Generate lisp/bbdb-site.el via lisp/Makefile as pkgdatadir is only known
# at "make" time.
AC_CONFIG_FILES([Makefile
                 lisp/Makefile
                 lisp/bbdb-pkg.el
                 doc/Makefile
                 tex/Makefile])

AC_OUTPUT
