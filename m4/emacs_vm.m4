### emacs_vm.m4

## Copyright (C) 2013-2014 Roland Winkler <winkler@gnu.org>
##
## This file is part of the Insidious Big Brother Database (aka BBDB),
##
## BBDB is free software: you can redistribute it and/or modify
## it under the terms of the GNU General Public License as published by
## the Free Software Foundation, either version 3 of the License, or
## (at your option) any later version.
##
## BBDB is distributed in the hope that it will be useful,
## but WITHOUT ANY WARRANTY; without even the implied warranty of
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
## GNU General Public License for more details.
##
## You should have received a copy of the GNU General Public License
## along with BBDB.  If not, see <http://www.gnu.org/licenses/>.

AC_DEFUN([EMACS_VM],
[
AC_ARG_WITH([vm-dir],
AS_HELP_STRING([--with-vm-dir=DIR], [where to find VM lisp directory]),
# if VM was requested, make sure we have access to the source
[if test "x$with_vm_dir" != xno -a "x$with_vm_dir" != "x"; then
    AC_MSG_CHECKING([for VM files])
    # convert path to absolute and canonicalize it.
    VMDIR=$(${EMACS} -batch --quick -eval "(message \"%s\" (expand-file-name \"${with_vm_dir}\"))" 2>&1)
    VM_LOCATE=$(${EMACS} -batch --quick --directory="${VMDIR}" -eval "(if (locate-library \"vm-autoloads\") (message \"vm\"))" 2>&1)
    if test "x$VM_LOCATE" = "x"; then
       AC_MSG_ERROR([*** VM vm-autoloads.el must exist in directory passed to --with-vm-dir.])
    fi
    AC_MSG_RESULT($VMDIR)
    # append VMDIR to AM_ELCFLAGS
    AM_ELCFLAGS="--directory=$VMDIR $AM_ELCFLAGS"
 fi])
# New conditional VM
AM_CONDITIONAL([VM], [test x$VMDIR != x])
])
