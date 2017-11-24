dnl Process this file with autoconf to produce a configure script.
dnl $Id: configure.ac,v 1.11 2007/06/10 13:17:24 ryants Exp $
AC_INIT(doxymacs, 1.8.0, http://sourceforge.net/projects/doxymacs)

AC_PREREQ(2.57)

AC_REVISION($Revision: 1.11 $)

AC_CONFIG_SRCDIR(c/doxymacs_parser.c)

AM_INIT_AUTOMAKE(doxymacs, 1.8.0)

AC_PREFIX_DEFAULT(${HOME})

dnl Checks for programs.
AC_PROG_CC
AC_PROG_INSTALL
AM_PATH_LISPDIR

dnl Checks for libraries.
AM_PATH_XML2(2.6.13)

dnl Checks for header files.
AC_HEADER_STDC

dnl Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST

dnl Checks for library functions.
AC_CHECK_FUNCS(strdup)

dnl Doxymacs specific configure options
AC_ARG_WITH(default-style,
  AC_HELP_STRING([--with-default-style=STYLE],
                 [Default Doxygen style to use.  One of "JavaDoc", "Qt", "C++" or "C++!".  Default "JavaDoc". ]),
  DOXYMACS_DEFAULT_STYLE="$withval", DOXYMACS_DEFAULT_STYLE="JavaDoc")

AC_ARG_WITH(external-xml-parser,
  AC_HELP_STRING([--with-external-xml-parser],
                 [Use external default xml parser by default.  Default is to use internal xml parser.]),
  DOXYMACS_USE_EXTERNAL_XML_PARSER="t", DOXYMACS_USE_EXTERNAL_XML_PARSER="nil")

AC_SUBST(DOXYMACS_DEFAULT_STYLE)
AC_SUBST(DOXYMACS_USE_EXTERNAL_XML_PARSER)

dnl Here is a hack to get the REAL bindir without any other
dnl embedded variables.
AC_CONFIG_COMMANDS_PRE([abs_bindir=${bindir} ; while echo ${abs_bindir} | grep '${[[A-Za-z0-9_]]\+}' > /dev/null ; do abs_bindir=`eval echo ${abs_bindir}` ; done ; DOXYMACS_PARSER=${abs_bindir}/doxymacs_parser${EXEEXT}])

AC_SUBST(DOXYMACS_PARSER)

AC_ARG_VAR(EMACS, [How to invoke emacs (e.g. EMACS=xemacs to use XEmacs).])
AC_ARG_VAR(EMACSLOADPATH, [Default load-path for EMACS.])

AC_CONFIG_FILES([Makefile c/Makefile lisp/Makefile lisp/doxymacs.el
                 no-autoconf/Makefile])

AC_OUTPUT
