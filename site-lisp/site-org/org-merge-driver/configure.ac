# Process this file with autoconf to produce a configure script.
AC_INIT([org-merge-driver], [0.1], [youngar17@gmail.com])
AC_CONFIG_AUX_DIR([config])
PKG_CHECK_MODULES([CHECK], [check >= 0.9.4],,
			   AC_MSG_WARN([Check is required to run unit tests http://check.sourceforge.net/]))
AM_INIT_AUTOMAKE([-Wall -Werror gnu parallel-tests])

AC_CONFIG_MACRO_DIR([m4])

## Check for programs
AC_PROG_CC   # c compiler
gl_EARLY     # gnu lib
AM_PROG_CC_C_O
AM_PROG_LEX  # flex
if test "x$LEX" != xflex; then
  AC_MSG_WARN([To generate the lexer, Flex is required.  Lexer will not be regenerated.])
  AC_SUBST([LEX],[:])
fi
AC_PROG_YACC # bison
AC_PROG_AWK # ak
AC_REQUIRE_AUX_FILE([tap-driver.sh]) # testing driver

## gnulib macros
gl_INIT

## Check for headers
## Check for typedefs, structures, and compilers characteristics
## Check for library functions

## Output files
AC_CONFIG_HEADERS([config.h])
AC_CONFIG_FILES([
 Makefile
 src/Makefile
 gnulib/lib/Makefile
 tests/Makefile
 doc/Makefile
])
AC_OUTPUT
