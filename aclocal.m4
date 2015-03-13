# serial 1

AC_DEFUN(AM_PATH_LISPDIR,
 [# If set to t, that means we are running in a shell under Emacs.
  # If you have an Emacs named "t", then use the full path.
  test "$EMACS" = t && EMACS=
  test "$EMACS" || AC_PATH_PROGS(EMACS, emacs xemacs, no)
  if test "$EMACS" != "no"; then
    AC_MSG_CHECKING([where .elc files should go])
    dnl Set default value
    lispdir="\$(datadir)/emacs/site-lisp"
    if test "x$prefix" = "xNONE"; then
      if test -d $ac_default_prefix/share/emacs/site-lisp; then
	lispdir="\$(prefix)/share/emacs/site-lisp"
      else
	if test -d $ac_default_prefix/lib/emacs/site-lisp; then
	  lispdir="\$(prefix)/lib/emacs/site-lisp"
	fi
      fi
    else
      if test -d $prefix/share/emacs/site-lisp; then
	lispdir="\$(prefix)/share/emacs/site-lisp"
      else
	if test -d $prefix/lib/emacs/site-lisp; then
	  lispdir="\$(prefix)/lib/emacs/site-lisp"
	fi
      fi
    fi
    AC_MSG_RESULT($lispdir)
  fi
  AC_SUBST(lispdir)])

dnl AC_EMACS_LIST AC_XEMACS_P AC_PATH_LISPDIR and AC_EMACS_CHECK_LIB
dnl are stolen from w3.
dnl AC_PATH_LISPDIR obsoletes AM_PATH_LISPDIR.

AC_DEFUN(AC_EMACS_LISP, [
elisp="$2"
if test -z "$3"; then
	AC_MSG_CHECKING(for $1)
fi
AC_CACHE_VAL(EMACS_cv_SYS_$1,[
	OUTPUT=./conftest-$$
	echo ${EMACS} -batch -eval "(let ((x ${elisp})) (write-region (if (stringp x) (princ x) (prin1-to-string x)) nil \"${OUTPUT}\"))" >& AC_FD_CC 2>&1  
	${EMACS} -batch -eval "(let ((x ${elisp})) (write-region (if (stringp x) (princ x 'ignore) (prin1-to-string x)) nil \"${OUTPUT}\"nil 5))" >& AC_FD_CC 2>&1
	retval=`cat ${OUTPUT}`
	echo "=> ${retval}" >& AC_FD_CC 2>&1
	rm -f ${OUTPUT}
	EMACS_cv_SYS_$1=$retval
])
$1=${EMACS_cv_SYS_$1}
if test -z "$3"; then
	AC_MSG_RESULT($$1)
fi
])

AC_DEFUN(AC_XEMACS_P, [
  AC_MSG_CHECKING([if $EMACS is really XEmacs])
  AC_EMACS_LISP(xemacsp,(if (string-match \"XEmacs\" emacs-version) \"yes\" \"no\") ,"noecho")
  XEMACS=${EMACS_cv_SYS_xemacsp}
  EMACS_FLAVOR=emacs
  if test "$XEMACS" = "yes"; then
     EMACS_FLAVOR=xemacs
  fi
  AC_MSG_RESULT($XEMACS)
  AC_SUBST(XEMACS)
  AC_SUBST(EMACS_FLAVOR)
])

AC_DEFUN(AC_PATH_LISPDIR, [
  AC_XEMACS_P
  if test "$prefix" = "NONE"; then
	AC_MSG_CHECKING([prefix for your Emacs])
	AC_EMACS_LISP(prefix,(expand-file-name \"..\" invocation-directory),"noecho")
	prefix=${EMACS_cv_SYS_prefix}
	AC_MSG_RESULT($prefix)
  fi
  AC_ARG_WITH(lispdir,[  --with-lispdir=DIR      Where to install lisp files], lispdir=${withval})
  AC_MSG_CHECKING([where .elc files should go])
  if test -z "$lispdir"; then
    dnl Set default value
    theprefix=$prefix
    if test "x$theprefix" = "xNONE"; then
	theprefix=$ac_default_prefix
    fi
    if test "$EMACS_FLAVOR" = "xemacs"; then
        datadir="\$(prefix)/lib"
        lispdir="\$(datadir)/${EMACS_FLAVOR}/site-packages/lisp/gnus"
    else
    lispdir="\$(datadir)/${EMACS_FLAVOR}/site-lisp/gnus"
    fi
    for thedir in share lib; do
	potential=
	dnl The directory name should be quoted because it might contain spaces.
	if test -d "${theprefix}/${thedir}/${EMACS_FLAVOR}/site-lisp"; then
           if test "$EMACS_FLAVOR" = "xemacs"; then
	       lispdir="\$(prefix)/${thedir}/${EMACS_FLAVOR}/site-packages/lisp/gnus"
           else
               lispdir="\$(datadir)/${EMACS_FLAVOR}/site-lisp/gnus"
           fi
	   break
	fi
    done
  fi
  AC_MSG_RESULT($lispdir)
  AC_SUBST(lispdir)
])

AC_DEFUN(AC_PATH_ETCDIR, [
  AC_ARG_WITH(etcdir,[  --with-etcdir=DIR       Where to install etc files], etcdir=${withval})
  AC_MSG_CHECKING([where etc files should go])
  if test -z "$etcdir"; then
    dnl Set default value.
    if test "$EMACS_FLAVOR" = "xemacs"; then
      etcdir="\$(lispdir)/../../etc"
    else
      etcdir="\$(lispdir)/../../etc"
    fi
  fi
  AC_MSG_RESULT($etcdir)
  AC_SUBST(etcdir)
])

dnl 
dnl This is a bit on the "evil hack" side of things.  It is so we can
dnl have a different default infodir for XEmacs.  A user can still specify
dnl someplace else with '--infodir=DIR'.
dnl
AC_DEFUN(AC_PATH_INFO_DIR, [
  AC_MSG_CHECKING([where the TeXinfo docs should go])
  dnl Set default value.  This must be an absolute path.
  if test "$infodir" = "\${prefix}/info"; then
    if test "$EMACS_FLAVOR" = "xemacs"; then
      info_dir="\$(prefix)/${thedir}/${EMACS_FLAVOR}/site-packages/info"
    else
      info_dir="\$(prefix)/info"
    fi
  else
    info_dir=$infodir
  fi
  AC_MSG_RESULT($info_dir)
  AC_SUBST(info_dir)
])

dnl
dnl This will set the XEmacs command line options to be slightly different
dnl from the Emacs ones.  If building with XEmacs the options will be
dnl "-batch -no-autoloads..." to give a much cleaner build environment.
dnl
AC_DEFUN(AC_SET_BUILD_FLAGS, [
  AC_MSG_CHECKING([which options to pass on to (X)Emacs])
  if test "x$FLAGS" = "x"; then
    if test "$EMACS_FLAVOR" = "xemacs"; then
      FLAGS="-batch -no-autoloads -l \$(srcdir)/dgnushack.el"
    else
      FLAGS="-batch -q -no-site-file -l \$(srcdir)/dgnushack.el"
    fi
  else
    FLAGS=$FLAGS
  fi
  AC_MSG_RESULT($FLAGS)
  AC_SUBST(FLAGS)
])

dnl
dnl Check whether a function exists in a library
dnl All '_' characters in the first argument are converted to '-'
dnl
AC_DEFUN(AC_EMACS_CHECK_LIB, [
if test -z "$3"; then
	AC_MSG_CHECKING(for $2 in $1)
fi
library=`echo $1 | tr _ -`
AC_EMACS_LISP($1,(progn (fmakunbound '$2) (condition-case nil (progn (require '$library) (fboundp '$2)) (error (prog1 nil (message \"$library not found\"))))),"noecho")
if test "${EMACS_cv_SYS_$1}" = "nil"; then
	EMACS_cv_SYS_$1=no
fi
if test "${EMACS_cv_SYS_$1}" = "t"; then
	EMACS_cv_SYS_$1=yes
fi
HAVE_$1=${EMACS_cv_SYS_$1}
AC_SUBST(HAVE_$1)
if test -z "$3"; then
	AC_MSG_RESULT($HAVE_$1)
fi
])

dnl
dnl Perform checking available fonts: Adobe Bembo, Adobe Futura and 
dnl Bitstream Courier.
dnl

AC_DEFUN(GNUS_CHECK_FONTS, [
test "$LATEX" = t && LATEX=
test "$LATEX" || AC_PATH_PROGS(LATEX, latex, no)
AC_MSG_CHECKING(for available fonts)
AC_ARG_WITH(fonts,[  --with-fonts            Assume all fonts required are available],[USE_FONTS="$withval"])
WITH_FONTS_bembo='%'
WITHOUT_FONTS_bembo=
WITH_FONTS_pfu='%'
WITHOUT_FONTS_pfu=
WITH_FONTS_bcr='%'
WITHOUT_FONTS_bcr=
if test -z "${USE_FONTS}"; then
  if test "${LATEX}" = no; then
	:
  else
    OUTPUT=./conftest-$$
    echo '\nonstopmode\documentclass{article}\usepackage{bembo}\begin{document}\end{document}' > ${OUTPUT}
    if ${LATEX} ${OUTPUT} </dev/null >& AC_FD_CC 2>&1  ; then  
      if test -z "${USE_FONTS}"; then
	USE_FONTS="Adobe Bembo"
      else
	USE_FONTS="${USE_FONTS}, Adobe Bembo"
      fi
      WITH_FONTS_bembo=
      WITHOUT_FONTS_bembo='%'
    fi
    echo '\nonstopmode\documentclass{article}\begin{document}{\fontfamily{pfu}\fontsize{10pt}{10}\selectfont test}\end{document}' > ${OUTPUT}
    if retval=`${LATEX} ${OUTPUT} </dev/null 2>& AC_FD_CC`; then
      if echo "$retval" | grep 'Some font shapes were not available' >& AC_FD_CC 2>&1  ; then  
	:
      else
        if test -z "${USE_FONTS}"; then
	  USE_FONTS="Adobe Futura"
        else
	  USE_FONTS="${USE_FONTS}, Adobe Futura"
        fi
        WITH_FONTS_pfu=
        WITHOUT_FONTS_pfu='%'
      fi
    fi
    echo '\nonstopmode\documentclass{article}\begin{document}{\fontfamily{bcr}\fontsize{10pt}{10}\selectfont test}\end{document}' > ${OUTPUT}
    if retval=`${LATEX} ${OUTPUT} </dev/null 2>& AC_FD_CC`; then
      if echo "$retval" | grep 'Some font shapes were not available' >& AC_FD_CC 2>&1  ; then  
	:
      else
        if test -z "${USE_FONTS}"; then
	  USE_FONTS="Bitstream Courier"
        else
	  USE_FONTS="${USE_FONTS}, Bitstream Courier"
        fi
        WITH_FONTS_bcr=
        WITHOUT_FONTS_bcr='%'
      fi
    fi
    rm -f ${OUTPUT} ${OUTPUT}.aux ${OUTPUT}.log ${OUTPUT}.dvi
  fi
elif test "${USE_FONTS}" = yes ; then
  WITH_FONTS_bembo=
  WITHOUT_FONTS_bembo='%'
  WITH_FONTS_pfu=
  WITHOUT_FONTS_pfu='%'
  WITH_FONTS_bcr=
  WITHOUT_FONTS_bcr='%'
fi
AC_SUBST(WITH_FONTS_bembo)
AC_SUBST(WITHOUT_FONTS_bembo)
AC_SUBST(WITH_FONTS_pfu)
AC_SUBST(WITHOUT_FONTS_pfu)
AC_SUBST(WITH_FONTS_bcr)
AC_SUBST(WITHOUT_FONTS_bcr)
if test -z "${USE_FONTS}" ; then
  USE_FONTS=no
fi
USE_FONTS=`echo "${USE_FONTS}" | sed 's/,\([[^,]]*\)$/ and\1/'`
AC_MSG_RESULT("${USE_FONTS}")
if test "${USE_FONTS}" = yes ; then
  USE_FONTS='Set in Adobe Bembo, Adobe Futura and Bitstream Courier.'
elif test "${USE_FONTS}" = no ; then
  USE_FONTS=''
else
  USE_FONTS="Set in ${USE_FONTS}."
fi
AC_SUBST(USE_FONTS)
])
