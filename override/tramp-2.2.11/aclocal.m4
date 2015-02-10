dnl  Copyright (C) 2003-2014 Free Software Foundation, Inc.

dnl  This file is free software: you can redistribute it and/or modify
dnl  it under the terms of the GNU General Public License as published by
dnl  the Free Software Foundation, either version 3 of the License, or
dnl (at your option) any later version.

dnl  This file is distributed in the hope that it will be useful,
dnl  but WITHOUT ANY WARRANTY; without even the implied warranty of
dnl  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
dnl  GNU General Public License for more details.

dnl  You should have received a copy of the GNU General Public License
dnl  along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

dnl Most functions are initially stolen from gnus.  Thanks for all the fish!

dnl
dnl Execute Lisp code
dnl
AC_DEFUN(AC_EMACS_LISP, [
  elisp="$2"
  if test -z "$3"; then
     AC_MSG_CHECKING(for $1)
  fi

  if test `echo "${EMACS}" | grep xemacs`; then
    EM="${EMACS} -no-autoloads -batch -eval"
  else
    EM="${EMACS} --no-site-file -batch -eval"
  fi

  AC_CACHE_VAL(EMACS_cv_SYS_$1, [
    OUTPUT=./conftest-$$
    echo ${EM} "(let ((x ${elisp})) (write-region (if (stringp x) (princ x) (prin1-to-string x)) nil \"${OUTPUT}\"))" >& AC_FD_CC 2>&1
    ${EM} "(let ((x ${elisp})) (write-region (if (stringp x) (princ x 'ignore) (prin1-to-string x)) nil \"${OUTPUT}\"nil 5))" >& AC_FD_CC 2>&1
    if test ! -e "${OUTPUT}"; then
      AC_MSG_RESULT()
      AC_MSG_ERROR([calling ${EMACS}])
    fi
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

dnl
dnl Checks the Emacs flavor in use.  Result for `EMACS' is the program to run.
dnl `EMACS_INFO' is the target the info file is generated for; will be either
dnl `emacs', or `xemacs'.  `EMACS_GW' (`yes' or `no') is an indication,
dnl whether tramp-gw.el can be offered.  Checks for proper version.
dnl
AC_DEFUN(AC_EMACS_INFO, [

  dnl Apparently, if you run a shell window in Emacs, it sets the EMACS
  dnl environment variable to 't'.  Lets undo the damage.
  if test "x${EMACS}" = "x" -o "x${EMACS}" = "xt"; then
     EMACS=emacs
  fi

  dnl Check parameter.
  AC_ARG_WITH(
    xemacs,
    [[  --with-xemacs[=PROG]    use XEmacs to build [PROG=xemacs]]],
    [ if test "${withval}" = "yes"; then EMACS=xemacs; else EMACS=${withval}; fi ])
  AC_ARG_WITH(
    emacs,
    [[  --with-emacs[=PROG]     use Emacs to build [PROG=emacs]]],
    [ if test "${withval}" = "yes"; then EMACS=emacs; else EMACS=${withval}; fi ])

  dnl Check program availability.
  if test -z $EMACS; then
    AC_CHECK_PROGS([EMACS], [emacs xemacs], [no])
    if test "${EMACS}" = no; then
      AC_MSG_ERROR([emacs not found])
    fi
  else
    AC_CHECK_PROG([EMACS_test_emacs], [$EMACS], [yes], [no], [$PATH:/])
    if test "${EMACS_test_emacs}" = no; then
      AC_MSG_ERROR([$EMACS not found])
    fi
  fi

  dnl Check flavor.
  AC_MSG_CHECKING([for $EMACS flavor])
  AC_EMACS_LISP(
    xemacsp,
    (if (featurep 'xemacs) \"yes\" \"no\"),
    "noecho")
  if test "${EMACS_cv_SYS_xemacsp}" = "yes"; then
     EMACS_INFO=xemacs
  else
     EMACS_INFO=emacs
  fi
  AC_MSG_RESULT($EMACS_INFO)
  AC_SUBST(EMACS_INFO)

  dnl Check gvfs support. It is assumed that D-Bus bindings are sufficient.
  AC_MSG_CHECKING([for $EMACS gvfs support])
  AC_EMACS_LISP(
    gvfsp,
    (if (featurep 'dbusbind) \"yes\" \"no\"),
    "noecho")
  EMACS_GVFS=$EMACS_cv_SYS_gvfsp
  AC_MSG_RESULT($EMACS_GVFS)
  AC_SUBST(EMACS_GVFS)

  dnl Check gateway support.
  AC_MSG_CHECKING([for $EMACS gateway support])
  AC_EMACS_LISP(
    gatewayp,
    (if (functionp 'make-network-process) \"yes\" \"no\"),
    "noecho")
  EMACS_GW=$EMACS_cv_SYS_gatewayp
  AC_MSG_RESULT($EMACS_GW)
  AC_SUBST(EMACS_GW)

  dnl Check version.
  TRAMP_EMACS_VERSION_CHECK="\
(if (or (>= emacs-major-version 22)
		 (and (featurep 'xemacs)
		      (= emacs-major-version 21)
		      (>= emacs-minor-version 4)))
	     \"ok\"
	   (format \"${PACKAGE_STRING} is not fit for %s\"
		   (when (string-match \"^.*$\" (emacs-version))
		     (match-string 0 (emacs-version)))))\
"
  AC_SUBST(TRAMP_EMACS_VERSION_CHECK)

  AC_MSG_CHECKING([for $EMACS version])
  AC_EMACS_LISP(emacs_version, $TRAMP_EMACS_VERSION_CHECK, "noecho")
  if test "${EMACS_cv_SYS_emacs_version}" = "ok"; then
     AC_MSG_RESULT(ok)
  else
     AC_MSG_RESULT(nok)
     AC_MSG_ERROR([$EMACS_cv_SYS_emacs_version])
  fi
])

dnl
dnl Checks whether a package provided via the contrib directory should
dnl be made available via a link. First parameter is a provided function
dnl from the package in question, which is the second parameter.
dnl If the first parameter is empty, just the package is looked for.
dnl If the third parmeter is not zero, the package is optional.
dnl Function and package names must encode "-" with "_".
dnl
AC_DEFUN(AC_CONTRIB_FILES, [

  function=`echo $1 | tr _ -`
  library=`echo $2 | tr _ -`
  AC_MSG_CHECKING([for $library])

  dnl Old links must be removed anyway.
  if test -h lisp/$library; then rm -f lisp/$library; fi

  dnl Check whether contrib packages could be used.
  AC_ARG_WITH(
    contrib,
    [  --with-contrib          use contributed packages],
    [ if test "${withval}" = "yes"; then USE_CONTRIB=yes; fi ])

  dnl Check whether Lisp function does exist.
  if test -z "$1"; then
    EMACS_cv_SYS_$1="nil"
  else
    AC_EMACS_LISP($1, (progn (if (featurep 'xemacs) (require 'timer-funcs)) (load \"$library\" t) (fboundp '$function)), "noecho")
  fi

  dnl Create the link.
  if test "${EMACS_cv_SYS_$1}" = "nil"; then
    if test "${USE_CONTRIB}" = "yes"; then
      if test -e contrib/$library; then
        TRAMP_CONTRIB_FILES="$library $TRAMP_CONTRIB_FILES"
	dnl AC_CONFIG_LINKS cannot expand $library.  Therefore, we use
	dnl $2 and replace it afterwards.
	AC_CONFIG_LINKS(lisp/$2:contrib/$2)
	ac_config_links=`echo $ac_config_links | sed -e s/$2/$library/g`
        AC_MSG_RESULT(linked to contrib directory)
      elif test -z "$3"; then
        AC_MSG_RESULT(not found)
        AC_MSG_ERROR(Could not find package $library in contrib directory)
      else
        AC_MSG_RESULT(not found)
      fi
    elif test -z "$3"; then
      AC_MSG_RESULT(not found)
      AC_MSG_ERROR(Use --with-contrib for implementation supplied with Tramp)
    else
      AC_MSG_RESULT(skipped)
    fi
  else
    AC_MSG_RESULT(ok)
  fi
])

dnl
dnl Checks whether Tramp is prepared for (X)Emacs package.  This case,
dnl the installation chapter is not part of the manual.  Necessary for
dnl maintainers only.
dnl
AC_DEFUN(AC_EMACS_INSTALL, [

  INSTALL_CHAPTER=yes

  dnl Check parameter.
  AC_MSG_CHECKING([for installation chapter])
  AC_ARG_WITH(
    packaging,
    [  --with-packaging        installation chapter not needed in manual],
    [ if test "${withval}" = "yes"; then INSTALL_CHAPTER=no; fi ])

  AC_MSG_RESULT($INSTALL_CHAPTER)
  AC_SUBST(INSTALL_CHAPTER)
])

dnl
dnl Return install target for Lisp files.
dnl
AC_DEFUN(AC_PATH_LISPDIR, [

  dnl Check prefix.
  AC_MSG_CHECKING([prefix ])

  prefix_default=$ac_default_prefix
  if test "${prefix}" = NONE; then
     prefix=$prefix_default
  fi

  AC_MSG_RESULT([$prefix])

  dnl Check datarootdir.
  AC_MSG_CHECKING([datarootdir])

  if test "$EMACS_INFO" = "xemacs"; then
     datarootdir_default="\${prefix}/lib"
  else
     datarootdir_default="\${prefix}/share"
  fi

  if test "${datarootdir}" = "\${prefix}/share"; then
     datarootdir=$datarootdir_default
  fi

  AC_MSG_RESULT([$datarootdir])

  dnl Check datadir.
  AC_MSG_CHECKING([datadir])

  datadir_default="\$datarootdir_default"

  if test "${datadir}" = NONE; then
     datadir=$datadir_default
  fi

  AC_MSG_RESULT([$datadir])

  dnl Check lispdir.
  AC_ARG_WITH(
    lispdir,
    [[  --with-lispdir=DIR      where to install lisp files
                          [DATADIR/emacs/site-lisp] or
                          [DATADIR/xemacs/site-lisp]]],
    lispdir=${withval})
  dnl Alternative approach.
dnl  m4_divert_once(HELP_BEGIN, [], [])
dnl  m4_divert_once(HELP_BEGIN,
dnl    AC_HELP_STRING(
dnl      [  lispdir=DIR],
dnl      [where to install lisp files
dnl       [[DATADIR/emacs/site-lisp]] or
dnl       [[DATADIR/xemacs/site-lisp]]]))
  AC_MSG_CHECKING([lispdir])

  lispdir_default="\${datadir}/${EMACS_INFO}/site-lisp"

  : ${lispdir:=$lispdir_default}

  dnl Expand $lispdir_default for trampinst.texi.  We need to apply `eval'
  dnl several times, because $prefix, $datarootdir and $datadir must be
  dnl expanded in an unknown order.
  lispdir_default=$(eval eval eval echo ${lispdir_default})

  AC_MSG_RESULT($lispdir)
])

dnl
dnl This is a bit on the "evil hack" side of things.  It is so we can
dnl have a different default infodir for XEmacs.  A user can still specify
dnl someplace else with '--infodir=DIR'.
dnl
AC_DEFUN(AC_PATH_INFODIR, [

  dnl Check infodir.
  AC_MSG_CHECKING([infodir])

  dnl Check default places.
  if test "$EMACS_INFO" = "xemacs"; then
     infodir_default="\${datadir}/xemacs/info"
  else
     infodir_default="\${datadir}/info"
  fi

  dnl If default directory doesn't exist, derive from $prefix.
  dnl ${prefix} and ${datadir} must be expanded for test.
  if ! test -d $(eval eval eval echo ${infodir_default})
  then
     infodir_default="\${prefix}/info"
  fi

  dnl If default directory doesn't exist, derive from $prefix_default.
  dnl ${prefix} and ${datadir} must be expanded for test.
  if ! test -d $(eval eval eval echo ${infodir_default})
  then
     infodir_default="\${prefix_default}/info"
  fi

  dnl Set it if necessary.
  if test "${infodir}" = "\${prefix}/info"; then
     infodir=$infodir_default
  fi

  dnl Expand $datarootdir.
  infodir=$(echo ${infodir} | sed -e "s#[$][{]datarootdir[}]#$datarootdir#")

  dnl Expand $infodir_default for trampinst.texi.  We need to apply it
  dnl several times, because $prefix, $datarootdir and $datadir need
  dnl to be expanded in an unknown order.
  infodir_default=$(eval eval eval echo ${infodir_default})

  AC_MSG_RESULT([$infodir])
])
