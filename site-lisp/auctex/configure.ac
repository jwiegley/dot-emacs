dnl Autoconf script for AUCTeX

dnl Maintainer: auctex-devel@gnu.org

dnl Copyright (C) 2003, 2004, 2005, 2006 Free Software Foundation, Inc.

dnl This file is part of AUCTeX.

dnl AUCTeX is free software; you can redistribute it and/or modify it
dnl under the terms of the GNU General Public License as published by
dnl the Free Software Foundation; either version 3, or (at your option)
dnl any later version.

dnl AUCTeX is distributed in the hope that it will be useful, but
dnl WITHOUT ANY WARRANTY; without even the implied warranty of
dnl MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
dnl General Public License for more details.

dnl You should have received a copy of the GNU General Public License
dnl along with AUCTeX; see the file COPYING.  If not, write to the Free
dnl Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
dnl MA 02110-1301, USA.

AC_INIT(auctex,11.89,bug-auctex@gnu.org)

AC_CHECK_PROGS_REQUIRED(MAKECMD, make, [make not found, aborting!])
AC_PROG_MAKE_SET
AC_PROG_INSTALL

AC_DATE_VERSION_FROM_CHANGELOG(AUCTEXDATE,AUCTEXVERSION,ChangeLog)
AC_SUBST(AUCTEXDATE)
AC_SUBST(AUCTEXVERSION)

AC_DATE_VERSION_FROM_CHANGELOG(PREVIEWDATE,PREVIEWVERSION,ChangeLog-preview)
AC_SUBST(PREVIEWDATE)
AC_SUBST(PREVIEWVERSION)

EMACS_PROG_EMACS

if test ${EMACS_FLAVOR} = xemacs
then
  EMACS_CHECK_VERSION(21,4)
else
  EMACS_CHECK_VERSION(21,1)
fi

EMACS_CHECK_MULE

# The Debian package uses `--disable-build-dir-test'; normal users should
# never need to modify the default behavior.
AC_ARG_ENABLE([build-dir-test],
  [  --enable-build-dir-test test for build directory inside `load-path'
			  (on by default)],
  [if ! [[ "X-${enableval}" = "X-no" ]]
     then VALID_BUILD_DIR
   fi],
  [VALID_BUILD_DIR])

AC_ARG_ENABLE(preview,
  [  --disable-preview       disable inclusion of preview-latex],
  [preview_enabled="$enableval"],
  [preview_enabled="yes"])
AC_SUBST(preview_enabled)

if test ${EMACS_FLAVOR} = "xemacs"  ; then
   EMACS_PATH_PACKAGEDIR
   PLAT_LISP=prv-xemacs.el
else
   packagedir=no
   PLAT_LISP=prv-emacs.el
fi

if test "X${packagedir}" = Xno
then
   EMACS_PATH_LISPDIR
   AC_MSG_CHECKING(what file to use for auctex startup)
   AC_ARG_WITH(auctexstartfile,
   [[  --with-auctexstartfile=FILE    What file to use for auctex startup.]],
   [[ auctexstartfile="${withval}" ]],
   [ _tmpdir_="${lispdir}"
     AC_FULL_EXPAND(_tmpdir_)
     if test -d "${_tmpdir_}/site-start.d"
     then
       auctexstartfile="${lispdir}/site-start.d/auctex.el"
     else
       auctexstartfile="${lispdir}/auctex.el"
     fi])
   AC_MSG_RESULT([[${auctexstartfile}]])

   AC_MSG_CHECKING(what file to use for preview startup)
   AC_ARG_WITH(previewstartfile,
   [[  --with-previewstartfile=FILE    What file to use for preview startup.]],
   [[ previewstartfile="${withval}" ]],
   [ _tmpdir_="${lispdir}"
     AC_FULL_EXPAND(_tmpdir_)
     if test -d "${_tmpdir_}/site-start.d"
     then
       previewstartfile="${lispdir}/site-start.d/preview-latex.el"
     else
       previewstartfile="${lispdir}/preview-latex.el"
     fi])
   AC_MSG_RESULT([[${previewstartfile}]])

   packagelispdir="${lispdir}/auctex"
   packagedatadir="${packagelispdir}"
   texsitedir="${lispdir}"
else
   #lispdir is only used for determining relative files.
   lispdir="${packagedir}"
   packagelispdir="${packagedir}/lisp/auctex"
   texsitedir="$packagelispdir"
   auctexstartfile="${packagelispdir}"/auto-autoloads.el
   previewstartfile="${packagelispdir}"/auto-autoloads.el
   packagedatadir="${packagedir}/etc/auctex"
   infodir="${packagedir}/info"
   INSTALL_INFO=:
fi

AC_SUBST(auctexstartfile)
AC_SUBST(previewstartfile)
AC_SUBST(PLAT_LISP)

AC_MSG_CHECKING([where the package lisp files go])
AC_ARG_WITH(packagelispdir,
[[  --with-packagelispdir=DIR
                        Directory for the package lisp files.]],
  [packagelispdir=["${withval}"]])
AC_LISPIFY_DIR(packagelispdir,[["${texsitedir}/tex-site.el"]])
AC_MSG_RESULT([[${packagelispdir}]])

AC_MSG_CHECKING([where the data files go])
AC_ARG_WITH(packagedatadir,
[[  --with-packagedatadir=DIR         Where the data files go.]],
  [packagedatadir=["${withval}"]])
AC_LISPIFY_DIR(packagedatadir,[["${texsitedir}/tex-site.el"]])
AC_MSG_RESULT([[${packagedatadir}]])

AC_LISPIFY_DIR(texsite,[["${auctexstartfile}"]],tex-site.el)

AC_MSG_CHECKING(where the info files go)
AC_MSG_RESULT([[${infodir}]])

AC_SUBST(packagedir)

if test $EMACS_FLAVOR = "xemacs" -a "$infodir" = '${prefix}/info'; then
  if test $packagedir != 'no'; then
   infodir='${packagedir}/info'
  fi
fi

AUCTEX_AUTO_DIR
AC_LISPIFY_DIR(autodir,"${texsitedir}/tex-site.el")

AC_PATH_PROG(TEX, tex, :)
AC_PATH_PROG(PDFTEX, pdftex, :)
AC_PATH_PROG(DVIPS, dvips, :)


dnl Preview related options.
if test "X${preview_enabled}" = Xyes
then
   AC_ARG_VAR(GS,[Ghostscript executable for batch operation])
   AC_CHECK_PROGS(GS, gs GSWIN32C.EXE, NONE)

   EMACS_LISP([[lispGS]],[[(if (member dir (list \"NONE\" (if (eq system-type 'windows-nt) \"GSWIN32C.EXE\" \"gs\"))) \"\" \`(defvar preview-gs-command ,dir))]],-no-site-file,[[dir]],[["${GS}"]])
   AC_SUBST(lispGS)

   dnl check to see if GS supports -dTextAlphaBits and -dGraphicsAlphaBits
   dnl Check to see if specific drivers are built in.
   dnl Need table of mappings, with priority

   AC_PATH_PROG_REQUIRED(LATEX, latex, [LaTeX not found, aborting!
   You must install LaTeX for preview to work.])

   AC_PATH_PROG(PDFLATEX, pdflatex)

   # Determine which latex-style components to install
   # To match .sty, .def, .cfg, but _not_ .drv
   TEXMFGEN=[`sed -n 's/^%<installer>.*file[{]\\([^}.]*\\.[sdc][tef][yfg]\\)[}].*/\\1/p' latex/preview.dtx`]
   # Replace newlines with spaces.
   TEXMFGEN="`echo ${TEXMFGEN}`"
   AC_SUBST(TEXMFGEN)

   AC_PATH_PROG_REQUIRED(TEX, tex, NONE)

   TEX_PATH_TEXMFDIR

   if test "x${texmfdir}" = "xno"
   then
     packagetexstyles="${packagedatadir}/latex"
     AC_LISPIFY_DIR(packagetexstyles,"${previewstartfile}")
     lisppackagetexstyles="(defvar preview-TeX-style-dir ${lisppackagetexstyles})"
     test "X${TEXHASH}" = X && TEXHASH=:
   else
     lisppackagetexstyles=
   fi
   AC_SUBST(lisppackagetexstyles)

   # Be very careful about assuming things about the available hash programs
   # MiKTeX comes with a braindead link to mktexlsr, apparently, so first
   # try the regular utility from them.
   AC_ARG_VAR(TEXHASH,[command to update the TeX filename database.
   Set to : to skip updating the database on installation.
   This is the default for --without-texmf-dir])

   if test "X${TEXHASH}" = "X"
   then
     AC_PATH_PROG(TEXHASH, texhash)
     AC_CHECK_PROG(TEXHASH, initexmf, initexmf -u)
     if test "X${TEXHASH}" = X
     then
        AC_PATH_PROGS(TEXHASH, mktexlsr MakeTeXls-R, :)
     fi
   fi

   AC_MSG_CHECKING([[for glaring installation conflicts]])
   exppackagelispdir="$packagelispdir"
   AC_FULL_EXPAND(exppackagelispdir)
   exppreviewstartfile="$previewstartfile"
   AC_FULL_EXPAND(exppreviewstartfile)

   EMACS_LISP(shadows,[[
     (concat
       (and (setq tmp (locate-library \"preview.elc\"))
            (not (string= (file-truename tmp)
                       (file-truename (expand-file-name \"preview.elc\"
                                         packagelispdir))))
            (format \"Conflicting previous installation in \`%s' found!\n\"
                    (file-name-directory tmp)))
       (and (setq tmp (locate-library \"preview-latex.el\"))
            (not (string= (file-truename tmp)
                          (file-truename previewstartfile)))
            (format \"Conflicting previous startup file \`%s' found!\n\" tmp)))]],,
     [[packagelispdir previewstartfile]],[["${exppackagelispdir}" "${exppreviewstartfile}"]])
   if test "NONE${shadows}" != NONE
   then
     conflictsmsg="Conflicts with previous installations have been detected.
   Please fix them before continuing.
   "
     AC_MSG_RESULT([[ouch!
   ]])
   AC_MSG_WARN([[${shadows}
   ]])
   else
     conflictsmsg=
     AC_MSG_RESULT([[probably none]])
   fi

   AC_SHELL_QUOTIFY(texmfdir)
   AC_SHELL_QUOTIFY(exec_prefix)
   AC_SHELL_QUOTIFY(libdir)
   AC_SHELL_QUOTIFY(previewtexmfdir)
   AC_SHELL_QUOTIFY(previewdocdir)
   AC_SHELL_QUOTIFY(previewstartfile)
   AC_SHELL_QUOTIFY(auctexdir)
   AC_SHELL_QUOTIFY(datadir)
   AC_SHELL_QUOTIFY(GS)
   AC_SHELL_QUOTIFY(TEXHASH)
   AC_SHELL_QUOTIFY(LATEX)
   AC_SHELL_QUOTIFY(PDFLATEX)
fi

AC_ARG_VAR(PERL,[Perl executable.  If set to :, some documentation
cannot be regenerated, but installation of an unmodified tarball will
succeed.])

if test "x$PERL" = x
then
   AC_PATH_PROG(PERL, perl, :)
fi

AC_ARG_VAR(MAKEINFO,[Makeinfo executable.  If set to :, some documentation
cannot be regenerated, but installation of an unmodified tarball will
succeed.])

AC_PATH_PROG(MAKEINFO, makeinfo, :)
AC_PATH_PROG(TEXI2HTML, texi2html, :)
AC_PATH_PROG(TEXI2DVI, texi2dvi, :)
AC_PATH_PROG(TEXI2PDF, texi2pdf, :)

AC_ARG_VAR(INSTALL_INFO, [install-info executable.  Set to : to skip making a dir file.  This is the default when installing into an XEmacs package.])

if test "X${INSTALL_INFO}" = X
then
  AC_PATH_PROG(INSTALL_INFO, install-info, :, ${PATH} /usr/sbin /sbin)
fi

AC_SHELL_QUOTIFY(prefix)
AC_SHELL_QUOTIFY(localstatedir)
AC_SHELL_QUOTIFY(packagedir)
AC_SHELL_QUOTIFY(packagelispdir)
AC_SHELL_QUOTIFY(packagedatadir)
AC_SHELL_QUOTIFY(lispdir)
AC_SHELL_QUOTIFY(infodir)
AC_SHELL_QUOTIFY(datadir)
AC_SHELL_QUOTIFY(autodir)
AC_SHELL_QUOTIFY(auctexstartfile)
AC_SHELL_QUOTIFY(EMACS)
AC_SHELL_QUOTIFY(INSTALL_INFO)
AC_SHELL_QUOTIFY(PERL)
AC_SHELL_QUOTIFY(MAKEINFO)
AC_SHELL_QUOTIFY(TEX)
AC_SHELL_QUOTIFY(PDFTEX)
AC_SHELL_QUOTIFY(DVIPS)
AC_SHELL_QUOTIFY(TEXI2HTML)
AC_SHELL_QUOTIFY(TEXI2DVI)
AC_SHELL_QUOTIFY(TEXI2PDF)

AC_OUTPUT(Makefile tex-site.el.out:tex-site.el.in doc/Makefile auctex.el preview.el latex/Makefile)


cat >&2 <<EOF

Congratulations!  Configuration of AUCTeX is complete.

Type "make" at the prompt to build.
EOF
