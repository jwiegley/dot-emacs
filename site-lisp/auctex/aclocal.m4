# serial 1

dnl this was once done by Katsumi Yamaoka <yamaoka@jpl.org>, but
dnl pretty much no original code remains.

dnl EMACS_LISP takes 5 arguments.  $1 is the name of the shell
dnl variable to assign a value, $2 is a Lisp expression placed into
dnl shell double quotes (which has consequences for quoting and
dnl variable expansion).  $3 is a list of Emacs options evaluated before
dnl the expression itself, $4 is a list of Elisp variables that is
dnl assigned from the command line arguments from $5.

AC_DEFUN(EMACS_LISP, [
  elisp="$2"
  OUTPUT=./conftest-$$
  echo "${EMACS}" -batch $3 -eval "(let* (patsubst([$4], [\w+], [(\&(pop command-line-args-left))])(x ${elisp})) (write-region (if (stringp x) x (prin1-to-string x)) nil \"${OUTPUT}\"))" $5 >& AC_FD_CC 2>&1
  "${EMACS}" -batch $3 -eval "(let* (patsubst([$4], [\w+], [(\&(pop command-line-args-left))])(x ${elisp})) (write-region (if (stringp x) x (prin1-to-string x)) nil \"${OUTPUT}\"))" $5 >& AC_FD_CC 2>&1
  $1="`cat ${OUTPUT}`"
  echo "=> [$]{$1}" >& AC_FD_CC 2>&1
  rm -f ${OUTPUT}
])

# This generates a prefix variables $1 from the executable in $2.
# The executable is searched in PATH, and a potential bin/ or
# bin/architecture/ component is stripped from it.
AC_DEFUN(EMACS_PATH_PREFIX,[
  EMACS_LISP([$1],[[(condition-case nil (let*
    ((prefix (directory-file-name (file-name-directory (executable-find cmd))))
     (parent (directory-file-name (file-name-directory prefix))))
    (if (string= (file-name-nondirectory prefix) \"bin\")
        (setq prefix parent)
      (if (string= (file-name-nondirectory parent) \"bin\")
         (setq prefix (directory-file-name (file-name-directory parent)))))
    prefix) (error "NONE"))]],[[-no-site-file]],[[cmd]],[$2])])

AC_DEFUN(EMACS_PROG_EMACS, [
# Check for (X)Emacs, report its path, flavor and prefix

# Apparently, if you run a shell window in Emacs, it sets the EMACS
# environment variable to 't'.  Let's undo the damage.
if test "${EMACS}" = "t"; then
   EMACS=""
fi
AC_ARG_WITH(emacs,
  [  --with-emacs@<:@=PATH@:>@     Use Emacs to build (on PATH if given)],
  [if test "${withval}" = "yes"; then EMACS=emacs
   elif test "${withval}" = "no"; then EMACS=xemacs
   else EMACS="${withval}"; fi])

AC_ARG_WITH(xemacs,
  [  --with-xemacs@<:@=PATH@:>@    Use XEmacs to build (on PATH if given)],
  [if test "x${withval}" != xno
   then
     if test "x${with_emacs}" != xno -a "x${with_emacs}" != x
     then
       AC_MSG_ERROR([[cannot use both Emacs and XEmacs]])
     fi
     if test "x${withval}" = "xyes"
     then
       EMACS=xemacs
     else
       EMACS="${withval}"
     fi
   elif test "x${with_emacs}" = xno
   then
     AC_MSG_ERROR([[need to use either Emacs or XEmacs]])
   fi])

# "${prefix}/bin" is for Windows users
AC_PATH_PROGS(EMACS, ${EMACS} emacs xemacs, "", ${PATH} "${prefix}/bin" )
if test -z "${EMACS}"; then
  AC_MSG_ERROR([(X)Emacs not found!  Aborting!])
fi

AC_MSG_CHECKING([if ${EMACS} is XEmacs])
EMACS_LISP(XEMACS,
	[[(if (featurep (quote xemacs)) \"yes\" \"no\")]],[[-no-site-file]])
if test "${XEMACS}" = "yes"; then
  EMACS_FLAVOR=xemacs
  EMACS_NAME="XEmacs"
elif test "${XEMACS}" = "no"; then
  EMACS_FLAVOR=emacs
  EMACS_NAME="Emacs"
else
  AC_MSG_ERROR([Unable to run ${EMACS}!  Aborting!])
fi
  AC_MSG_RESULT(${XEMACS})
  AC_SUBST(XEMACS)
  AC_SUBST(EMACS_FLAVOR)
  AC_MSG_CHECKING([for ${EMACS_NAME} prefix])
  EMACS_PATH_PREFIX([[emacsprefix]],[["${EMACS}"]])
  AC_MSG_RESULT([["${emacsprefix}"]])
])

AC_DEFUN(AC_DATE_VERSION_FROM_CHANGELOG, [
AC_MSG_CHECKING([for date in ChangeLog])
$1=[`sed -n '1s/^\([-0-9][-0-9]*\).*/\1/p' "$3"`]
if test "X${$1}" = X
then
  AC_MSG_ERROR([[not found]])
fi
AC_MSG_RESULT(${$1})
AC_MSG_CHECKING([for release in ChangeLog])
$2=[`sed -n '2,/^[0-9]/s/.*Version \(.*\) released\..*/\1/p' "$3"`]
if test "X${$2}" = X
then
  $2=${$1}
  AC_MSG_RESULT([not found, using ${$2} instead])
else
  AC_MSG_RESULT([${$2}])
fi
])

AC_DEFUN(EMACS_CHECK_VERSION, [
AC_MSG_CHECKING([if ${EMACS_NAME} is recent enough])
EMACS_LISP(result,[(cond ((< emacs-major-version $1) \"no\")
			 ((> emacs-major-version $1) \"yes\")
			 ((< emacs-minor-version 0$2) \"no\")
			 (t \"yes\"))],[[-no-site-file]])
AC_MSG_RESULT([${result}])
if test "${result}" != "yes"
then
  AC_MSG_ERROR([This package requires at least ${EMACS_NAME} version $1.$2  Aborting!])
fi
])

dnl Look for an installation directory under given prefixes.
dnl $1 is the variable name we are looking for.
dnl $2 is a list of prefixes to try as a list of shell words
dnl $3 is a Lisp expression giving a list of directory names
dnl    those should be be either nil or a relative path like "tex/latex".
dnl   Those names are tried in turn, and every one of them is matched
dnl   against the tail of each location in $4.  nil matches everything,
dnl   it is a wildcard.
dnl $4 is Lisp expression giving a list of locations where to find names.
dnl   A location is only considered if it is nonnil, an existing
dnl   absolute directory,
dnl   and is a subdirectory of one of the given prefixes.
dnl $5,$6,$7 are additional arguments for the elisp call
AC_DEFUN(EMACS_EXAMINE_INSTALLATION_DIR,
 [  for currentprefix in $2
  do
  expprefix="${currentprefix}"
  AC_FULL_EXPAND(expprefix)
  EMACS_LISP([$1],
    [(catch 22
       (let (reldir (dirs $4))
	  (dolist (name $3 \"NONE\")
	    (dolist (dir dirs)
	      (when (and dir
	      	         (setq dir (directory-file-name dir))
                         (file-name-absolute-p dir)
	      	         (file-directory-p dir)
	                 (not (string-match \"\\\\\`\\\\.\\\\.\"
                           (setq reldir (file-relative-name dir expanded))))
			 (not (file-name-absolute-p reldir))
                         (let ((name name) (dir dir))
		           (while (and dir name
		                       (string= (file-name-nondirectory dir)
		                                (file-name-nondirectory name))
                              (setq dir (file-name-directory dir)
				   name (file-name-directory name))
			      (if (and dir name)
			         (setq dir (directory-file-name dir)
			              name (directory-file-name name)))))
		            (null name))
		   (throw 22
                      (if (string= reldir \".\") (directory-file-name prefix)
                        (concat (file-name-as-directory prefix)
                                reldir)))))))))],[$5],
  [prefix expanded $6],["${currentprefix}" "${expprefix}" $7])
  if test "[$]$1" != NONE; then break; fi; done])

AC_DEFUN(EMACS_PATH_PACKAGEDIR,
 [AC_ARG_WITH(packagedir,
    [  --with-packagedir=DIR   package DIR for XEmacs],
    [packagedir="`echo ${withval} | sed 's/^~\//${HOME}\//;s/[[\/\\]]$//'`"],
    [if test ${EMACS_FLAVOR} = xemacs; then
      AC_MSG_CHECKING([for XEmacs package directory])
      EMACS_EXAMINE_INSTALLATION_DIR(packagedir,
        [['${datadir}/xemacs/xemacs-packages' \
	  '${libdir}/xemacs/xemacs-packages' \
          '${datadir}' '${libdir}' "${emacsprefix}"]],
        [[(list \"xemacs/site-packages\" \"xemacs/xemacs-packages\"
                \"site-packages\" \"xemacs-packages\")]],
        [[(if (boundp 'late-packages)
	      (append late-packages last-packages early-packages)
	    (append late-package-hierarchies last-package-hierarchies
		    early-package-hierarchies))]])
      if test "x${packagedir}" = xNONE -o -z "${packagedir}"; then
        AC_MSG_ERROR([not found, exiting!])
      fi
      AC_MSG_RESULT(${packagedir})
    else
      packagedir=no
    fi])
  AC_SUBST(packagedir)])

AC_DEFUN(EMACS_PATH_LISPDIR, [
  AC_MSG_CHECKING([where lisp files go])
  AC_ARG_WITH(lispdir,
    [  --with-lispdir=DIR      A place in load-path for Lisp files; most
                          files will be place in a subdirectory.],
    [[lispdir="${withval}"]])
  if test "X${lispdir}" = X; then
     if test "X${packagedir}" = Xno; then
       # Test paths relative to prefixes
       EMACS_EXAMINE_INSTALLATION_DIR(lispdir,
         [['${datadir}/'${EMACS_FLAVOR} '${libdir}/'${EMACS_FLAVOR} \
	   "${emacsprefix}/share/${EMACS_FLAVOR}" \
           '${datadir}' '${libdir}' "${emacsprefix}"]],
	 [[(list \"${EMACS_FLAVOR}/site-lisp\" \"${EMACS_FLAVOR}/site-packages\"
	         \"site-lisp\" \"site-packages\")]], load-path)
       if test "${lispdir}" = "NONE"; then
	 # No? notify user.
	 AC_MSG_ERROR([Cannot locate lisp directory,
use  --with-lispdir, --datadir, or possibly --prefix to rectify this])
       fi
     else
       # XEmacs
       lispdir="${packagedir}/lisp"
     fi
    fi
  AC_MSG_RESULT([[${lispdir}]])
  AC_SUBST(lispdir)
])


AC_DEFUN(TEX_PATH_TEXMFDIR,
 [
AC_ARG_WITH(texmf-dir,
[  --with-texmf-dir=DIR    TEXMF tree to install into,
                         or --without-texmf-dir for runtime config],
 [ texmfdir="${withval}" ;
   if test "x${texmfdir}" = xno
   then
     previewtexmfdir="${packagedatadir}/latex"
     previewdocdir="${packagedatadir}/doc"
   else
     AC_FULL_EXPAND(withval)
     if test ! -d "${withval}"  ; then
        AC_MSG_ERROR([--with-texmf-dir="${texmfdir}": Directory does not exist])
     fi
     previewtexmfdir="${texmfdir}/tex/latex/preview"
     previewdocdir="${texmfdir}/doc/latex/styles"
   fi
   ])

AC_ARG_WITH(tex-dir,
 [  --with-tex-dir=DIR      Location to install preview TeX sources],
 [ previewtexmfdir="${withval}" ;
   AC_FULL_EXPAND(withval)
   if test ! -d "${withval}"  ; then
      AC_MSG_ERROR([--with-tex-dir="${previewtexmfdir}": Directory does not exist])
   fi
   ])

AC_ARG_WITH(doc-dir,
  [  --with-doc-dir=DIR      Location to install preview.dvi],
  [ previewdocdir="${withval}" ;
   AC_FULL_EXPAND(withval)
   if test ! -d "${withval}"  ; then
      AC_MSG_ERROR([--with-doc-dir="${previewdocdir}": Directory does not exist])
   fi
   ])

# First check for docstrip.cfg information -- removed.  Too high
# likelihood to pick up a user preference instead of a system setting.

# Next
# kpsepath -n latex tex
# and then go for the following in its output:
# a) first path component in datadir/prefix ending in tex/latex// (strip trailing
# // and leading !!):  "Searching for TDS-compliant directory."  Install
# in preview subdirectory.
# b) first absolute path component ending in // "Searching for directory
# hierarchy"  Install in preview subdirectory.
# c) anything absolute.  Install both files directly there.

if test "x${texmfdir}" != xno ; then
if test "x${previewtexmfdir}" = x ; then

AC_MSG_CHECKING([for prefix from kpsepath])

EMACS_PATH_PREFIX(texprefix,kpsepath)

if test "x${texprefix}" != "xNONE"
then

AC_MSG_RESULT([["${texprefix}"]])

AC_MSG_CHECKING([for TDS-compliant directory])

pathoutput="`kpsepath -n latex tex`"

EMACS_EXAMINE_INSTALLATION_DIR(texmfdir,
  [['${datadir}/texmf' "${texprefix}/share/texmf-local" "${texprefix}/share/texmf" "${texprefix}/texmf-local" "${texprefix}/texmf"]],
  [[(list nil)]],
  [[(mapcar (lambda(x)
              (and (string-match \"\\\\\`!*\\\\(.*\\\\)/tex/latex//+\\\\'\" x)
	           (match-string 1 x)))
      (append (split-string pathoutput \";\")
             (split-string pathoutput \":\")))]],
    [[-no-site-file]],
    [[pathoutput]],[["${pathoutput}"]])

if test -n "${texmfdir}" -a "${texmfdir}" != "NONE" ; then
   previewdocdir="${texmfdir}/doc/latex/styles"
   previewtexmfdir="${texmfdir}/tex/latex/preview"
fi

if test -z "${previewtexmfdir}" -o "${previewtexmfdir}" = no  ; then

AC_MSG_RESULT([no])
AC_MSG_CHECKING([for TeX directory hierarchy])

EMACS_EXAMINE_INSTALLATION_DIR(texmfdir,
  [['${datadir}/texmf' "${texprefix}/share/texmf-local" "${texprefix}/share/texmf" "${texprefix}/texmf-local" "${texprefix}/texmf" '${datadir}' "${texprefix}/share" "${texprefix}"]],
  [[(list nil)]],
  [[(mapcar (lambda(x)
              (and (string-match \"\\\\\`!*\\\\(.*[^/]\\\\)//+\\\\'\" x)
	           (match-string 1 x)))
      (append (split-string pathoutput \";\")
             (split-string pathoutput \":\")))]],
    [[-no-site-file]],
    [[pathoutput]],[["${pathoutput}"]])

if test -n "${texmfdir}" -a "${texmfdir}" != "NONE" ; then
   previewtexmfdir="${texmfdir}/preview"
   previewdocdir="${texmfdir}/preview"
fi
fi

if test -z "${previewtexmfdir}" -o "${previewtexmfdir}" = no  ; then

AC_MSG_RESULT([no])
AC_MSG_CHECKING([for TeX input directory])

EMACS_EXAMINE_INSTALLATION_DIR(texmfdir,
  [['${datadir}' "${texprefix}/share" "${texprefix}"]],
  [[(list nil)]],
  [[(mapcar (lambda(x)
              (and (string-match \"\\\\\`!*\\\\(.*[^/]\\\\)/?\\\\'\" x)
	           (match-string 1 x)))
      (append (split-string pathoutput \";\")
             (split-string pathoutput \":\")))]],
    [[-no-site-file]],
    [[pathoutput]],[["${pathoutput}"]])

if test -n "${texmfdir}" -a "${texmfdir}" != "NONE" ; then
   previewtexmfdir="${texmfdir}"
   previewdocdir="${texmfdir}"
fi
fi
fi

if test -z "${previewtexmfdir}" -o "${previewtexmfdir}" = no  ; then

AC_MSG_RESULT([no])
	AC_MSG_ERROR([Cannot find the texmf directory!
Please use --with-texmf-dir=dir to specify where the preview tex files go])
fi

AC_MSG_RESULT(${texmfdir})
fi
fi

echo Preview will be placed in ${previewtexmfdir}
echo Preview docs will be placed in ${previewdocdir}
AC_SUBST(texmfdir)
AC_SUBST(previewtexmfdir)
AC_SUBST(previewdocdir)])

AC_DEFUN(AC_FULL_EXPAND,
[ __ac_tmp_oldprefix__="${prefix}"
  __ac_tmp_oldexec_prefix__="$exec_prefix"
 test "x${prefix}" = xNONE && prefix="${ac_default_prefix}"
 test "x${exec_prefix}" = xNONE && exec_prefix='${prefix}'
 while :;do case "[$]$1" in *\[$]*) __ac_tmp__='s/[[\`"-"]]/\\&/g'
eval "$1=`sed ${__ac_tmp__} <<EOF
[$]$1
EOF
`";; *) break ;; esac; done
  prefix="${__ac_tmp_oldprefix__}"
  exec_prefix="${__ac_tmp_oldexec_prefix__}" ])

AC_DEFUN(AC_CHECK_PROG_REQUIRED, [
AC_CHECK_PROG($1, $2, NONE)
if test "${$1}"x = NONEx ; then
   AC_MSG_ERROR([$3])
fi
])

AC_DEFUN(AC_CHECK_PROGS_REQUIRED, [
AC_CHECK_PROGS($1, $2, NONE)
if test "${$1}"x = NONEx ; then
   AC_MSG_ERROR([$3])
fi
])


AC_DEFUN(AC_PATH_PROG_REQUIRED, [
AC_PATH_PROG($1, $2, NONE)
if test "${$1}"x = NONEx ; then
   AC_MSG_ERROR([$3])
fi
])

AC_DEFUN(AC_PATH_PROGS_REQUIRED, [
AC_PATH_PROGS($1, $2, NONE)
if test "${$1}"x = NONEx ; then
   AC_MSG_ERROR([$3])
fi
])


dnl
dnl Check whether a function exists in a library
dnl All '_' characters in the first argument are converted to '-'
dnl
AC_DEFUN(EMACS_CHECK_LIB, [
if test -z "$3"; then
	AC_MSG_CHECKING(for $2 in $1)
fi
library=`echo $1 | tr _ -`
EMACS_LISP(EMACS_cv_SYS_$1,(progn (fmakunbound '$2) (condition-case nil (progn (require '${library}) (fboundp '$2)) (error (prog1 nil (message \"${library} not found\"))))))
if test "${EMACS_cv_SYS_$1}" = "nil"; then
	EMACS_cv_SYS_$1=no
fi
if test "${EMACS_cv_SYS_$1}" = "t"; then
	EMACS_cv_SYS_$1=yes
fi
HAVE_$1=${EMACS_cv_SYS_$1}
AC_SUBST(HAVE_$1)
if test -z "$3"; then
	AC_MSG_RESULT(${HAVE_$1})
fi
])

dnl
dnl Check whether a library is require'able
dnl All '_' characters in the first argument are converted to '-'
dnl
AC_DEFUN(EMACS_CHECK_REQUIRE, [
if test -z "$2"; then
	AC_MSG_CHECKING(for $1)
fi
library=`echo $1 | tr _ -`
EMACS_LISP($1,
	[(condition-case nil (require '${library} ) \
	(error (prog1 nil (message \"${library} not found\"))))])
if test "$$1" = "nil"; then
	$1=no
fi
if test "$$1" = "${library}"; then
	$1=yes
fi
HAVE_$1=$$1
AC_SUBST(HAVE_$1)
if test -z "$2"; then
	AC_MSG_RESULT(${HAVE_$1})
fi
])

dnl
dnl Perform sanity checking and try to locate the auctex package
dnl
AC_DEFUN(EMACS_CHECK_AUCTEX, [
AC_MSG_CHECKING(for the location of AUCTeX's tex-site.el)
AC_ARG_WITH(tex-site,[  --with-tex-site=DIR     Location of AUCTeX's tex-site.el, if not standard],
 [ auctexdir="${withval}" ;
   AC_FULL_EXPAND(withval)
   if test ! -d "${withval}"  ; then
      AC_MSG_ERROR([--with-tex-site=${auctexdir}: Directory does not exist])
   fi
])
if test -z "${auctexdir}" ; then
  AC_CACHE_VAL(EMACS_cv_ACCEPTABLE_AUCTEX,[
    EMACS_LISP(EMACS_cv_ACCEPTABLE_AUCTEX,
	[[(condition-case nil
             (directory-file-name (file-name-directory
                (locate-library \"tex-site\")))
	    (error \"\"))]])
    if test -z "${EMACS_cv_ACCEPTABLE_AUCTEX}" ; then
	AC_MSG_ERROR([Can't find AUCTeX!  Please install it!
Check the PROBLEMS file for details.])
  fi
  ])
  auctexdir="${EMACS_cv_ACCEPTABLE_AUCTEX}"
fi
AC_MSG_RESULT(${auctexdir})
AC_SUBST(auctexdir)
])

dnl
dnl Check if (X)Emacs supports international characters,
dnl i.e. provides MULE libraries and runs in multibyte mode.
dnl
AC_DEFUN(EMACS_CHECK_MULE, [
AC_MSG_CHECKING(for MULE support)
EMACS_CHECK_REQUIRE(mule,silent)
if test "${HAVE_mule}" = "yes" && test "X${EMACS_UNIBYTE}" = X; then
  MULESRC="tex-jp.el"
  MULEELC="tex-jp.elc"
  AC_MSG_RESULT(yes)
else
  AC_MSG_RESULT(no)
  if test "X${EMACS_UNIBYTE}" != X; then
    AC_MSG_WARN([[EMACS_UNIBYTE environment variable set.
Disabling features requiring international character support.]])
  fi
fi
AC_SUBST(MULESRC)
AC_SUBST(MULEELC)
])

dnl
dnl MAKEINFO_CHECK_MACRO( MACRO, [ACTION-IF-FOUND
dnl					[, ACTION-IF-NOT-FOUND]])
dnl
AC_DEFUN(MAKEINFO_CHECK_MACRO,
[if test -n "${MAKEINFO}" -a "${makeinfo}" != ":"; then
  AC_MSG_CHECKING([if ${MAKEINFO} understands @$1{}])
  echo \\\\input texinfo > conftest.texi
  echo @$1{test} >> conftest.texi
  if ${MAKEINFO} conftest.texi > /dev/null 2> /dev/null; then
    AC_MSG_RESULT(yes)
    ifelse([$2], , :, [$2])
  else
    AC_MSG_RESULT(no)
    ifelse([$3], , :, [$3])
  fi
  rm -f conftest.texi conftest.info
fi
])

dnl
dnl MAKEINFO_CHECK_MACROS( MACRO ... [, ACTION-IF-FOUND
dnl					[, ACTION-IF-NOT-FOUND]])
dnl
AC_DEFUN(MAKEINFO_CHECK_MACROS,
[for ac_macro in $1; do
    MAKEINFO_CHECK_MACRO(${ac_macro}, $2,
	[MAKEINFO_MACROS="-D no-${ac_macro} ${MAKEINFO_MACROS}"
	$3])dnl
  done
AC_SUBST(MAKEINFO_MACROS)
])

AC_DEFUN(AC_SHELL_QUOTIFY,
[$1=["`sed 's/[^-0-9a-zA-Z_./:$]/\\\\&/g;s/[$]\\\\[{(]\\([^)}]*\\)\\\\[})]/${\\1}/g' <<EOF]
[$]$1
EOF
`"])

dnl
dnl Check if build directory is valid.
dnl The directory should not be part of `load-path'
dnl
AC_DEFUN(VALID_BUILD_DIR, [
  AC_MSG_CHECKING([if build directory is valid])
  EMACS_LISP(valid_build_dir,
    [[(if (or (member (directory-file-name default-directory) load-path)\
	      (member (file-name-as-directory default-directory) load-path))\
	 \"no\" \"yes\")]])
  if test "${valid_build_dir}" = "no"; then
    AC_MSG_ERROR([Build directory inside load-path!  Aborting!])
  else
    AC_MSG_RESULT([yes])
  fi
])

# AUCTEX_AUTO_DIR
# ---------------
# Set the directory containing AUCTeX automatically generated global style
# hooks.
AC_DEFUN(AUCTEX_AUTO_DIR,
[AC_MSG_CHECKING([where automatically generated global style hooks go])
 AC_ARG_WITH(auto-dir,
	     [  --with-auto-dir=DIR     directory containing AUCTeX automatically generated
			  global style hooks],
	     [autodir="${withval}"],
	     [autodir='${localstatedir}/auctex'])
 AC_MSG_RESULT([${autodir}])
 AC_SUBST(autodir)
])

# AC_LISPIFY_DIR
# First argument is a variable name where a lisp expression is to be
# substituted with AC_SUBST and "lisp" prepended.
# lispdir is used for two purposes: any relative names are resolved
# relative to lispdir, and the lispification uses relative file names
# in relation to the second argument if the target dir is in the
# lispdir hierarchy.
# Second argument is a path to be resolved relatively to the filename
# in the third argument.
# If a third argument is given, it specifies a path specification
# to be expanded relative to the resulting directory.
AC_DEFUN(AC_LISPIFY_DIR,[
 tmpdir="[$]{$1}"
 AC_FULL_EXPAND(tmpdir)
 explispdir="[$]{lispdir}"
 AC_FULL_EXPAND(explispdir)
 expstartup=$2
 AC_FULL_EXPAND(expstartup)
EMACS_LISP([lisp$1],[[(progn (setq path (directory-file-name path))
  (if (or target
          (not (string= (car load-path) (directory-file-name (car load-path)))))
    (setq path (file-name-as-directory path)))
  (setq path (expand-file-name path lispdir))
  (setq startupdir (file-name-directory (expand-file-name startup lispdir)))
  (prin1-to-string
    (if (or (string-match \"\\\\\`\\\\.\\\\.\"
              (setq relname (file-relative-name startupdir lispdir)))
            (file-name-absolute-p relname)
	    (string-match \"\\\\\`\\\\.\\\\.\"
              (setq relname (file-relative-name path lispdir)))
 	    (file-name-absolute-p relname))
	  (concat path target)
	(cond (target
	       \`(expand-file-name
                   ,(file-relative-name (concat path target) startupdir)
	           (file-name-directory load-file-name)))
              ((string= path startupdir)
	         '(file-name-directory load-file-name))
	      ((string= path (directory-file-name startupdir))
                 '(directory-file-name (file-name-directory load-file-name)))
              (t
	       \`(expand-file-name
                   ,(file-relative-name path startupdir)
	           (file-name-directory load-file-name)))))))]],
       -no-site-file,[[path lispdir startup target]],
  [["${tmpdir}" "${explispdir}" "${expstartup}" $3]])
   AC_SUBST([lisp$1])
   AC_SUBST([$1])])
