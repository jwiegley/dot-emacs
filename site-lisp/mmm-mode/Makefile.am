## Process this file with automake to produce Makefile.in

## The MMM Mode distribution is `flat', so we have no SUBDIRS macro.

lisp_LISP = mmm-compat.el mmm-vars.el mmm-utils.el mmm-auto.el \
  mmm-region.el mmm-class.el mmm-cmds.el mmm-mode.el \
  mmm-sample.el mmm-mason.el mmm-univ.el mmm-rpm.el mmm-cweb.el \
  mmm-noweb.el mmm-myghty.el mmm-erb.el mmm-defaults.el

info_TEXINFOS = mmm.texinfo

# This is a hack IMO.  Automake should recognize lisp files as
# "sources" and include them in the distribution, but it doesn't.
EXTRA_DIST = $(lisp_LISP) README.Mason FAQ

# See also `elisp-comp' for another hack.
