### Makefile --- create info, ps, pdf and html files for package X-Symbol

## Copyright (C) 1998-2003 Free Software Foundation, Inc.
##
## Author: Christoph Wedler <wedler@users.sourceforge.net>
## Version: 4.5
## Keywords: fonts, WYSIWYG, LaTeX, HTML, wp, math
## X-URL: http://x-symbol.sourceforge.net/

# This file is not part of XEmacs.

# This software is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the
# Free Software Foundation; either version 2, or (at your option) any
# later version.

# This software is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# for more details.

# You should have received a copy of the GNU General Public License
# along with This software; see the file COPYING.  If not, write to
# the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
# Boston, MA 02111-1307, USA.


MAKEINFO = makeinfo --no-split
TEXI2DVI = texi2dvi -t @afourpaper
DVIPS = dvips
TEXI2PDF = texi2pdf -t @afourpaper
TEXI2HTML = texi2html -Verbose -expand info -split chapter -menu -number \
		-lang="en" -top_file="index.html" -init_file="x-symbol.init"

EMACS = xemacs
EFLAG = -q --no-site-file --batch
EFLAG_FINAL = --kill

# pdfTeX, Version 3.14159-13d (Web2C 7.3.1) has problems with @value in both
# @url and @uref.  Use expanded texi file for texi2pdf...
PRELOADS = -eval "(progn \
  (defun texi-expand (last) \
    (let (replaces text) \
      (goto-char (point-min)) \
      (while (re-search-forward \"^@set[ \\t]+\\\\([a-zA-Z-_]+\\\\)[ \\t]+\\\\(.+\\\\)\" \
                                nil t) \
        (if (setq text (assoc (match-string 1) replaces)) \
            (if last (setcdr text (match-string 2))) \
          (push (cons (match-string 1) (match-string 2)) replaces))) \
      (setq text \
            (concat \"@value{\\\\(\" (regexp-opt (mapcar 'car replaces)) \"\\\\)}\")) \
      (goto-char (point-min)) \
      (while (re-search-forward text nil t) \
        (replace-match (cdr (assoc (match-string 1) replaces)) t t)) \
      (write-file (concat buffer-file-name \"-exp\")))))"

ifeq ($(EMACS),emacs)
GNU = -D GNU
PRELOADS += -eval "(texi-expand nil)"
else
GNU =
PRELOADS += -eval "(texi-expand t)"
endif

info:	x-symbol.info
x-symbol.info: x-symbol.texi
	$(MAKEINFO) $(GNU) x-symbol.texi

ps:	x-symbol.ps
x-symbol.ps: x-symbol.dvi
	$(DVIPS) -o x-symbol.ps x-symbol.dvi
x-symbol.dvi: x-symbol.texi
	$(TEXI2DVI) x-symbol.texi

pdf:	x-symbol.pdf
x-symbol.pdf: x-symbol.texi-exp
	$(TEXI2PDF) x-symbol.texi-exp
x-symbol.texi-exp: x-symbol.texi
	$(EMACS) $(EFLAG) x-symbol.texi $(PRELOADS) $(EFLAG_FINAL)

html:	index.html
index.html: x-symbol.texi x-symbol.init
	$(TEXI2HTML) x-symbol.texi

all:	info ps pdf html

clean:
	rm -f x-symbol x-symbol.aux x-symbol.cp* \
                x-symbol.dvi x-symbol.fn* x-symbol.ky* \
                x-symbol.log x-symbol.pg* x-symbol.ps \
		x-symbol.texi-exp x-symbol.pdf \
                x-symbol.toc x-symbol.tp x-symbol.tp \
                x-symbol.vr* x-symbol.info* x-symbol*.html index.html
