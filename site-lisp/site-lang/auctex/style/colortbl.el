;;; colortbl.el --- AUCTeX style for `colortbl.sty' (v1.0a)

;; Copyright (C) 2015, 2016 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-03-22
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; AUCTeX is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:

;; This file adds support for `colortbl.sty' (v1.0a) from 2012/02/13.
;; `colortbl.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "colortbl"
 (lambda ()

   ;; array.el is always loaded:
   (TeX-run-style-hooks "array")

   ;; Load color.el only if xcolor.el is not already loaded.  This is
   ;; mainly for the option `table' from xcolor.sty which loads
   ;; colortbl.sty, but we don't want to load color.el.
   (unless (member "xcolor" (TeX-style-list))
     (TeX-run-style-hooks "color"))

   (TeX-add-symbols
    ;; `TeX-arg-color' is provided by color.el,
    ;; `TeX-arg-xcolor' is provided by xcolor.el.
    '("columncolor" (TeX-arg-conditional (member "xcolor" (TeX-style-list))
					 (TeX-arg-xcolor)
				       (TeX-arg-color))
      [ TeX-arg-length "Left overhang" ] [ TeX-arg-length "Right overhang" ] )

    '("rowcolor"    (TeX-arg-conditional (member "xcolor" (TeX-style-list))
					 (TeX-arg-xcolor)
				       (TeX-arg-color))
      [ TeX-arg-length "Left overhang" ] [ TeX-arg-length "Right overhang" ] )

    '("cellcolor"   (TeX-arg-conditional (member "xcolor" (TeX-style-list))
					 (TeX-arg-xcolor)
				       (TeX-arg-color))
      [ TeX-arg-length "Left overhang" ] [ TeX-arg-length "Right overhang" ] )

    '("arrayrulecolor" (TeX-arg-conditional (member "xcolor" (TeX-style-list))
					 (TeX-arg-xcolor)
				       (TeX-arg-color)))

    '("doublerulesepcolor" (TeX-arg-conditional (member "xcolor" (TeX-style-list))
					 (TeX-arg-xcolor)
				       (TeX-arg-color))))

   (LaTeX-add-lengths "minrowclearance")

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("columncolor"  "[{[[")
				("rowcolor"     "[{[[")
				("cellcolor"    "[{[[")
				("arrayrulecolor"     "[{")
				("doublerulesepcolor" "[{"))
			      'function)))
 LaTeX-dialect)

;; colortbl.sty has one option `debugshow'.  I ignore that since it
;; would only take more time during insertation in a buffer and I
;; presume that not many users use it anyway.
(defvar LaTeX-colortbl-package-options nil
  "Package option for the colortbl package.")

;;; colortbl.el ends here
