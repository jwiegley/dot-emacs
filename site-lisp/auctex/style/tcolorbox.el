;;; tcolorbox.el --- AUCTeX style for `tcolorbox.sty'

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Tassilo Horn <tsdh@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-01-04
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

;; This file adds support for `tcolorbox.sty'.

;;; Code:

;; TODO: There are tons of more options...
(defvar LaTeX-tcolorbox-keyval-options
  '(("title")
    ("notitle")
    ("adjusted title")
    ("adjust text")
    ("squeezed title")
    ("squeezed title*")
    ("detach title")
    ("attach title")
    ("attach title to upper")
    ("upperbox" ("visible" "invisible"))
    ("visible")
    ("invisible")
    ("lowerbox" ("visible" "invisible" "ignored"))
    ("savelowerto")
    ("lower separated" ("true" "false"))
    ("savedelimiter")
    ("colframe")
    ("colback")
    ("title filled" ("true" "false"))
    ("colbacktitle")
    ("colupper")
    ("collower")
    ("coltext")
    ("coltitle")
    ("fontupper")
    ("fontlower")
    ("fonttitle")
    ("width")
    ("height")
    ("after")
    ("before")))

(TeX-add-style-hook
 "tcolorbox"
 (lambda ()
   ;; TODO: There are many more macros
   (TeX-add-symbols
    "tcblower"
    '("tcbset"
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options))
    '("tcbsetforeverylayer"
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options)))
   (LaTeX-add-environments
    '("tcolorbox" LaTeX-env-args
      [TeX-arg-key-val LaTeX-tcolorbox-keyval-options])))
 LaTeX-dialect)

;;; tcolorbox.el ends here
