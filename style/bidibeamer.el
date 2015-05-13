;;; bidibeamer.el --- AUCTeX style for the bidibeamer class

;; Copyright (C) 2015 Free Software Foundation

;; Author: Tassilo Horn <tsdh@gnu.org>
;; Created: 2015-03-08
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

;; This file adds support for the bidibeamer class which offers the same
;; functionality and interface as latex-beamer, so we simply call the style
;; hook of the latter.

;;; Code:

(TeX-add-style-hook
 "bidibeamer"
 (lambda ()
   (TeX-run-style-hooks "beamer"))
 LaTeX-dialect)

;;; bidibeamer.el ends here
