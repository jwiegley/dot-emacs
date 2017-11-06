;;; tarticle.el - Special code for tarticle class.

;; Copyright (C) 2017 Free Software Foundation, Inc.

;; Author: Ikumi Keita <ikumi@ikumi.que.jp>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2017-03-23
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

;; Please write me.

;;; Code:

(TeX-load-style "jarticle")
(defvar LaTeX-tarticle-class-options LaTeX-jarticle-class-options
  "Class options for the tarticle class.")

(TeX-add-style-hook
 "tarticle"
 (lambda ()
   (TeX-run-style-hooks "jarticle" "plext"))
 LaTeX-dialect)

;;; tarticle.el ends here
