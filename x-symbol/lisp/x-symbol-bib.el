;;; x-symbol-bib.el --- token language "BibTeX macro" for package x-symbol

;; Copyright (C) 2002 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.4.X
;; Keywords: WYSIWYG, LaTeX, HTML, wp, math, internationalization
;; X-URL: http://x-symbol.sourceforge.net/

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; If you want to use package x-symbol, please visit the URL (use
;; \\[x-symbol-package-web]) and read the info (use \\[x-symbol-package-info]).

;; 

;;; Code:

(provide 'x-symbol-bib)
(require 'x-symbol-tex)


;;;===========================================================================
;;;  General language accesses, see `x-symbol-language-access-alist'
;;;===========================================================================

(defcustom x-symbol-bib-auto-style '(t nil nil nil nil nil)
  "TODO"
  :group 'x-symbol-bib
  :group 'x-symbol-mode
  :type 'x-symbol-auto-style)

(defcustom x-symbol-bib-modeline-name "bib"
  "*String naming the language TeX in the modeline."
  :group 'x-symbol-bib
  :type 'string)

(defcustom x-symbol-bib-header-groups-alist x-symbol-tex-header-groups-alist
  "*If non-nil, used in TeX specific grid/menu.
See `x-symbol-header-groups-alist'."
  :group 'x-symbol-bib
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-bib-electric-ignore x-symbol-tex-electric-ignore
  "*Additional TeX version of `x-symbol-electric-ignore'."
  :group 'x-symbol-bib
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)

(defcustom x-symbol-bib-class-alist x-symbol-tex-class-alist
    "Alist for TeX's token classes displayed by info in echo area.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-bib
  :group 'x-symbol-info-strings
  :type 'x-symbol-class-info)

(defcustom x-symbol-bib-class-face-alist x-symbol-tex-class-face-alist
  "Alist for TeX's color scheme in TeX's grid and info.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-bib
  :group 'x-symbol-input-init
  :group 'x-symbol-info-general
  :type 'x-symbol-class-faces)


;;;===========================================================================
;;;  foo
;;;===========================================================================

(defvar x-symbol-bib-token-grammar
  '(x-symbol-make-grammar
    :encode-spec (?\\ (math . "[a-z@-Z]"))
    :decode-regexp "\\\\\\(?:[@A-Za-z]+\\|[-{}#_&]\\)\\|{\\\\\\(?:[ckvuHr]\\(?: [A-Za-z]\\|{}\\|\\\\ \\)\\|[@A-Za-z]+\\|[.~^\"'`=]\\(?:[A-Za-z]\\|{}\\|\\\\[ij]\\)\\)}"
    :decode-spec (?\\)
    :token-list x-symbol-bib-default-token-list)
  "Token grammar for language `bib'.")

(defvar x-symbol-bib-input-token-grammar
  '("\\\\\\(?:[@A-Za-z]+\\|[-{}#_&]\\)\\'\\|{\\\\\\(?:[ckvuHr]\\(?: [A-Za-z]\\|{}\\|\\\\ \\)\\|[@A-Za-z]+\\|[.~^\"'`=]\\(?:[A-Za-z]\\|{}\\|\\\\[ij]\\)\\)}\\'"
    ?\\ (math . "[a-z@-Z]"))
  "Grammar of input method Token for language `bib'.")

(defvar x-symbol-bib-required-fonts x-symbol-tex-required-fonts
  "List of features providing fonts for language `bib'.")

(defvar x-symbol-bib-user-table nil
  "User table defining TeX macros, used in `x-symbol-bib-table'.")

(defvar x-symbol-bib-table
  (append x-symbol-bib-user-table x-symbol-tex-table)
  "Complete table defining Unique TeX macros, see `x-symbol-bib-user-table'.
Default value uses all definitions in `x-symbol-bib-table'.")

(defvar x-symbol-bib-generated-data nil
  "Internal.")

(defun x-symbol-bib-default-token-list (tokens)
  (if (stringp tokens)
      (list (list (concat "{" tokens "}")))
    (mapcar (lambda (x)
	      (cons x (if (string-match "\\\\[A-Za-z]+\\'" x) 'math)))
	    tokens)))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-bib.el ends here
