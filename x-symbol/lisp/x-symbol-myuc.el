;;; x-symbol-myuc.el --- example token language "My Unicode" from manual

;; Copyright (C) 1998-1999 Christoph Wedler
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.1
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
;; This file defines the example token language "My Unicode" from the manual of
;; package X-Symbol.

;; The following lines define the major mode `myuc-mode':

;;(put 'myuc-mode 'font-lock-defaults '(myuc-font-lock-keywords t t))
;;(defvar myuc-font-lock-keywords '(("##" (0 font-lock-type-face))))
;;(defun myuc-mode ()
;;  (interactive)
;;  (fundamental-mode)
;;  (setq mode-name "MyUnicode")
;;  (setq major-mode 'myuc-mode))
;;(push '("\\.myuc\\'" . myuc-mode) auto-mode-alist)

;; Put the following code into your ~/.emacs to register language `myuc':

;;(defvar x-symbol-myuc-name "My Unicode")
;;(defvar x-symbol-myuc-modes '(myuc-mode))
;;(x-symbol-register-language 'myuc 'x-symbol-myuc x-symbol-myuc-modes)

;;; Code:

(provide 'x-symbol-myuc)
(require 'x-symbol-vars)
;; If you want to make the file compilable without X-Symbol, you could use the
;; following instead (require 'x-symbol-vars):
;;   (custom-add-load 'x-symbol-myuc 'x-symbol-vars)
(eval-when-compile (require 'cl))


(defvar x-symbol-myuc-required-fonts nil)

(defvar x-symbol-myuc-modeline-name "myuc")
(defvar x-symbol-myuc-header-groups-alist nil)

(defvar x-symbol-myuc-class-alist
  '((VALID "My Unicode" (x-symbol-info-face))
    (INVALID "no My Unicode" (x-symbol-emph-info-face))))
(defvar x-symbol-myuc-class-face-alist nil)
(defvar x-symbol-myuc-electric-ignore nil)

(defvar x-symbol-myuc-font-lock-keywords nil)
(defvar x-symbol-myuc-image-keywords nil)
(defvar x-symbol-myuc-master-directory 'ignore)
(defvar x-symbol-myuc-image-searchpath '("./"))
(defvar x-symbol-myuc-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-myuc-image-file-truename-alist nil)

(defvar x-symbol-myuc-case-insensitive 'upcase)
(defvar x-symbol-myuc-token-shape '(?# "#[0-9A-Fa-f]+\\'" . "[0-9A-Fa-f]"))
(defvar x-symbol-myuc-exec-specs '(nil (nil . "#[0-9A-Fa-f]+")))
(defvar x-symbol-myuc-input-token-ignore nil)

(defun x-symbol-myuc-default-token-list (tokens)
  (list (format "#%X" (car tokens))))

(defvar x-symbol-myuc-token-list 'x-symbol-myuc-default-token-list)
(defvar x-symbol-myuc-user-table nil)

(defvar x-symbol-myuc-xsymb0-table
  '((alpha () 945)
    (beta () 946)))

(defvar x-symbol-myuc-table
  (append x-symbol-myuc-user-table x-symbol-myuc-xsymb0-table))


;;;===========================================================================
;;;  Internal
;;;===========================================================================

(defvar x-symbol-myuc-menu-alist nil
  "Internal.  Alist used for MyUc specific menu.")
(defvar x-symbol-myuc-grid-alist nil
  "Internal.  Alist used for MyUc specific grid.")

(defvar x-symbol-myuc-decode-atree nil
  "Internal.  Atree used by `x-symbol-token-input'.")
(defvar x-symbol-myuc-decode-alist nil
  "Internal.  Alist used for decoding of MyUc macros.")
(defvar x-symbol-myuc-encode-alist nil
  "Internal.  Alist used for encoding to MyUc macros.")

(defvar x-symbol-myuc-nomule-decode-exec nil
  "Internal.  File name of MyUc decode executable.")
(defvar x-symbol-myuc-nomule-encode-exec nil
  "Internal.  File name of MyUc encode executable.")

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-myuc.el ends here
