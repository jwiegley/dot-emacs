;;; x-symbol-xmacs.el --- make package x-symbol work with XEmacs

;; Copyright (C) 1998-1999, 2001-2003 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.5
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

;;; Code:

;;; Release dates: XEmacs-21.1.2 = 14 May 1999, XEmacs-21.1.9 = 13 Feb 2000.

(provide 'x-symbol-xmacs)
;; the following line can be included AFTER (require 'x-symbol-{mule/nomule}) has been deleted from x-symbol-hooks
;;(eval-when-compile (require 'x-symbol))	; x-symbol also requires this file

(cond ((not (and (fboundp 'emacs-version>=) (emacs-version>= 20 4)))
       ;; Yes, it probably works with XEmacs-20.2, too, but I do not want to
       ;; care about its bug in `string-match':
       (error "Package X-Symbol requires XEmacs-21.1.9+"))
      ((or (emacs-version>= 21 2) (not x-symbol-warn-of-old-emacs)))
      ((< emacs-major-version 21)
       (warn "X-Symbol: minor problem in GRID, upgrade to XEmacs-21.1.9+"))
      ((or (zerop emacs-minor-version)
	   ;; 3rd arg for `emacs-version>=' introduced in XEmacs-21.2.15
	   (not (and (boundp 'emacs-patch-level)
		     (>= emacs-patch-level 9))))
       ;; XEmacs-21.1.8 + X-Symbol + abbrev-mode + input method TOKEN => core
       (setq-default x-symbol-token-input nil)
       (warn "X-Symbol: XEmacs might core, upgrade to XEmacs-21.1.9+")))

(when (eq (console-type) 'mswindows)
  (unless (emacs-version>= 21 4)
    (warn "X-Symbol: might not work correctly, upgrade to XEmacs-21.4+"))
  (unless (and (boundp 'x-symbol-default-coding)
	       (or (null x-symbol-default-coding)
		   (eq x-symbol-default-coding 'iso-8859-1)))
    ;; no idea about XEmacs/NT in a Japanese environment...
    (warn "X-Symbol: only limited support with XEmacs-21.4+ on Windows")
    (setq x-symbol-default-coding 'iso-8859-1))
  (unless (and (boundp 'x-symbol-latin-force-use)
	       (eq x-symbol-latin-force-use 'mswindows-user))
    ;; Hm, this isn't a really great situation that all font settings are
    ;; useless for MS-Windows...
    (setq x-symbol-latin1-fonts
	  '(("Microsoft Sans Serif:Regular:11::Western"
	     "Courier New:Regular:11::Western")))
    ;; Latin2 != CP1250, see EMACS/lisp/international/codepage.el
    (setq x-symbol-latin2-fonts nil)
    ;;	  '(("Microsoft Sans Serif:Regular:11::Central European"
    ;;	     "Courier New:Regular:11::Central European")))
    ;; Latina-3 from <http://www.esperanto.se/html/latina.html> does not work,
    ;; I have no time to download and test various others...
    (setq x-symbol-latin3-fonts nil)
    (setq x-symbol-latin5-fonts
	  '(("Microsoft Sans Serif:Regular:11::Turkish"
	     "Courier New:Regular:11::Turkish")))
    (setq x-symbol-latin9-fonts nil)
    (setq x-symbol-xsymb0-fonts
	  '(("Symbol:Regular:11::Symbol")))
    (setq x-symbol-xsymb1-fonts nil)
    (make-face 'x-symbol-heading-face)
    (set-face-font 'x-symbol-heading-face
		   "Microsoft Sans Serif:Bold:10::Western")
    (set-face-foreground 'x-symbol-heading-face "green4")
    (set-face-underline-p 'x-symbol-heading-face t)
    (make-face 'x-symbol-info-face)
    (set-face-font 'x-symbol-info-face
		   "Microsoft Sans Serif:Regular:10::Western")
    (set-face-foreground 'x-symbol-info-face "green4")
    (make-face 'x-symbol-emph-info-face)
    (set-face-font 'x-symbol-emph-info-face
		   "Microsoft Sans Serif:Regular:10::Western")
    (set-face-foreground 'x-symbol-emph-info-face "red4")))


;;;===========================================================================
;;;  Fixing non X-Symbol induced annoyances
;;;===========================================================================

(defun x-symbol-paren-reset-mode ()
  (make-local-variable 'paren-mode)
  (setq paren-mode nil))
(add-hook 'list-mode-hook 'x-symbol-paren-reset-mode)


;;;===========================================================================
;;;  Autoloads
;;;===========================================================================

(autoload 'browse-url "browse-url" nil t)


;;;===========================================================================
;;;  Bug workarounds
;;;===========================================================================

;; Workaround for XEmacs bug (since XEmacs-20) with char syntax `inherit': the
;; following should be executed before(!) the AucTeX's syntax table is created.
(unless (or (featurep 'mule) (emacs-version>= 21 4)) ; OK in XEmacs-21.4.5
  (modify-syntax-entry ?\237 "\\" (standard-syntax-table))
  (modify-syntax-entry ?\236 "\\" (standard-syntax-table))
  (modify-syntax-entry ?\235 "\\" (standard-syntax-table))
  (modify-syntax-entry ?\234 "\\" (standard-syntax-table))
  (modify-syntax-entry ?\233 "\\" (standard-syntax-table))
  (modify-syntax-entry ?\232 "\\" (standard-syntax-table))
  ;; Add appropriately if more csets (fonts) are added.
  )


;;;===========================================================================
;;;  X-Symbol functions that depend on the Emacs flavor
;;;===========================================================================

(defvar x-symbol-xmacs-default-face-fonts nil)

(defalias 'x-symbol-directory-files 'directory-files)

(defun x-symbol-event-in-current-buffer ()
  (or (null current-mouse-event)
      (eq (event-buffer current-mouse-event) (current-buffer))))

(defun x-symbol-create-image (file type)
  (make-image-instance (vector (or type 'autodetect) ; autodetect is not clever
			       :file file)
		       nil nil t))

(defalias 'x-symbol-make-glyph 'make-glyph)

(defalias 'x-symbol-set-glyph-image 'set-glyph-image)

(defun x-symbol-set-face-font (face font charsets default)
  "Set font to use for text using FACE and CHARSETS."
  (if default
      (progn
	(push (cons face font) x-symbol-xmacs-default-face-fonts)
	(set-face-property face 'font font))
    (set-face-property face 'font font nil '(mule-fonts) 'prepend)
    (let ((dfont (assq face x-symbol-xmacs-default-face-fonts)))
      (if dfont (set-face-property face 'font (cdr dfont))))))

(defun x-symbol-event-matches-key-specifier-p (event specifier)
  "Return non-nil if EVENT matches key or mouse SPECIFIER.
This is like `event-matches-key-specifier-p', except that it also works
for mouse events."
  (if (mouse-event-p event)
      (equal (aref (events-to-keys (vector event)) 0) specifier)
    (condition-case nil
	(event-matches-key-specifier-p event specifier)
      (error nil))))

(defun x-symbol-window-width (&optional window)
  "Return the number of display columns in WINDOW (corrected version)."
  (or window (setq window (selected-window)))
  (/ (- (window-pixel-width window)
	(window-left-margin-pixel-width window) ; ??
	(window-right-margin-pixel-width window) ; ??
	(specifier-instance scrollbar-width window))
     (font-instance-width (face-font-instance 'default window))))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-xmacs.el ends here
