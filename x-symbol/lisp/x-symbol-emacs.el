;;; x-symbol-emacs.el --- make package x-symbol work with Emacs

;; Copyright (C) 2000-2002 Free Software Foundation, Inc.
;;
;; Authors: Stefan Monnier, Christoph Wedler
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

(provide 'x-symbol-emacs)

(unless (fboundp 'emacs-version>=)
  (defun emacs-version>= (major &optional minor)
  "Return true if the Emacs version is >= to the given MAJOR, and
MINOR numbers, MINOR is optional.  MINOR is only used in the test if it
is non-nil."
  (cond ((> emacs-major-version major))
	((< emacs-major-version major) nil)
	((null minor))
	((>= emacs-minor-version minor)))))


;;;===========================================================================
;;;  Emacs-21.4 features
;;;===========================================================================
;; To make use of newer Emacs features with the current stable version of
;; Emacs, you can download individual files from the CVS repository of
;; <http://savannah.gnu.org/projects/emacs/>.  E.g., I use Emacs-21.1.5
;; together with updates of the following files:

;; lisp/font-lock.el,v 1.200, lisp/font-core.el,v 1.8(new),
;; lisp/emacs-lisp/syntax.el,v 1.5(new):
;;   (defvar char-property-alias-alist nil)
;;   (unless (fboundp 'copy-tree) (defalias 'copy-tree 'copy-alist))
;;   (unless (fboundp 'remove-list-of-text-properties)
;;     (defun remove-list-of-text-properties (start end proplist)
;;       (let (props)
;;         (while proplist (push nil props) (push (pop proplist) props))
;;         (remove-text-properties start end props))))
;;   (or (featurep 'font-core) (load "font-core" t))
(defvar x-symbol-emacs-has-font-lock-with-props
  (and (boundp 'font-lock-extra-managed-props)
       (boundp 'char-property-alias-alist)
       (fboundp 'copy-tree)
       (locate-library "font-core")
       (locate-library "syntax")))
;; with the following line, "reveal invisible around point" won't work:
;;   (setq x-symbol-emacs-has-font-lock-with-props 'invisible)

;; lisp/warnings.el,v 1.6(new): recommended
(condition-case nil (require 'warnings) (error))

;; src/fileio.c,v 1.447:
(defvar x-symbol-emacs-has-correct-find-safe-coding
  (emacs-version>= 21 4))

;; lisp/format.el,v 1.39 (with src/fileio.c,v 1.447):
;;   (setq x-symbol-auto-conversion-method 'format)

;; lisp/isearch.el,v 1.213 (makes isearch+GRID work):
;;   (load "isearch")  ; only nec/ when updated after Emacs built

;; lisp/language/european.el,v 1.76 (makes X-Symbol+ispell work)
;;   (load "european")  ; only nec/ when updated after Emacs built

;;; Bugs:

(defvar x-symbol-emacs-after-create-image-function 'clear-image-cache)

;;; Todo:

;; - Invisible text support.
;; - Use Emacs-21's `display' text-property to make sub/super-scripts.
;; - many more, I'm sure.

;; Changes I (CW) would like to see in Emacs:
;;  * `directory-files': 5th arg FILES-ONLY like in XEmacs
;;  * `file-remote-p' like in XEmacs (defined below)
;;  * tooltip and menu cannot use text props, Emacs display strings with prop
;;    as "("STRING" 0 4 nil...) instead, which is not useful

;; Restrictions, Questions (or other changes I would like to see):
;;  * how to use temp image files for images?

;;; Code:

(require 'cl)
(require 'fontset)			;seems not to be loaded in batch mode

;; temp hack:
(if (memq 'png image-types) (provide 'png))
(if (memq 'gif image-types) (provide 'gif))

;; No way to test patch level?
(cond ((not (and (boundp 'emacs-major-version)
		 (>= emacs-major-version 21)
		 (or (> emacs-major-version 21) (>= emacs-minor-version 1))))
       (error "Package X-Symbol can only be used with Emacs-21.1+")))

;;(require 'x-symbol-hooks)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;   Emacs-20 specific       ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(unless (fboundp 'puthash) (defalias 'puthash 'cl-puthash))
;;(unless (fboundp 'plist-member) (defalias 'plist-member 'widget-plist-member))
;;(unless (fboundp 'point-at-bol) (defalias 'point-at-bol 'line-end-position))
;;(unless (fboundp 'point-at-eol) (defalias 'point-at-eol 'line-beginning-position))
;;(unless (fboundp 'add-minor-mode)
;;  (defun add-minor-mode (tog name map)
;;    (when name (add-to-list 'minor-mode-alist (list tog name)))
;;    (when map (add-to-list 'minor-mode-map-alist (cons tog map)))))

(unless (and (boundp 'emacs-major-version) (>= emacs-major-version 21))
  (error "X-Symbol requires Emacs-21 or higher"))


;;(define-key isearch-mode-map [?\C-=] nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;   Problematic XEmacs compatibility  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar init-file-loaded t)

;; Used in x-symbol-show-info-and-invisible
(defvar message-stack nil)		;message-stack ~= (current-message)
(unless (fboundp 'warn) (defalias 'warn 'message))
(unless (fboundp 'lwarn)
  (defun lwarn (class level msg &rest args)
    (warn (format "(%s/%s) %s" class level msg) args)))
(unless (fboundp 'display-message)
  (defun display-message (label msg)
    (if (memq label '(help-echo command progress prompt no-log
				garbage-collecting auto-saving))
	;; XEmacs `log-message-ignore-labels'
	(let ((message-log-max nil))	;#dynamic
	  (message "%s" msg))
      (message "%s" msg))))

(unless (fboundp 'face-font-instance)
  (defalias 'face-font-instance 'face-font))
(unless (fboundp 'try-font-name)
  (defun try-font-name (name)
    (and name
	 ;; TODO: shouldn't `x-list-fonts' work when not running on X?
	 (condition-case nil (x-list-fonts name) (error nil))
	 name)))
(unless (fboundp 'put-nonduplicable-text-property)
  (defun put-nonduplicable-text-property (start end prop val &optional obj)
    (let ((inhibit-modification-hooks t)
	  (modified (buffer-modified-p)))
      (unwind-protect
	  (put-text-property start end prop val obj)
	(set-buffer-modified-p modified)))))

;;; list-mode ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(unless (fboundp 'list-mode)
  (define-derived-mode list-mode completion-list-mode "List"
    "Major mode for buffer containing lists of items."
    (setq buffer-read-only t)))
(unless (fboundp 'add-list-mode-item)
  (defun add-list-mode-item (start end &optional buffer activate-callback
				   ;; activate-callback is ignored
				   user-data)
    ;; BEWARE!!! (list 'highlight) here is tricky.  It makes sure that each
    ;; item has a distinct mouse-face text-property value, so that they
    ;; won't be aggregated arbitrarily (aggregation uses `eq' rather
    ;; than `equal').
    (put-text-property start end 'mouse-face (list 'highlight) buffer)
    (let ((ol (make-overlay start end buffer)))
      (overlay-put ol 'list-mode-item t)
      (if user-data (overlay-put ol 'list-mode-item-user-data user-data))
      ol)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;   Plain XEmacs compatibility        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Extents ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'lucid)
(unless (fboundp 'extent-property) (defalias 'extent-property 'overlay-get))
(unless (fboundp 'map-extents) (defalias 'map-extents 'cl-map-overlays))
(unless (fboundp 'set-extent-end-glyph)
  (defun set-extent-end-glyph (extent glyph)
    (overlay-put extent 'after-string glyph)))
(unless (fboundp 'insert-face)
  (defun insert-face (string face)
    (let ((ol (make-overlay (point) (progn (insert string) (point)))))
      (overlay-put ol 'face face) ol)))

;;; Chars ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(unless (fboundp 'characterp) (defalias 'characterp 'integerp))
(unless (fboundp 'int-to-char) (defalias 'int-to-char 'identity))
(unless (fboundp 'char-to-int) (defalias 'char-to-int 'identity))

;;; Char tables ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(put 'generic 'char-table-extra-slots 0)
(unless (fboundp 'put-char-table)
  (defun put-char-table (range val tab) (set-char-table-range tab range val)))
(unless (fboundp 'get-char-table)
  (defun get-char-table (ch table) (char-table-range table ch)))

;;; Charsets ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun region-active-p () (and transient-mark-mode mark-active))
(unless (fboundp 'make-charset)
  (defun make-charset (name docstring info)
    (let ((registry (plist-get info 'registry))
	  (graphic (plist-get info 'graphic))
	  (dimension (plist-get info 'dimension))
	  (ccl-program (plist-get info 'ccl-program)))
      (define-charset nil name
	(vector dimension
		(plist-get info 'chars)
		(or (plist-get info 'columns) dimension)
		(if (eq (plist-get info 'direction) 'l2r) 0 1)
		(plist-get info 'final)
		graphic
		(symbol-name name)
		(symbol-name name)
		docstring))
      ;; Don't ask for X-Symbol's private charsets (with Emacs-21.0.104+).  But
      ;; you're still asked for latin-{2,3,5,9} chars even if they are encoded
      ;; by X-Symbol (changes in Emacs-21.4: first do annotate functions, then
      ;; determine safe coding).
      (or x-symbol-emacs-has-correct-find-safe-coding
	  (aset char-coding-system-table (make-char name) t))
      (when registry
	(set-fontset-font "fontset-default" name (cons "*" registry))
	(when (eq graphic 0) (set-font-encoding registry name 0))
	(when ccl-program
	  (add-to-list 'font-ccl-encoder-alist (cons registry ccl-program))))
      name)))

(unless (fboundp 'find-charset)
  (defun find-charset (c) (and (charsetp c) c)))

;;; Misc ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(autoload 'Info-goto-node "info")

(defvar x-symbol-data-directory (expand-file-name "x-symbol" data-directory))

(unless (fboundp 'signal-error) (defalias 'signal-error 'signal))

(unless (fboundp 'console-type)
  (defun console-type ()
    (case window-system
      (x 'x)
      (w32 'mswindows)
      (nil 'tty)
      (t window-system))))

(unless (fboundp 'symbol-value-in-buffer)
  (defun symbol-value-in-buffer (sym buf &optional def)
    (with-current-buffer buf (if (boundp sym) (symbol-value sym) def))))

(unless (fboundp 'make-key-weak-hashtable)
  (defun make-key-weak-hashtable (size &optional test)
    ;; The :weakness is (hopefully) ignored on Emacs-20
    (make-hash-table :size size :test test :weakness 'key)))

(unless (fboundp 'set-keymap-default-binding)
  (defun set-keymap-default-binding (map cmd)
    (define-key-after map [t] cmd t)))

(unless (fboundp 'destructive-alist-to-plist)
  (defun destructive-alist-to-plist (alist)
    (let ((next alist) tmp head)
      (while next
	(setq head (car next) tmp next)
	(if (not (consp head)) (pop next)
	  (setcar next (car head))
	  (setcar head (cdr head))
	  (setcdr head (setq next (cdr next)))
	  (setcdr tmp head))))
    alist))

(unless (fboundp 'plists-eq)
  ;; All kinds of potential problems here with "shadowed properties".
  (defun plists-eq (a b)
    (when (= (length a) (length b))
      (let (tmp)
	(while (and a
		    (setq tmp (plist-member b (pop a)))
		    (eq (car a) (cadr tmp)))
	  (setq a (cdr a)))
	(null a)))))

;; From XEmacs
(unless (fboundp 'sorted-key-descriptions)
  (defun sorted-key-descriptions (keys &optional separator)
    "Sort and separate the key descriptions for KEYS.
The sorting is done by length (shortest bindings first), and the bindings
are separated with SEPARATOR (\", \" by default)."
    (mapconcat 'key-description
	       (sort keys #'(lambda (x y)
			      (< (length x) (length y))))
	       (or separator ", "))))

(unless (fboundp 'file-remote-p)
  (defun file-remote-p (file-name)
    "Test whether FILE-NAME is looked for on a remote system."
    (cond ((featurep 'ange-ftp)
	   (if (fboundp 'ange-ftp-ftp-name)
	       (ange-ftp-ftp-name file-name)
	     (ange-ftp-ftp-path file-name)))
	  ((fboundp 'efs-ftp-path) (efs-ftp-path file-name))
	  (t nil))))

(defun x-symbol-directory-files (dirname &optional full match nosort
					 files-only)
  (let ((files (directory-files dirname full match nosort))
	result)
    (if (null files-only)
	files
      (while files
	(if (if (file-directory-p (car files))
		(null (eq files-only t))
	      (eq files-only t))
	    (push (car files) result))
	(setq files (cdr files)))
      (nreverse result))))

(defun x-symbol-event-in-current-buffer ()
  t)

(defun x-symbol-create-image (file type)
  (create-image file type nil :ascent 80))

(defun x-symbol-make-glyph (image)
  (propertize "x" 'display image))

(defun x-symbol-set-glyph-image (glyph image)
  (set-text-properties 0 (length glyph) (list 'display image) glyph))

(unless (fboundp 'event-closest-point)
  (defun event-closest-point (event) (posn-point (event-end event))))

(unless (fboundp 'event-buffer)
  (defun event-buffer (event) (window-buffer (posn-window (event-end event)))))

;;;
;;; X-Symbol functions
;;;

;; Defvarred to prevent their initialization code to run (since that
;; code uses XEmacs'isms that haven't been ported yet).
(defvar x-symbol-heading-strut-glyph " ")

;; Define face's vars for Emacs' font-lock.
(defvar x-symbol-invisible-face 'x-symbol-invisible-face)
(defvar x-symbol-face 'x-symbol-face)
(defvar x-symbol-sub-face 'x-symbol-sub-face)
(defvar x-symbol-sup-face 'x-symbol-sup-face)

(defvar x-symbol-emacs-w32-font-directories
  (mapcar (lambda (dir) (expand-file-name dir x-symbol-data-directory))
	  '("fonts/" "genfonts/")))

(if (and (eq window-system 'w32)
	 x-symbol-emacs-w32-font-directories
	 (fboundp 'w32-find-bdf-fonts)
	 (boundp 'w32-bdf-filename-alist))
    (setq w32-bdf-filename-alist
	  (nconc w32-bdf-filename-alist
		 (w32-find-bdf-fonts x-symbol-emacs-w32-font-directories))))

;; Invisibility cannot be done this way in Emacs.
(defvar x-symbol-invisible-display-table nil)

(defalias 'x-symbol-window-width 'window-width)

(defun x-symbol-set-face-font (face font charsets default)
  (let ((fontset (concat "fontset-" (symbol-name face))))
    (unless (query-fontset fontset)
      ;; We assume that the first time around we're using latin-8859-1
      (new-fontset fontset
		   (x-complement-fontset-spec (make-vector 14 "*")
					      (list (cons 'ascii font)))))
    (dolist (charset charsets)
      (when charset (set-fontset-font fontset charset font)))
    (set-face-font face fontset)))

(defun x-symbol-event-matches-key-specifier-p (event specifier)
  (if (consp specifier) (setq specifier (event-convert-list specifier)))
  (if (consp event) (setq event (car event)))
  (eq event specifier))

;;;
;;; Possibly useful compat functions
;;;

;;; from Sang-Min
(defun start-itimer (name func value restart isidle)
  (run-with-idle-timer value restart func))
(defun itimer-live-p (obj) (and obj (not (aref obj 0))))

;;; x-symbol-emacs.el ends here
