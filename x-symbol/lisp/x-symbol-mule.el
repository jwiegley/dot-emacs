;;; x-symbol-mule.el --- XEmacs/Mule support for package x-symbol

;; Copyright (C) 1997-1999, 2001-2002 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.4.X
;; Keywords: WYSIWYG, LaTeX, HTML, wp, math, internationalization, Mule
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

;; No `eval-and-compile' around this test, would just complicate distribution
(unless (featurep 'mule)
  (error "This file is meant to be used with XEmacs/Mule"))
(provide 'x-symbol-mule)
(eval-when-compile (require 'cl))
(require 'x-symbol-hooks)
(eval-when-compile (require 'x-symbol-vars)) ; TODO: or always?  or next line?
(eval-when-compile (require 'x-symbol))	; x-symbol also requires this file
;;  (defvar x-symbol-cstring-table)	; in x-symbol.el
;;  (defvar x-symbol-face-docstrings))
;;(require 'quail) has autoload

;;(unless (eq x-symbol-default-coding 'iso-8859-1)
;;  (warn "Package x-symbol under XEmacs/Mule has only been tested with default coding `iso-8859-1'"))

;; Provide easier XEmacs-21/Mule bug workaround:
(defvar x-symbol-mule-default-charset
  (cond
   ((or (null x-symbol-default-coding)
	(eq x-symbol-default-coding 'iso-8859-1))
    'latin-iso8859-1)
   ;; XEmacs iso-2022 coding-system-type
   ((eq (coding-system-type x-symbol-default-coding) 'iso2022)
    (coding-system-property x-symbol-default-coding 'charset-g1))
   ;; Emacs iso-2022 coding-system-type
   ((eq (coding-system-type x-symbol-default-coding) 2)
    (aref (coding-system-flags x-symbol-default-coding) 1))
   (t
    (lwarn 'x-symbol 'warning
      "Can't determine charset from coding system %s, using latin-iso8859-1" 
      x-symbol-default-coding)
    'latin-iso8859-1))
  "Mule charset corresponding to `x-symbol-default-coding'.")


;;;===========================================================================
;;;  Function aliases and internal variables
;;;===========================================================================

(defalias 'x-symbol-make-cset 'x-symbol-mule-make-cset)
(defalias 'x-symbol-make-char 'x-symbol-mule-make-char)
(defalias 'x-symbol-init-charsym-syntax 'x-symbol-mule-init-charsym-syntax)
(defalias 'x-symbol-charsym-after 'x-symbol-mule-charsym-after)
(defalias 'x-symbol-string-to-charsyms 'x-symbol-mule-string-to-charsyms)
(defalias 'x-symbol-match-before 'x-symbol-mule-match-before)
(defalias 'x-symbol-encode-lisp 'x-symbol-mule-encode-lisp)
(defalias 'x-symbol-pre-command-hook 'x-symbol-mule-pre-command-hook)
(defalias 'x-symbol-post-command-hook 'x-symbol-mule-post-command-hook)
(defalias 'x-symbol-encode-charsym-after 'x-symbol-mule-encode-charsym-after)
(defalias 'x-symbol-init-quail-bindings 'x-symbol-mule-init-quail-bindings)

(defvar x-symbol-mule-char-table nil
  "Internal.  Map characters to charsyms.")
(defvar x-symbol-mule-pre-command nil
  "Internal.  Used for pre- and post-command handling.")


;;;===========================================================================
;;;  Init code
;;;===========================================================================

(defun x-symbol-mule-make-charset (definition graphic registry)
  "Define new charset according to DEFINITION.
DEFINITION looks like nil or (NAME) or (NAME DOCSTRING CHARS FINAL), see
`x-symbol-init-cset'.  GRAPHIC and REGISTRY are charset properties, see
`make-charset' for details."
  (and definition
       (null (find-charset (car definition)))
       (make-charset (car definition) (cadr definition)
		     (list 'registry registry
			   'dimension 1
			   'chars (caddr definition)
			   'final (cadddr definition)
			   'graphic graphic))))

(defvar x-symbol-mule-default-font nil)

(defun x-symbol-mule-default-font ()
  ;; It would be probably better to set the font for all (device-list)s.  But
  ;; even better would be if XEmacs would allow an easy way to set fonts for
  ;; other charset-encodings without changing the font for the default
  ;; charset-encoding.  No using `append' instead `prepend' as HOW-TO-ADD is
  ;; loosing since then other settings might have preference.
  (or x-symbol-mule-default-font
      (setq x-symbol-mule-default-font
	    (font-instance-name
	     (face-property-instance 'default 'font (selected-device))))))
;;;      (let ((temp-buffer (get-buffer-create " x-symbol default font")))
;;;	(save-window-excursion
;;;	  (display-buffer temp-buffer)
;;;	  (sit-for 0.1)  ; necessary?
;;;	  (setq x-symbol-mule-default-font
;;;		(font-instance-name (face-property-instance 'default 'font))))
;;;	(kill-buffer temp-buffer)
;;;	x-symbol-mule-default-font)))

(defun x-symbol-mule-make-cset (cset fonts)
  "Define new charsets according to CSET using FONTS.
See `x-symbol-init-cset'.  Return (NORMAL SUBSCRIPT SUPERSCIPT).  Each
element is a face or nil if the corresponding font in FONTS could not be
found.  Return nil, if no default font for that registry could be found."
  (let ((first (if noninteractive
		   (caar fonts)
		 (x-symbol-try-font-name (car fonts)))))
    (when (or first
	      (and x-symbol-latin-force-use (x-symbol-cset-coding cset))
	      (and (find-charset (car (x-symbol-cset-left cset)))
		   (find-charset (car (x-symbol-cset-right cset)))))
      (let ((default (eq (x-symbol-cset-coding cset)
			 (or x-symbol-default-coding 'iso-8859-1)))
	    (registry (x-symbol-cset-registry cset))
	    (left (x-symbol-cset-left cset))
	    (right (x-symbol-cset-right cset)))
	(x-symbol-mule-make-charset left 0 registry)
	(x-symbol-mule-make-charset right 1 registry)
	(or default
	    (null first)
	    noninteractive
	    (not (fboundp 'face-property-matching-instance)) ;Only for XEmacs.
	    (and (null x-symbol-mule-change-default-face)
		 (face-property-matching-instance 'default 'font
						  (or (car left) (car right))
						  nil nil t))
	    (let ((origfont (x-symbol-mule-default-font)))
	      (set-face-property 'default 'font first nil
				 '(mule-fonts) 'prepend)
	      ;; If we do not reset the originally default font, we end up
	      ;; using a latin5 default font...
	      (set-face-property 'default 'font origfont)))
	(if noninteractive
	    (list nil)
	  (let ((faces '(x-symbol-face x-symbol-sub-face x-symbol-sup-face))
		(docstrings x-symbol-face-docstrings)
		(raise 0)
		font)
	    (while faces
	      (when (setq font (x-symbol-try-font-name (car fonts) raise))
		(make-face (car faces) (car docstrings))
		(x-symbol-set-face-font (car faces) font
					(list (car left) (car right))
					default))
	      (setq fonts (cdr fonts)
		    raise (1+ raise)
		    faces (cdr faces)
		    docstrings (cdr docstrings))))
	  (if first '(x-symbol-face) '(default)))))))

(defun x-symbol-mule-make-char (cset encoding charsym face coding)
  "Define character in CSET with ENCODING, represented by CHARSYM.
The character is considered to be a 8bit character in CODING.  Use FACE
when character is presented in the grid."
  (unless (char-table-p x-symbol-mule-char-table)
    (setq x-symbol-mule-char-table (make-char-table 'generic))
    (put-char-table t nil x-symbol-mule-char-table))
  (let* ((char (if (< encoding 128)
		   (make-char (caadr cset) encoding)
		 (make-char (caddr cset) (- encoding 128)))))
    (put-char-table char charsym x-symbol-mule-char-table)
    (x-symbol-set-cstrings charsym coding char
			   (and coding (>= encoding 160)
				(make-char x-symbol-mule-default-charset
					   (- encoding 128)))
			   face)))

(defun x-symbol-mule-init-charsym-syntax (charsyms)
  "Initialize the syntax for the characters represented by CHARSYMS.
See `x-symbol-init-cset' and `x-symbol-group-syntax-alist'."
  (dolist (charsym charsyms)
    (when (gethash charsym x-symbol-cstring-table)
      (let ((syntax (get charsym 'x-symbol-syntax)))
	(when syntax
	  (let ((opposite (and (cdr syntax)
			       (gethash (cddr syntax) x-symbol-cstring-table))))
	    (modify-syntax-entry (aref (gethash charsym x-symbol-cstring-table)
				       0)
				 (if opposite
				     (format (cadr syntax) opposite)
				   (car syntax))
				 (standard-syntax-table))))))))

(defun x-symbol-mule-init-quail-bindings (context chain)
  (if context
      (quail-defrule (if (< (length context) (max x-symbol-key-min-length 2))
			 (concat context x-symbol-quail-suffix-string)
		       context)
		     (mapconcat (lambda (charsym)
				  (gethash charsym x-symbol-cstring-table))
				chain ""))
    (quail-define-package
     "x-symbol" "X-Symbol" "XS" t
     "X-Symbol input method Quail, see <info:(x-symbol)Input Method Quail>"
     nil t				; FORGET-LAST-SELECTION
     nil nil nil nil t)))		; MAXIMUM-SHORTEST


;;;===========================================================================
;;;  Character recognition
;;;===========================================================================

(defun x-symbol-mule-encode-charsym-after ()
  (get-char-table (char-after) x-symbol-mule-char-table))


(defun x-symbol-mule-charsym-after (&optional pos)
  "Return x-symbol charsym for character at POS.
POS defaults to point.  If POS is out of range, return nil.  Otherwise,
return (POS . CHARSYM) where CHARSYM is the x-symbol charsym for the
character at POS or nil otherwise."
  (or pos (setq pos (point)))
  (and (char-after pos)
       (cons pos (get-char-table (char-after pos) x-symbol-mule-char-table))))

(defun x-symbol-mule-string-to-charsyms (string)
  "Return list of charsyms for the characters in STRING.
If a character is not represented as a charsym, use the character itself
if is an ascii in the range \\040-\\176, otherwise nil."
  (let ((chars (nreverse (append string nil)))
	result after)
    (while chars
      (setq after (pop chars))
      (push (or (get-char-table after x-symbol-mule-char-table)
		(and (<= ?\040 after) (< after ?\177) after))
	    result))
    result))

(defun x-symbol-mule-match-before (atree pos &optional case-fn)
  "Return association in ATREE for longest match before POS.
Return (START . VALUE) where the buffer substring between START and
point is the key to the association VALUE in ATREE.  If optional CASE-FN
is non-nil, convert characters before the current position with CASE-FN.
See `x-symbol-atree-push'."
  (let ((result nil))
    (while (setq atree (cdr (assoc (if case-fn
				       (funcall case-fn (char-after (decf pos)))
				     (char-after (decf pos)))
				   (cdr atree))))
      (and (car atree)
	   (setq result (cons pos (car atree)))))
    result))


;;;===========================================================================
;;;  Command hooks
;;;===========================================================================

;; Functions in these hooks are run twice (and more) when pressing a key which
;; runs a keyboard macro, e.g., if [backspace] runs [delete] and [delete] runs
;; `delete-backward-char'.

(defun x-symbol-mule-pre-command-hook ()
  "Function used in `pre-command-hook' when `x-symbol-mode' is turned on.
Hide revealed characters, see `x-symbol-hide-revealed-at-point'.
Provide input method TOKEN, see `x-symbol-token-input'."
  (x-symbol-hide-revealed-at-point)
  (when (and x-symbol-mode (null x-symbol-mule-pre-command))
    (setq x-symbol-mule-pre-command t)
    (x-symbol-token-input)))

(defun x-symbol-mule-post-command-hook ()
  "Function used in `post-command-hook' when `x-symbol-mode' is turned on.
Provide input method ELECTRIC, see `x-symbol-electric-input'.  Start
idle timer for info in echo area and revealing invisible characters, see
`x-symbol-start-itimer-once'."
  (when (and x-symbol-mode x-symbol-mule-pre-command)
    (x-symbol-electric-input)
    (x-symbol-start-itimer-once))
  (setq x-symbol-mule-pre-command nil))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-mule.el ends here
