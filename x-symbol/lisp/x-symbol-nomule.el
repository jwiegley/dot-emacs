;;; x-symbol-nomule.el --- XEmacs/no-Mule support for package x-symbol

;; Copyright (C) 1996-1998, 2002 Free Software Foundation, Inc.
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

(when (featurep 'mule)
  (error "This file is meant to be used with XEmacs/no-Mule"))
(provide 'x-symbol-nomule)
(require 'x-symbol-hooks)
(eval-when-compile (require 'x-symbol))	; x-symbol also requires this file
;;(eval-when-compile
;;  (defvar x-symbol-encode-rchars)
;;  (defvar x-symbol-face-docstrings))


;;;===========================================================================
;;;  Function aliases and internal variables
;;;===========================================================================

(defalias 'x-symbol-make-cset 'x-symbol-nomule-make-cset)
(defalias 'x-symbol-make-char 'x-symbol-nomule-make-char)
(defalias 'x-symbol-init-charsym-syntax 'ignore)
(defalias 'x-symbol-charsym-after 'x-symbol-nomule-charsym-after)
(defalias 'x-symbol-string-to-charsyms 'x-symbol-nomule-string-to-charsyms)
(defalias 'x-symbol-match-before 'x-symbol-nomule-match-before)
(defalias 'x-symbol-encode-lisp 'x-symbol-nomule-encode-lisp)
(defalias 'x-symbol-pre-command-hook 'x-symbol-nomule-pre-command-hook)
(defalias 'x-symbol-post-command-hook 'x-symbol-nomule-post-command-hook)
(defalias 'x-symbol-encode-charsym-after 'x-symbol-nomule-encode-charsym-after)
(defalias 'x-symbol-init-quail-bindings 'ignore)

(defvar x-symbol-nomule-mouse-yank-function mouse-yank-function
  "Function that is called upon by `x-symbol-nomule-mouse-yank-function'.")

(defvar x-symbol-nomule-mouse-track-function
  (and (boundp 'default-mouse-track-normalize-point-function)
       default-mouse-track-normalize-point-function)
  "Function that is called upon by `x-symbol-nomule-mouse-track-function'.")

(defvar x-symbol-nomule-cstring-regexp "[\231-\237][\041-\176\240-\377]"
  "Internal configuration.  Regexp matching cstrings of length 2.
You should probably change the value when adding additional csets.")
;; should match `x-symbol-nomule-multibyte-char-p'.

(defvar x-symbol-nomule-char-table nil
  "Internal.  Map characters to charsyms.")
(defvar x-symbol-nomule-pre-command nil
  "Internal.  Used for pre- and post-command handling.")

(defvar x-symbol-nomule-leading-faces-alist nil
  "Internal.  Alist of leading character with their faces.
Each element looks like (LEADING NORMAL SUBSCRIPT SUPERSCRIPT).")
(defvar x-symbol-nomule-font-lock-face nil
  "Internal.  Face to fontify current font-lock match.")

(defvar x-symbol-nomule-display-table
  ;; display-table via characters table is not implemented in XEmacs yet...
  (let ((table (make-vector 256 nil))
	(i 128))
    (while (< i 160)
      (aset table i "")
      (incf i))
    table)
  "Display table in faces with non-standard charset registry.
It makes the leading characters, range \\200-\\237, invisible.")

(defvar x-symbol-nomule-character-quote-syntax "\\" ; bug in XEmacs
  "Syntax designator for leading characters in cstrings.")


;;;===========================================================================
;;;  Init code
;;;===========================================================================

(defun x-symbol-nomule-init-faces (fonts prefix &optional display-table)
  "Create and return faces for FONTS.
If a font can not be found, return nil for that font.  PREFIX is the
prefix in the name of the new face.  If non-nil, the new faces use
display table DISPLAY-TABLE."
  (let ((suffixes '("-face" "-sub-face" "-sup-face"))
	(docstrings x-symbol-face-docstrings)
	(raise 0)
	faces font face)
    (while suffixes
      (push (when (setq font (x-symbol-try-font-name (car fonts) raise))
	      (setq face (intern (concat prefix (car suffixes))))
	      (make-face face (car docstrings))
	      (set-face-font face font)
	      (if display-table (set-face-display-table face display-table))
	      face)
	    faces)
      (setq fonts (cdr fonts)
	    suffixes (cdr suffixes)
	    raise (1+ raise)
	    docstrings (cdr docstrings)))
    (nreverse faces)))

(defun x-symbol-nomule-make-cset (cset fonts)
  "Define new charsets according to CSET using FONTS.
See `x-symbol-init-cset'.  Return (NORMAL SUBSCRIPT SUPERSCIPT).  Each
element is a face or nil if the corresponding font in FONTS could not be
found.  Return nil, if no default font for that registry could be found."
  (cond ((noninteractive) (list nil))
	((eq (x-symbol-cset-coding cset) x-symbol-default-coding)
	 (or (x-symbol-nomule-init-faces fonts "x-symbol") ; no registry!
	     (list nil)))
	((x-symbol-try-font-name (car fonts))
	 (let* ((faces (x-symbol-nomule-init-faces
			fonts
			(concat "x-symbol-" (x-symbol-cset-registry cset))
			x-symbol-nomule-display-table))
		(leading (x-symbol-cset-leading cset))
		(ass (assq leading x-symbol-nomule-leading-faces-alist)))
	   (if x-symbol-nomule-character-quote-syntax
	       (modify-syntax-entry leading
				    x-symbol-nomule-character-quote-syntax
				    (standard-syntax-table)))
	   (if ass
	       (setcdr ass faces)
	     (push (cons leading faces)
		   x-symbol-nomule-leading-faces-alist))
	   faces))))

(defun x-symbol-nomule-make-char (cset encoding charsym face coding)
  "Define character in CSET with ENCODING, represented by CHARSYM.
The character is considered to be a 8bit character in CODING.  Use FACE
when character is presented in the grid or has a non-standard registry."
  (unless (char-table-p x-symbol-nomule-char-table)
    (setq x-symbol-nomule-char-table (make-char-table 'generic))
    (put-char-table t nil x-symbol-nomule-char-table))
  (let* ((leading (and (null (eq coding
				 (or x-symbol-default-coding 'iso-8859-1)))
		       (cadar cset)))
	 (table (if leading
		    (get-char-table leading x-symbol-nomule-char-table)
		  x-symbol-nomule-char-table))
	 (cstring (if leading
		      (concat (list leading encoding))
		    (char-to-string (int-to-char encoding)))))
    (unless (char-table-p table)
      (setq table (make-char-table 'generic))
      (put-char-table t nil table)
      (put-char-table leading table x-symbol-nomule-char-table))
    (put-char-table encoding charsym table)
    (x-symbol-set-cstrings charsym coding cstring
			   (and coding (>= encoding 160) (int-to-char encoding))
			   face)))


;;;===========================================================================
;;;  Character recognition
;;;===========================================================================

(defun x-symbol-nomule-multibyte-char-p (leading octet)
  "Non-nil if LEADING and OCTET are a multibyte character."
  (and leading (>= leading ?\200) (< leading ?\240)
       octet (or (< octet ?\177) (>= octet ?\240)) (>= octet ?\41)))

(defun x-symbol-nomule-encode-charsym-after ()
  (let ((charsym (get-char-table (char-after) x-symbol-nomule-char-table)))
    (if (char-table-p charsym)
	(let ((after (char-after (1+ (point)))))
	  (if after
	      (progn (setq x-symbol-encode-rchars 2)
		     (get-char-table after charsym))
	    (setq x-symbol-encode-rchars 1)
	    nil))
      (setq x-symbol-encode-rchars 1)
      charsym)))

(defun x-symbol-nomule-charsym-after (&optional pos)
  "Return x-symbol charsym for character at POS.
POS defaults to point.  If POS is out of range, return nil.  Otherwise,
return (POS1 . CHARSYM) where POS1 is POS-1 if the character before POS
is a leading character and POS1 is POS otherwise.  CHARSYM is the
x-symbol charsym for the character at POS1 or nil otherwise."
  (or pos (setq pos (point)))
  (let ((before (char-before pos))
	(after (char-after pos)))
    (and after
	 (if (or (x-symbol-nomule-multibyte-char-p before after)
		 (x-symbol-nomule-multibyte-char-p
		  (setq before after)
		  (setq after (char-after (incf pos)))))
	     (let ((table (get-char-table before x-symbol-nomule-char-table)))
	       (cons (1- pos)
		     (and (char-table-p table) (get-char-table after table))))
	   (cons (1- pos)
		 (and (symbolp (setq after (get-char-table
					    before
					    x-symbol-nomule-char-table)))
		      after))))))

(defun x-symbol-nomule-string-to-charsyms (string)
  "Return list of charsyms for the characters in STRING.
If a character is not represented as a charsym, use the character itself
if is an ascii in the range \\040-\\176, otherwise nil."
  (let ((chars (nreverse (append string nil)))
	result after table)
    (while chars
      (setq after (pop chars))
      (push (if (x-symbol-nomule-multibyte-char-p (car chars) after)
		(and (setq table (get-char-table (pop chars)
						 x-symbol-nomule-char-table))
		     (get-char-table after table))
	      (or (get-char-table after x-symbol-nomule-char-table) after))
	    result))
    result))

(defun x-symbol-nomule-match-before (atree pos &optional case-fn)
  "Return association in ATREE for longest match before POS.
Return (START . VALUE) where the buffer substring between START and
point is the key to the association VALUE in ATREE.  Do not use matches
where the character before START is a leading character.  If optional
CASE-FN is non-nil, convert characters before the current position with
CASE-FN.  See `x-symbol-atree-push'."
  (or pos (setq pos (point)))
  (let ((result nil)
	char)
    (while (setq char (if case-fn
			  (funcall case-fn (char-after (decf pos)))
			(char-after (decf pos)))
		 atree (cdr (assoc char (cdr atree))))
      (and (car atree)
	   (not (x-symbol-nomule-multibyte-char-p (char-before pos) char))
	   (setq result (cons pos (car atree)))))
    result))


;;;===========================================================================
;;;  Point correction
;;;===========================================================================

;; `mouse-track', `mouse-yank': If you set `mouse-yank-function' and/or
;; `default-mouse-track-normalize-point-function', set them before initializing
;; package X-Symbol.
(and x-symbol-nomule-mouse-yank-function
     (setq mouse-yank-function 'x-symbol-nomule-mouse-yank-function))
(and x-symbol-nomule-mouse-track-function
     (setq default-mouse-track-normalize-point-function
	   'x-symbol-nomule-mouse-track-function))

(defun x-symbol-nomule-goto-leading-char ()
  "If character before point is a leading character, move point left."
  (if (x-symbol-nomule-multibyte-char-p (char-before (point))
					(char-after (point)))
      (backward-char)))

(defun x-symbol-nomule-mouse-yank-function ()
  "Function used as value for `mouse-yank'.
If character under point is a x-symbol character, move point to its
leading character before calling `x-symbol-nomule-mouse-yank-function'."
  (x-symbol-nomule-goto-leading-char)
  (funcall x-symbol-nomule-mouse-yank-function))

(defun x-symbol-nomule-mouse-track-function (type forwardp)
  ;; checkdoc-params: (type forwardp)
  "Function used as value for `default-mouse-track-normalize-point-function'.
After calling `x-symbol-nomule-mouse-track-function', if character under
point is a x-symbol character, move point to its leading character."
  (funcall x-symbol-nomule-mouse-track-function type forwardp)
  (x-symbol-nomule-goto-leading-char))


;;;===========================================================================
;;;  Command hooks
;;;===========================================================================

;; Functions in these hooks are run twice (and more) when pressing a key which
;; runs a keyboard macro, e.g., if [backspace] runs [delete] and [delete] runs
;; `delete-backward-char'.

(defun x-symbol-nomule-pre-command-hook ()
  "Function used in `pre-command-hook' when `x-symbol-mode' is turned on.
Hide revealed characters, see `x-symbol-hide-revealed-at-point'.
Provide input method TOKEN, see `x-symbol-token-input'.  If character
under point is a x-symbol character, move point to its leading character."
  (x-symbol-hide-revealed-at-point)
  (when (and x-symbol-mode (null x-symbol-nomule-pre-command))
    (setq x-symbol-nomule-pre-command
	  (if (x-symbol-nomule-multibyte-char-p (char-before (point))
						(char-after (point)))
	      (prog1 (point) (backward-char))
	    t))
    (x-symbol-token-input)))

(defun x-symbol-nomule-post-command-hook ()
  "Function used in `post-command-hook' when `x-symbol-mode' is turned on.
Provide input method ELECTRIC, see `x-symbol-electric-input'.  Start
idle timer for info in echo area and revealing invisible characters, see
`x-symbol-start-itimer-once'.  Make sure that not only a part of a
length-two cstring has been deleted by the previous command."
  (when (and x-symbol-nomule-pre-command x-symbol-mode)
    (if (stringp (car-safe (car-safe buffer-undo-list)))
	;; i.e., after deleting text (`delete-char',...)
	(let* ((pos (abs (cdar buffer-undo-list)))
	       (str (caar buffer-undo-list))
	       (len (length str))
	       (pre (and (> len 0)
			 (x-symbol-nomule-multibyte-char-p
			  (char-before (point)) (aref str 0))))
	       (post (and (> len 0)
			  (x-symbol-nomule-multibyte-char-p
			   (aref str (1- len)) (char-after pos)))))
	  (if (or pre post)
	      (delete-region (if pre (1- pos) pos) (if post (1+ pos) pos))))
      (and (null (car-safe buffer-undo-list))
	   (integerp x-symbol-nomule-pre-command)
	   (= (point) x-symbol-nomule-pre-command)
	   ;; i.e., after pressing Right
	   (< x-symbol-nomule-pre-command (point-max))
	   (goto-char (1+ x-symbol-nomule-pre-command))))
    (x-symbol-electric-input)
    (if (x-symbol-nomule-multibyte-char-p (char-after (point))
					  (char-after (1+ (point))))
	(forward-char))
    (x-symbol-start-itimer-once))
  (setq x-symbol-nomule-pre-command nil))


;;;===========================================================================
;;;  Font-lock support
;;;===========================================================================

(defun x-symbol-nomule-match-cstring (limit)
  "Match next cstring of length 2 before LIMIT if `x-symbol-mode' is on.
Sets `x-symbol-nomule-font-lock-face' to the face used for this cstring
considering super- and subscripts."
  (when x-symbol-mode
    (let (faces old)
      (block nil
	(while (re-search-forward x-symbol-nomule-cstring-regexp limit t)
	  (setq faces (cdr (assq (char-after (match-beginning 0))
				 x-symbol-nomule-leading-faces-alist))
		old (get-text-property (match-beginning 0) 'face))
	  (or (listp old) (setq old (list old)))
	  (if (setq x-symbol-nomule-font-lock-face
		    (or (and (memq 'x-symbol-sup-face old) (caddr faces))
			(and (memq 'x-symbol-sub-face old) (cadr faces))
			(car faces)))
	      (return t)))))))

(defun x-symbol-nomule-fontify-cstrings ()
  "Fontify all cstrings in buffer even when `x-symbol-mode' is off.
Faces according to the cstrings are prepended to existing face settings.
See also `x-symbol-nomule-match-cstring'."
  (let ((x-symbol-mode t)
	(limit (point-max)))
    (goto-char (point-min))
    (while (x-symbol-nomule-match-cstring limit)
      (font-lock-prepend-text-property (match-beginning 0) (match-end 0)
				       'face
				       x-symbol-nomule-font-lock-face))))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-nomule.el ends here
