;;; x-symbol-macs.el --- macros used when compiling or interpreting x-symbol.el

;; Copyright (C) 1998-2002 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.4
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

;; Macro expansion must not dependent on Mule vs no-Mule!  Depending on Emacs
;; vs XEmacs is OK, since the elc files aren't compatible anyway.

;;; Code:

(provide 'x-symbol-macs)
(require 'cl)


;;;===========================================================================
;;;  
;;;===========================================================================

(defmacro x-symbol-ignore-property-changes (&rest body)
  (if (featurep 'xemacs)
      (cons 'progn body)
    (let ((modified (gensym "--x-symbol-modified--")))
      `(let ((,modified (buffer-modified-p))
	     (buffer-undo-list t)
	     (inhibit-read-only t)
	     (inhibit-modification-hooks t)
	     (inhibit-point-motion-hooks t))
	 (unwind-protect
	     (progn ,@body)
	   (and (not ,modified) (buffer-modified-p)
		(set-buffer-modified-p nil)))))))


;;;===========================================================================
;;;  Function used by macros and the macros
;;;===========================================================================

(defun x-symbol-set/push-assq/assoc (x key alist pushp test)
  (let* ((temp (gensym "--x-symbol-set/push-assq/assoc-temp--"))
	 (evalp (and (consp key) (null (eq (car key) 'quote))))
	 (keysymb (if evalp
		      (gensym "--x-symbol-set/push-assq/assoc-temp--")
		    key))
	 (keydef (and evalp (list (list keysymb key)))))
    `(let* (,@keydef
	    (,temp (,test ,keysymb ,alist)))
       (if ,temp
	   (setcdr ,temp ,(if pushp `(cons ,x (cdr ,temp)) x))
	 (setq ,alist (cons (,(if pushp 'list 'cons) ,keysymb ,x) ,alist)))
       ,temp)))

(defmacro x-symbol-set-assq (x key alist)
  "Set X to be the association for KEY in ALIST.
If no car of an element in ALIST is `eq' to KEY, inserts (KEY . X) at
the head of ALIST."
  (x-symbol-set/push-assq/assoc x key alist nil 'assq))

(defmacro x-symbol-set-assoc (x key alist)
  "Set X to be the association for KEY in ALIST.
If no car of an element in ALIST is `equal' to KEY, inserts (KEY . X) at
the head of ALIST."
  (x-symbol-set/push-assq/assoc x key alist nil 'assoc))

(defmacro x-symbol-push-assq (x key alist)
  "Insert X at the head of the association for KEY in ALIST.
If no car of an element in ALIST is `eq' to KEY, inserts (KEY X) at the
head of ALIST.  An element (KEY A B) would look like (KEY X A B) after
the operation."
  (x-symbol-set/push-assq/assoc x key alist t 'assq))

(defmacro x-symbol-push-assoc (x key alist)
  "Insert X at the head of the association for KEY in ALIST.
If no car of an element in ALIST is `equal' to KEY, inserts (KEY X) at
the head of ALIST.  An element (KEY A B) would look like (KEY X A B)
after the operation."
  (x-symbol-set/push-assq/assoc x key alist t 'assoc))


;;;===========================================================================
;;;  Macros
;;;===========================================================================

(defmacro x-symbol-dolist-delaying (spec cond &rest body)
  ;; checkdoc-params: (spec)
  "Loop over a list delaying elements if condition yields non-nil.
The macro looks like
  (x-symbol-dolist-delaying (VAR LIST [WORKING [DELAYED]]) COND BODY...)
Bind VAR to each `car' from LIST, in turn.  If COND yields nil, evaluate
BODY.  Otherwise, BODY with VAR bound to the list value is evaluated
after all other list values have been processed.  Return all list
values which could not been processed.

The looping is done in cycles.  In each cycle, the value of WORKING,
which defaults to some internal symbol, is the list of elements still to
be processed during the current cycle.  VAR is always the head of
WORKING.  If COND yields non-nil, VAR is inserted at the head of the
list stored in DELAYED which defaults to some internal symbol.  At the
end of each CYCLE, WORKING is set to the reversed value of DELAYED.  The
macro ends if all elements has been processed or all elements in a cycle
has been inserted into the delayed list."
  (let ((working (or (nth 2 spec)
		     (gensym "--x-symbol-dolist-delaying-temp--")))
	(delayed (or (nth 3 spec)
		     (gensym "--x-symbol-dolist-delaying-temp--")))
	(non-circ (gensym "--x-symbol-dolist-delaying-temp--")))
    `(block nil
       (let ((,working ,(nth 1 spec))
	     (,non-circ t)
	     ,delayed
	     ,(car spec))
	 (while (and ,working ,non-circ)
	   (setq ,delayed nil
		 ,non-circ nil)
	   (while ,working
	     (setq ,(car spec) (car ,working))
	     (if ,cond
		 (setq ,delayed (cons ,(car spec) ,delayed))
	       ,@body
	       (setq ,non-circ t))
	     (setq ,working (cdr ,working)))
	   (setq ,working (nreverse ,delayed)))
	 ,working))))

(defmacro x-symbol-do-plist (spec &rest body)
  ;; checkdoc-params: (spec)
  "Loop over a property list.
The macro looks like
  (x-symbol-do-plist (PROP VAR PLIST) BODY...)
Evaluate BODY with each PROP bound to each property of PLIST and VAR
bound to the corresponding value, in turn.  PROP and VAR can also be nil
if their value is not important.  Return nil."
  (let ((plist (gensym "--x-symbol-do-plist-temp--")))
    `(block nil
       (let ((,plist ,(nth 2 spec))
	     ,@(and (car spec) (list (car spec)))
	     ,@(and (nth 1 spec) (list (nth 1 spec))))
	 (while ,plist
	   (setq ,@(and (car spec) `(,(car spec) (car ,plist)))
		 ,@(and (nth 1 spec) `(,(nth 1 spec) (cadr ,plist))))
	   ,@body
	   (setq ,plist (cddr ,plist)))
	 nil))))

(defmacro x-symbol-while-charsym (spec &rest body)
  "(x-symbol-while-charsym (CHARSYM CHAR) BODY...)"
  (unless (and (consp spec)
	       (symbolp (car spec))
	       (symbolp (cadr spec))
	       (null (cddr spec)))
    (error "Wrong call of `x-symbol-while-charsym'."))
  (let ((charsym (car spec))
	(char (cadr spec)))
    `(let (,charsym ,char)
       (block nil
	 (skip-chars-forward "\000-\177")
	 (while (setq ,char (char-after))
	   (if (setq ,charsym
		     ,(if (featurep 'xemacs)
			  '(x-symbol-encode-charsym-after)
			;; no need for nomule byte-comp in Emacs => inline
			`(get-char-table ,char x-symbol-mule-char-table)))
	       (progn ,@body)
	     (forward-char x-symbol-encode-rchars))
	   (skip-chars-forward "\000-\177"))))))

(defmacro x-symbol-encode-for-charsym (spec &rest body)
  "(x-symbol-while-charsym ((TOKEN-TABLE FCHAR-TABLE FCHAR-FALLBACK-TABLE) TOKEN CHARSYM)) BODY...)"
  (let* ((tables (car spec))
	 (vars (cdr spec))
	 (fchar-table (cadr tables))
	 (fchar-fb-table (caddr tables))
	 (token (car vars))
	 (charsym (or (cadr vars)
		      (gensym "--x-symbol-encode-for-charsym-temp--")))
	 (char (gensym "--x-symbol-encode-for-charsym-temp--"))
	 (fchar (gensym "--x-symbol-encode-for-charsym-temp--")))
    `(let (,fchar ,token)
       (x-symbol-while-charsym ,(list charsym char)
	 (cond ((and ,fchar-table
		     (setq ,fchar (gethash ,charsym ,fchar-table)))
		;; fchar-fb-table = nil => no recoding
		(if (or (null ,fchar-fb-table) (eq ,fchar ,char))
		    (forward-char x-symbol-encode-rchars)
		  (insert ,fchar)
		  (delete-char x-symbol-encode-rchars)))
	       ((setq ,token (gethash ,charsym ,(car tables)))
		,@body)
	       ((setq ,fchar (gethash ,charsym ,fchar-fb-table))
		(if (eq ,fchar ,char)
		    (forward-char x-symbol-encode-rchars)
		  (insert ,fchar)
		  (delete-char x-symbol-encode-rchars)))
	       (t
		(forward-char x-symbol-encode-rchars)))))))

(defmacro x-symbol-decode-for-charsym (spec undefined &rest body)
  "(x-symbol-decode-for-charsym ((REGEXP DECODE-OBARRAY CASE-FN) DEFN BEG END) UNDEFINED BODY...)"
  (let* ((grammar (car spec))
	 (case-fn (caddar spec))
	 (defn (cadr spec))
	 (beg (caddr spec))
	 (end (cadddr spec)))
    `(let (,beg ,end ,defn)
       (block nil
	 (while (re-search-forward ,(car grammar) nil t)
	   (setq ,beg (match-beginning 0)
		 ,end (match-end 0))
	   (if (setq ,defn (intern-soft
			    ,(if case-fn
				 `(if ,case-fn
				      (funcall ,case-fn
					       (buffer-substring ,beg ,end))
				    (buffer-substring ,beg ,end))
			       `(buffer-substring ,beg ,end))
			    ,(cadr grammar)))
	       (progn
		 (setq ,defn (symbol-value ,defn)) ; nil shouldn't happen
		 ,@body)
	     ,@(if undefined (list undefined))))))))

(defmacro x-symbol-decode-unique-test (token-spec unique)
  `(and ,unique
	(or (cddr ,token-spec)
	    (and (hash-table-p ,unique)
		 (gethash (car ,token-spec) ,unique)))))

(defmacro x-symbol-set-buffer-multibyte ()
  ;; Make sure the buffer is not in unibyte mode (for Emacs).
  (unless (featurep 'xemacs)
    '(set-buffer-multibyte t)))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-macs.el ends here
