;;; NOTE: this is a temporary file, for testing a new variant
;;; of the unicode tokens, based on font-lock.  At present
;;; not used.

;;; unicode-tokens2.el --- Support for editing tokens for Unicode characters
;;
;; Copyright(C) 2008 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; A few functions are adapted from `xmlunicode.el' by Norman Walsh.
;; Created: 2004-07-21, Version: 1.6, Copyright (C) 2003 Norman Walsh
;;
;; This is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;;
;; This is a partial replacement for X-Symbol for Proof General.
;; STATUS: experimental.  
;;
;; Functions to help insert tokens that represent Unicode characters
;; and control code sequences for changing the layout.  Character
;; tokens are useful for programs that do not understand a Unicode
;; encoding.
;; 

;; TODO:
;; -- add input methods for subscript/superscripts (further props in general)
;; -- after change function so inserting control sequences works? or other support
;; -- one-char subs should not be sticky so doesn't extend
;; -- make property removal more accurate/patch in font-lock
;; -- disentangle Isabelle specific code
;; -- perhaps separate out short-cut input method and don't use for tokens
;; -- cleanup insertion functions
;; -- investigate testing for an appropriate glyph

(require 'cl)

(require 'unicode-chars)		; list of Unicode characters

;;
;; Variables that should be set
;; (default settings are for XML, but configuration incomplete; 
;;  use xmlunicode.el instead)
;;

(defvar unicode-tokens2-charref-format "&#x%x;"
  "The format for numeric character references")

(defvar unicode-tokens2-token-format "&%x;"
  "The format for token character references")

(defvar unicode-tokens2-token-name-alist nil
  "Mapping of token names to Unicode strings.")

(defvar unicode-tokens2-glyph-list nil
  "List of available glyphs, as characters.
If not set, constructed to include glyphs for all tokens. ")

(defvar unicode-tokens2-token-prefix "&"
  "Prefix for start of tokens to insert.")

(defvar unicode-tokens2-token-suffix ";"
  "Suffix for end of tokens to insert.")

(defvar unicode-tokens2-control-token-match nil
  "Regexp matching tokens")

(defvar unicode-tokens2-token-match "&\\([A-Za-z]\\);"
  "Regexp matching tokens")

(defvar unicode-tokens2-hexcode-match "&#[xX]\\([0-9a-fA-F]+\\);"
  "Regexp matching numeric token string")

(defvar unicode-tokens2-next-character-regexp "&#[xX]\\([0-9a-fA-F]+\\);\\|."
  "Regexp matching a logical character following a control code.")

(defvar unicode-tokens2-shortcut-alist
  "An alist of keyboard shortcuts to unicode strings.
The alist is added to the input mode for tokens.
Behaviour is much like abbrev.")

;;
;; Faces
;;

;;
;; TODO: make these into faces but extract attributes
;; to use in `unicode-tokens2-annotation-translations'.
;; Let that be dynamically changeable
;; TODO: choose family acccording to likely architecture and what's available
(cond
 ((not (featurep 'xemacs))
(defface unicode-tokens2-script-font-face
  (cond
   ((eq window-system 'x) ; Linux/Unix
    '((t :family "URW Chancery L")))
   ((or ; Mac
     (eq window-system 'ns)
     (eq window-system 'carbon))
    '((t :family "Lucida Calligraphy"))))
  "Script font face")

(defface unicode-tokens2-fraktur-font-face
  (cond
   ((eq window-system 'x) ; Linux/Unix
    '((t :family "URW Bookman L"))) ;; not at all black letter!
   ((or ; Mac
     (eq window-system 'ns)
     (eq window-system 'carbon))
    '((t :family "Lucida Blackletter"))))
  "Fraktur font face")

(defface unicode-tokens2-serif-font-face
  (cond
   ((eq window-system 'x) ; Linux/Unix
    '((t :family "Liberation Serif"))) 
   ((or ; Mac
     (eq window-system 'ns)
     (eq window-system 'carbon))
    '((t :family "Lucida"))))
  "Serif (roman) font face")))


;;
;; Variables initialised in unicode-tokens2-initialise 
;;

(defvar unicode-tokens2-max-token-length 10
  "Maximum length of a token in underlying encoding.")

(defvar unicode-tokens2-codept-charname-alist nil
  "Alist mapping unicode code point to character names.")

(defvar unicode-tokens2-token-alist nil
  "Mapping of tokens to Unicode strings.
Also used as a flag to detect if `unicode-tokens2-initialise' has been called.")

(defvar unicode-tokens2-ustring-alist nil
  "Mapping of Unicode strings to tokens.")


;;
;;; Code:
;;

(defun unicode-tokens2-insert-char (arg codepoint)
  "Insert the Unicode character identified by CODEPOINT.
If ARG is non-nil, ignore available glyphs."
  (let ((glyph (memq codepoint unicode-tokens2-glyph-list)))
    (cond
     ((and (decode-char 'ucs codepoint) (or arg glyph))
      (ucs-insert codepoint)) ;; glyph converted to token on save
     (t
      (insert (format unicode-tokens2-charref-format codepoint))))))

(defun unicode-tokens2-insert-string (arg ustring)
  "Insert a Unicode string.
If a prefix is given, the string will be inserted regardless
of whether or not it has displayable glyphs; otherwise, a
numeric character reference for whichever codepoints are not
in the unicode-tokens2-glyph-list."
  (mapcar (lambda (char) 
	    (unicode-tokens2-insert-char arg char))
	  ustring))

(defun unicode-tokens2-character-insert (arg &optional argname)
  "Insert a Unicode character by character name, with completion. 
If a prefix is given, the character will be inserted regardless
of whether or not it has a displayable glyph; otherwise, a
numeric character reference is inserted if the codepoint is not
in the `unicode-tokens2-glyph-list'. If argname is given, it is used for
the prompt. If argname uniquely identifies a character, that
character is inserted without the prompt."
  (interactive "P")
  (let* ((completion-ignore-case t)
	 (uniname (if (stringp argname) argname ""))
	 (charname
	  (if (eq (try-completion uniname unicode-chars-alist) t)
	      uniname
	    (completing-read
	     "Unicode name: "
	     unicode-chars-alist
	     nil t uniname)))
	 codepoint glyph)
    (setq codepoint (cdr (assoc charname unicode-chars-alist)))
    (unicode-tokens2-insert-char arg codepoint)))

(defun unicode-tokens2-token-insert (arg &optional argname)
  "Insert a Unicode string by a token  name, with completion. 
If a prefix is given, the string will be inserted regardless
of whether or not it has displayable glyphs; otherwise, a
numeric character reference for whichever codepoints are not
in the unicode-tokens2-glyph-list. If argname is given, it is used for
the prompt. If argname uniquely identifies a character, that
character is inserted without the prompt."
  (interactive "P")
  (let* ((stokname (if (stringp argname) argname ""))
	 (tokname
	  (if (eq (try-completion stokname unicode-tokens2-token-name-alist) t)
	      stokname
	    (completing-read
	     "Token name: "
	     unicode-tokens2-token-name-alist
	     nil t stokname)))
	 charname ustring)
    (setq ustring (cdr (assoc tokname unicode-tokens2-token-name-alist)))
    (unicode-tokens2-insert-string arg ustring)))

(defun unicode-tokens2-replace-token-after (length)
  (let ((bpoint (point)) ustring)
    (save-excursion
      (forward-char length)
      (save-match-data
	(while (re-search-backward 
		unicode-tokens2-token-match 
		(max (- bpoint unicode-tokens2-max-token-length) 
		     (point-min)) t nil)
	  (setq ustring 
		(assoc (match-string 1) unicode-tokens2-token-name-alist))
	  (if ustring ;; TODO: should check on glyphs here
	      (progn
		(let ((matchlen (- (match-end 0) (match-beginning 0))))
		  (replace-match (replace-quote (cdr ustring)))
		  ;; was: (format "%c" (decode-char 'ucs (cadr codept)))
		  (setq length 
			(+ (- length matchlen) (length (cdr ustring)))))))))))
    length)


;;stolen from hen.el which in turn claims to have stolen it from cxref
(defun unicode-tokens2-looking-backward-at (regexp)
  "Return t if text before point matches regular expression REGEXP.
This function modifies the match data that `match-beginning',
`match-end' and `match-data' access; save and restore the match
data if you want to preserve them."
  (save-excursion
    (let ((here (point)))
      (if (re-search-backward regexp (point-min) t)
          (if (re-search-forward regexp here t)
              (= (point) here))))))

;; TODO: make this work for control tokens.  
;; But it's a bit nasty and introduces font-lock style complexity again.
;; Better if we stick with dedicated input methods.
(defun unicode-tokens2-electric-suffix ()
  "Detect tokens and replace them with the appropriate string.
This is bound to the character ending `unicode-tokens2-token-suffix'
if there is such a unique character."
  (interactive)
  (let ((pos (point))
	(case-fold-search nil)
	amppos codept ustring)
    (search-backward unicode-tokens2-token-prefix nil t nil)
    (setq amppos (point))
    (goto-char pos)
    (cond
     ((unicode-tokens2-looking-backward-at unicode-tokens2-token-match)
      (progn
	(re-search-backward unicode-tokens2-token-match nil t nil)
	(if (= amppos (point))
	    (progn
	      (setq ustring 
		     (assoc (match-string 1) 
			    unicode-tokens2-token-name-alist))
	      (if ustring  ;; todo: check glyphs avail/use insert fn
		  (replace-match (replace-quote (cdr ustring)))
		   ;; was (format "%c" (decode-char 'ucs (cdr codept))))
		(progn
		  (goto-char pos)
		  (insert unicode-tokens2-token-suffix))))
	  (progn
	    (goto-char pos)
	    (insert unicode-tokens2-token-suffix)))))
     ((unicode-tokens2-looking-backward-at unicode-tokens2-hexcode-match)
      (progn
	(re-search-backward unicode-tokens2-hexcode-match nil t nil)
	(if (= amppos (point))
	    (progn
	      (setq codept (string-to-number (match-string 1) 16))
	      (if ;; todo : check glyph (memq codept unicode-tokens2-glyph-list)
		  codept
		  (replace-match (format "%c" (decode-char 'ucs (cdr codept))))
		(progn
		  (goto-char pos)
		  (insert unicode-tokens2-token-suffix))))
	  (progn
	    (goto-char pos)
	    (insert unicode-tokens2-token-suffix)))))
     (t
      (insert unicode-tokens2-token-suffix)))))

(defvar unicode-tokens2-rotate-glyph-last-char nil)

(defun unicode-tokens2-rotate-glyph-forward (&optional n)
  "Rotate the character before point in the current code page, by N steps.
If no character is found at the new codepoint, no change is made.
This function may only work reliably for GNU Emacs >= 23."
  (interactive "p")
  (if (> (point) (point-min))
      (let* ((codept  (or (if (or (eq last-command
				      'unicode-tokens2-rotate-glyph-forward)
				  (eq last-command
				      'unicode-tokens2-rotate-glyph-backward))
			      unicode-tokens2-rotate-glyph-last-char)
			  (char-before (point))))
	     (page    (/ codept 256))
	     (pt      (mod codept 256))
	     (newpt   (mod (+ pt (or n 1)) 256))
	     (newcode (+ (* 256 page) newpt))
	     (newname (assoc newcode 
			     unicode-tokens2-codept-charname-alist))
	     ;; NOTE: decode-char 'ucs here seems to fail on Emacs <23
	     (newchar (decode-char 'ucs newcode)))
	(when (and newname newchar)
	  (delete-char -1)
	  (insert-char newchar 1)
	  (message (cdr newname))
	  (setq unicode-tokens2-rotate-glyph-last-char nil))
	(unless (and newname newchar)
	  (message "No character at code %d" newcode)
	  (setq unicode-tokens2-rotate-glyph-last-char newcode)))))

(defun unicode-tokens2-rotate-glyph-backward (&optional n)
  "Rotate the character before point in the current code page, by -N steps.
If no character is found at the new codepoint, no change is made.
This function may only work reliably for GNU Emacs >= 23."
  (interactive "p")
  (unicode-tokens2-rotate-glyph-forward (if n (- n) -1)))
    


(defconst unicode-tokens2-ignored-properties
  '(vanilla type fontified face auto-composed
    rear-nonsticky field inhibit-line-move-field-capture
    utoks)
  "Text properties to ignore when saving files.")

(defconst unicode-tokens2-annotation-translations
  `((font-lock-face
     (bold		"bold")
     (unicode-tokens2-script-font-face "script")
     (unicode-tokens2-fraktur-font-face "frak")
     (unicode-tokens2-serif-font-face "serif")
     (proof-declaration-name-face "loc1")
     (default	))
    (display   
     ((raise 0.4)    "superscript")
     ((raise -0.4)   "subscript")
     ((raise 0.35)  "superscript1")
     ((raise -0.35) "subscript1")
     ((raise -0.3)   "idsubscript1")
     (default	)))
  "Text property table for annotations.")


(defun unicode-tokens2-font-lock-keywords ()
  "Calculate value for `font-lock-keywords'."
  (when (fboundp 'compose-region)
    (let ((alist nil))
      (dolist (x unicode-tokens2-token-name-alist)
	(when (and (if (fboundp 'char-displayable-p)
		       (reduce (lambda (x y) (and x (char-displayable-p y)))
			       (cdr x)
			       :initial-value t))
		     t)
		   (not (assoc (car x) alist)))	;Not yet in alist.
	  (push (cons
		 (format unicode-tokens2-token-format (car x))
		 (cdr x))
		alist)))
      (when alist
	(setq unicode-tokens2-token-alist alist)
	`((,(regexp-opt (mapcar 'car alist) t)
	   (0 (unicode-tokens2-compose-symbol)
              ;; In Emacs-21, if the `override' field is nil, the face
              ;; expressions is only evaluated if the text has currently
              ;; no face.  So force evaluation by using `keep'.
              keep))))))

   

  
(defvar unicode-tokens2-next-control-token-seen-token nil
  "Records currently open single-character control token.")

(defun unicode-tokens2-next-control-token ()
  "Find next control token and interpret it.
If `unicode-tokens2-next-control-token' is non-nil, end current control sequence
after next character (single character control sequence)."
  (let (result)
    (when unicode-tokens2-next-control-token-seen-token
      (if (re-search-forward unicode-tokens2-next-character-regexp nil t)
	  (setq result (list (match-end 0) (match-end 0)
			     unicode-tokens2-next-control-token-seen-token 
			     nil)))
      (setq unicode-tokens2-next-control-token-seen-token nil))
    (while (and (not result)
		(re-search-forward unicode-tokens2-control-token-match nil t))
      (let*
	  ((tok  (match-string 1))
	   (annot
	    (cond
	     ((equal tok "bsup")    '("superscript" t))
	     ((equal tok "esup")    '("superscript" nil))
	     ((equal tok "bsub")    '("subscript" t))
	     ((equal tok "esub")    '("subscript" nil))
	     ((equal tok "bbold")   '("bold" t))
	     ((equal tok "ebold")   '("bold" nil))
	     ((equal tok "bitalic") '("italic" t))
	     ((equal tok "eitalic") '("italic" nil))
	     ((equal tok "bscript") '("script" t))
	     ((equal tok "escript") '("script" nil))
	     ((equal tok "bfrak")   '("frak" t))
	     ((equal tok "efrak")   '("frak" nil))
	     ((equal tok "bserif")  '("serif" t))
	     ((equal tok "eserif")  '("serif" nil))
	     ((equal tok "loc") 
	      (list (setq unicode-tokens2-next-control-token-seen-token
			  "loc1") t))
	     ((equal tok "sup") 
	      (list (setq unicode-tokens2-next-control-token-seen-token
			  "superscript1") t))
	     ((equal tok "sub") 
	      (list (setq unicode-tokens2-next-control-token-seen-token
			  "subscript1") t))
	     ((equal tok "isub") 
	      (list (setq unicode-tokens2-next-control-token-seen-token
			  "idsubscript1") t)))))
	(if annot
	    (setq result
		  (append
		   (list (match-beginning 0) (match-end 0))
		   annot)))))
    result))

;; TODO: this should be instance specific  
(defconst unicode-tokens2-annotation-control-token-alist 
  '(("bold" .         ("bbold" . "ebold"))
    ("subscript" .    ("bsub" . "esub"))
    ("superscript" .  ("bsup" . "esup"))
    ("subscript1" .   ("sub"))
    ("superscript1" . ("sup"))
    ("loc1"	    . ("loc"))
    ;; non-standard
    ("italic" .       ("bitalic" . "eitalic"))
    ("script" .       ("bscript" . "escript"))
    ("frak" .         ("bfrak" . "efrak"))
    ("serif" .        ("bserif" . "eserif"))))
  
(defun unicode-tokens2-make-token-annotation (annot positive)
  "Encode a text property start/end by adding an annotation in the file."
  (let ((toks (cdr-safe
	       (assoc annot unicode-tokens2-annotation-control-token-alist))))
    (cond
     ((and toks positive)
      (format unicode-tokens2-control-token-format  (car toks)))
     ((and toks (cdr toks))
      (format unicode-tokens2-control-token-format  (cdr toks)))
     (t ""))))

(defun unicode-tokens2-find-property (name)
  (let ((props unicode-tokens2-annotation-translations)
	prop vals val vname)
    (catch 'return
      (while props
	(setq prop (caar props))
	(setq vals (cdar props))
	(while vals
	  (setq val (car vals))
	  (if (member name (cdr val))
	      (throw 'return (list prop (car val))))
	  (setq vals (cdr vals)))
	(setq props (cdr props))))))
      
(defun unicode-tokens2-annotate-region (beg end &optional annot)
  (interactive "r")
  (or annot 
      (if (interactive-p)
	  (setq annot
		(completing-read "Annotate region as: " 
				 unicode-tokens2-annotation-control-token-alist
				 nil t))
	(error "In unicode-tokens2-annotation-control-token-alist: TYPE must be given.")))
  (add-text-properties beg end
		       (unicode-tokens2-find-property annot)))

(defun unicode-tokens2-annotate-string (annot string)
  (add-text-properties 0 (length string)
		       (unicode-tokens2-find-property annot)
		       string)
  string)

(defun unicode-tokens2-unicode-to-tokens (&optional start end buffer)
  "Encode a buffer to save as a tokenised file."
  (let ((case-fold-search proof-case-fold-search)
	(buffer-undo-list t)
	(modified (buffer-modified-p)))
    (save-restriction
      (save-excursion
	(narrow-to-region (or start (point-min)) (or end (point-max)))
	(format-insert-annotations
	 (format-annotate-region (point-min) (point-max) 
				 unicode-tokens2-annotation-translations
				 'unicode-tokens2-make-token-annotation
				 unicode-tokens2-ignored-properties))
;; alternative experiment: store original tokens inside text properties
;;	(unicode-tokens2-replace-strings-unpropertise)
	(format-replace-strings unicode-tokens2-ustring-alist 
				nil (point-min) (point-max))
	(set-buffer-modified-p modified)))))


(defun unicode-tokens2-replace-strings-propertise (alist &optional beg end)
  "Do multiple replacements on the buffer.
ALIST is a list of (FROM . TO) pairs, which should be proper arguments to
`search-forward' and `replace-match', respectively.
The original contents FROM are retained in the buffer in the text property `utoks'.
Optional args BEG and END specify a region of the buffer on which to operate."
  (save-excursion
    (save-restriction
      (or beg (setq beg (point-min)))
      (if end (narrow-to-region (point-min) end))
      (while alist
	(let ((from (car (car alist)))
	      (to   (cdr (car alist)))
	      (case-fold-search nil))
	  (goto-char beg)
	  (while (search-forward from nil t)
	    (goto-char (match-beginning 0))
	    (insert to)
	    (set-text-properties (- (point) (length to)) (point)
				 (cons 'utoks
				       (cons from 
					     (text-properties-at (point)))))
	    (delete-region (point) (+ (point) (- (match-end 0)
						 (match-beginning 0)))))
	  (setq alist (cdr alist)))))))

;; NB: this is OK, except that now if we edit with raw symbols, we
;; don't get desired effect but instead rely on hidden annotations.
;; Also doesn't work as easily with quail.
;; Can we have a sensible mixture of both things?
(defun unicode-tokens2-replace-strings-unpropertise (&optional beg end)
  "Reverse the effect of `unicode-tokens2-replace-strings-unpropertise'.
Replaces contiguous text with 'utoks' property with property value."
  (let ((pos (or beg (point-min)))
	(lim (or end (point-max)))
	start to)
    (save-excursion
      (while (and 
	      (setq pos (next-single-property-change pos 'utoks nil lim))
	      (< pos lim))
	(if start
	    (progn
	      (setq to (get-text-property start 'utoks))
	      (goto-char start)
	      (insert to)
	      (set-text-properties start (point)
				   (text-properties-at start))
	      (delete-region (point) (+ (point) (- pos start)))
	      (setq start nil))
	  (setq start pos))))))
	  


  

;; 
;; Minor mode
;;

(defvar unicode-tokens2-mode-map (make-sparse-keymap)
  "Key map used for Unicode Tokens mode.")

(define-minor-mode unicode-tokens2-mode
  "Minor mode for unicode token input." nil " Utoks"
  unicode-tokens2-mode-map
  (unless unicode-tokens2-token-alist
    (unicode-tokens2-initialise))
  (when unicode-tokens2-mode
    (when (boundp 'text-property-default-nonsticky)
      (make-variable-buffer-local 'text-property-default-nonsticky)
      (setq text-property-default-nonsticky
	    ;; We want to use display property with stickyness
	    (delete '(display . t) text-property-default-nonsticky)))
    (if (and
	 (fboundp 'set-buffer-multibyte)
	 (not (buffer-base-buffer)))
	(set-buffer-multibyte t))
    (let ((inhibit-read-only t))
      ;; format is supposed to manage undo, but doesn't remap
      (setq buffer-undo-list nil) 
      (format-decode-buffer 'unicode-tokens2))
    (set-input-method "Unicode tokens"))
  (unless unicode-tokens2-mode
    (when (boundp 'text-property-default-nonsticky)
      (add-to-list 'text-property-default-nonsticky '(display . t)))
    ;; leave buffer encoding as is
    (let ((inhibit-read-only t)
	  (modified (buffer-modified-p)))
      ;; format is supposed to manage undo, but doesn't remap
      (setq buffer-undo-list nil) 
      (format-encode-buffer 'unicode-tokens2)
      (unicode-tokens2-remove-properties (point-min) (point-max))
      (set-buffer-modified-p modified))
    (inactivate-input-method)))

;; 
;; Initialisation
;;
(defun unicode-tokens2-initialise ()
  "Initialise tables."
  ;; Calculate max token length
  (let ((tlist unicode-tokens2-token-name-alist)
	(len 0) tok)
    (while tlist
      (when (> (length (caar tlist)) 0)
	  (setq len (length (caar tlist)))
	  (setq tok (caar tlist)))
      (setq tlist (cdr tlist)))
    (setq unicode-tokens2-max-token-length
	  (length (format unicode-tokens2-token-format tok))))
  ;; Names from code points
  (setq unicode-tokens2-codept-charname-alist
	(mapcar (lambda (namechar)
		  (cons (cdr namechar) (car namechar)))
		unicode-chars-alist))
  ;; Default assumed available glyph list based on tokens;
  ;; TODO: filter with what's really available, if can find out.
  ;; TODO: allow altering of this when the token-name-alist is reset
  ;; in proof-token-name-alist (unless test here is for specific setting)
  (unless unicode-tokens2-glyph-list
    (setq unicode-tokens2-glyph-list
	  (reduce (lambda (glyphs tokustring)
		    (append glyphs (string-to-list (cdr tokustring))))
		  unicode-tokens2-token-name-alist
		  :initial-value nil)))
  (unicode-tokens2-quail-define-rules)
  ;; Key bindings
  (if (= (length unicode-tokens2-token-suffix) 1)
      (define-key unicode-tokens2-mode-map
	(vector (string-to-char unicode-tokens2-token-suffix))
	'unicode-tokens2-electric-suffix))
   (define-key unicode-tokens2-mode-map [(control ?,)]
     'unicode-tokens2-rotate-glyph-backward)
   (define-key unicode-tokens2-mode-map [(control ?.)]
     'unicode-tokens2-rotate-glyph-forward)
  ;; otherwise action on space like in X-Symbol?
  )


(provide 'unicode-tokens2)

;;; unicode-tokens2.el ends here
