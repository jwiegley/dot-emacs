;;; unicode-tokens.el --- Support for editing tokens for Unicode characters
;;
;; Copyright(C) 2008 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; This is a partial replacement for X-Symbol for Proof General.
;; STATUS: experimental.  Super/subscripts not yet supported.
;;
;; Some functions are adapted from `xmlunicode.el' by Norman Walsh.
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
;; Functions to help insert tokens that represent Unicode characters.
;; Tokens are used for programs that do not understand a Unicode encoding.
;; 


(require 'cl)

(require 'unicode-chars)		; list of Unicode characters

;;
;; Variables that should be set
;; (default settings are for XML, but configuration incomplete; 
;;  use xmlunicode.el instead)
;;

(defvar unicode-tokens-charref-format "&#x%x;"
  "The format for numeric character references")

(defvar unicode-tokens-token-format "&%x;"
  "The format for token character references")

(defvar unicode-tokens-token-name-alist nil
  "Mapping of token names to Unicode strings.")

(defvar unicode-tokens-glyph-list nil
  "List of available glyphs, as characters.
If not set, constructed to include glyphs for all tokens. ")

(defvar unicode-tokens-token-prefix "&"
  "Prefix for start of tokens to insert.")

(defvar unicode-tokens-token-suffix ";"
  "Suffix for end of tokens to insert.")

(defvar unicode-tokens-token-match "&#[xX][0-9a-fA-F]+"
  "Regexp matching tokens")

(defvar unicode-tokens-hexcode-match "&#[xX]\\([0-9a-fA-F]+\\)"
  "Regexp matching numeric token string")

(defvar unicode-tokens-shortcut-alist
  "An alist of keyboard shortcuts to unicode strings.
The alist is added to the input mode for tokens.
Behaviour is much like abbrev.")


;;
;; Variables initialised in unicode-tokens-initialise 
;;

(defvar unicode-tokens-max-token-length 10
  "Maximum length of a token in underlying encoding.")

(defvar unicode-tokens-codept-charname-alist nil
  "Alist mapping unicode code point to character names.")

(defvar unicode-tokens-token-alist nil
  "Mapping of tokens to Unicode strings.")

(defvar unicode-tokens-ustring-alist nil
  "Mapping of Unicode strings to tokens.")


;;
;;; Code:
;;

(defun unicode-tokens-insert-char (arg codepoint)
  "Insert the Unicode character identified by CODEPOINT.
If ARG is non-nil, ignore available glyphs."
  (let ((glyph (memq codepoint unicode-tokens-glyph-list)))
    (cond
     ((and (decode-char 'ucs codepoint) (or arg glyph))
      (ucs-insert codepoint)) ;; glyph converted to token on save
     (t
      (insert (format unicode-tokens-charref-format codepoint))))))

(defun unicode-tokens-insert-string (arg ustring)
  "Insert a Unicode string.
If a prefix is given, the string will be inserted regardless
of whether or not it has displayable glyphs; otherwise, a
numeric character reference for whichever codepoints are not
in the unicode-tokens-glyph-list."
  (mapcar (lambda (char) 
	    (unicode-tokens-insert-char arg char))
	  ustring))

(defun unicode-tokens-character-insert (arg &optional argname)
  "Insert a Unicode character by character name, with completion. 
If a prefix is given, the character will be inserted regardless
of whether or not it has a displayable glyph; otherwise, a
numeric character reference is inserted if the codepoint is not
in the `unicode-tokens-glyph-list'. If argname is given, it is used for
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
    (unicode-tokens-insert-char arg codepoint)))

(defun unicode-tokens-token-insert (arg &optional argname)
  "Insert a Unicode string by a token  name, with completion. 
If a prefix is given, the string will be inserted regardless
of whether or not it has displayable glyphs; otherwise, a
numeric character reference for whichever codepoints are not
in the unicode-tokens-glyph-list. If argname is given, it is used for
the prompt. If argname uniquely identifies a character, that
character is inserted without the prompt."
  (interactive "P")
  (let* ((stokname (if (stringp argname) argname ""))
	 (tokname
	  (if (eq (try-completion stokname unicode-tokens-token-name-alist) t)
	      stokname
	    (completing-read
	     "Token name: "
	     unicode-tokens-token-name-alist
	     nil t stokname)))
	 charname ustring)
    (setq ustring (cdr (assoc tokname unicode-tokens-token-name-alist)))
    (unicode-tokens-insert-string arg ustring)))

(defun unicode-tokens-replace-token-after (length)
  (let ((bpoint (point)) ustring)
    (save-excursion
      (forward-char length)
      (save-match-data
	(while (re-search-backward 
		unicode-tokens-token-match 
		(max (- bpoint unicode-tokens-max-token-length) 
		     (point-min)) t nil)
	  (setq ustring 
		(assoc (match-string 1) unicode-tokens-token-name-alist))
	  (if ustring ;; TODO: should check on glyphs here
	      (progn
		(let ((matchlen (- (match-end 0) (match-beginning 0))))
		  (replace-match (cdr ustring))
		  ;; was: (format "%c" (decode-char 'ucs (cadr codept)))
		  (setq length 
			(+ (- length matchlen) (length (cdr ustring)))))))))))
    length)


;;stolen from hen.el which in turn claims to have stolen it from cxref
(defun unicode-tokens-looking-backward-at (regexp)
  "Return t if text before point matches regular expression REGEXP.
This function modifies the match data that `match-beginning',
`match-end' and `match-data' access; save and restore the match
data if you want to preserve them."
  (save-excursion
    (let ((here (point)))
      (if (re-search-backward regexp (point-min) t)
          (if (re-search-forward regexp here t)
              (= (point) here))))))

(defun unicode-tokens-electric-suffix ()
  "Detect tokens and replace them with the appropriate string.
This is bound to the character ending `unicode-tokens-token-suffix'
if there is such a unique character."
  (interactive)
  (let ((pos (point))
	amppos codept ustring)
    (search-backward unicode-tokens-token-prefix nil t nil)
    (setq amppos (point))
    (goto-char pos)
    (cond
     ((unicode-tokens-looking-backward-at unicode-tokens-token-match)
      (progn
	(re-search-backward unicode-tokens-token-match nil t nil)
	(if (= amppos (point))
	    (progn
	      (setq ustring 
		     (assoc (match-string 1) 
			    unicode-tokens-token-name-alist))
	      (if ustring  ;; todo: check glyphs avail/use insert fn
		  (replace-match (cdr ustring))
		   ;; was (format "%c" (decode-char 'ucs (cdr codept))))
		(progn
		  (goto-char pos)
		  (insert unicode-tokens-token-suffix))))
	  (progn
	    (goto-char pos)
	    (insert unicode-tokens-token-suffix)))))
     ((unicode-tokens-looking-backward-at unicode-tokens-hexcode-match)
      (progn
	(re-search-backward unicode-tokens-hexcode-match nil t nil)
	(if (= amppos (point))
	    (progn
	      (setq codept (string-to-number (match-string 1) 16))
	      (if ;; todo : check glyph (memq codept unicode-tokens-glyph-list)
		  codept
		  (replace-match (format "%c" (decode-char 'ucs (cdr codept))))
		(progn
		  (goto-char pos)
		  (insert unicode-tokens-token-suffix))))
	  (progn
	    (goto-char pos)
	    (insert unicode-tokens-token-suffix)))))
     (t
      (insert unicode-tokens-token-suffix)))))

(defvar unicode-tokens-rotate-glyph-last-char nil)

(defun unicode-tokens-rotate-glyph-forward (&optional n)
  "Rotate the character before point in the current code page, by N steps.
If no character is found at the new codepoint, no change is made."
  (interactive "p")
  (if (> (point) (point-min))
      (let* ((codept  (or (if (or (eq last-command
				      'unicode-tokens-rotate-glyph-forward)
				  (eq last-command
				      'unicode-tokens-rotate-glyph-backward))
			      unicode-tokens-rotate-glyph-last-char)
			  (char-before (point))))
	     (page    (/ codept 256))
	     (pt      (mod codept 256))
	     (newpt   (mod (+ pt (or n 1)) 256))
	     (newcode (+ (* 256 page) newpt))
	     (newname (assoc newcode 
			     unicode-tokens-codept-charname-alist))
	     ;; NOTE: decode-char 'ucs here seems to fail on Emacs <23
	     (newchar (decode-char 'ucs newcode)))
	(when (and newname newchar)
	  (delete-char -1)
	  (insert-char newchar 1)
	  (message (cdr newname))
	  (setq unicode-tokens-rotate-glyph-last-char nil))
	(unless (and newname newchar)
	  (message "No character at code %d" newcode)
	  (setq unicode-tokens-rotate-glyph-last-char newcode)))))

(defun unicode-tokens-rotate-glyph-backward (&optional n)
  "Rotate the character before point in the current code page, by -N steps.
If no character is found at the new codepoint, no change is made."
  (interactive "p")
  (unicode-tokens-rotate-glyph-forward (if n (- n) -1)))
    


;;
;; Setup quail for Unicode tokens mode
;;

(require 'quail)

(quail-define-package
 "Unicode tokens" "UTF-8" "u" t
 "Unicode characters input method using application specific token names"
 nil t nil nil nil nil nil nil nil nil t)

(defun unicode-tokens-map-ordering (s1 s2)
  "Ordering on (car S1, car S2): order longer strings first."
  (>= (length (car s1)) (length (car s2))))

(defun unicode-tokens-quail-define-rules ()
  "Define the token and shortcut input rules.
Calculated from `unicode-tokens-token-name-alist' and 
`unicode-tokens-shortcut-alist'.
Also sets `unicode-tokens-token-alist'."
  (let ((unicode-tokens-quail-define-rules 
	 (list 'quail-define-rules)))
    (let ((ulist (copy-list unicode-tokens-token-name-alist))
	  ustring tokname token)
      ;; sort in case of non-terminated token syntax (empty suffix)
      (setq ulist (sort ulist 'unicode-tokens-map-ordering))
      (setq unicode-tokens-token-alist nil)
      (while ulist
	(setq tokname (caar ulist))
	(setq ustring (cdar ulist))
	(setq token (format unicode-tokens-token-format tokname))
	(nconc unicode-tokens-quail-define-rules
	       (list (list token 
			   (vector ustring))))
	(setq unicode-tokens-token-alist
	      (nconc unicode-tokens-token-alist
		     (list (cons token ustring))))
	(setq ulist (cdr ulist))))
    ;; make reverse map: convert longer ustring sequences first
    (setq unicode-tokens-ustring-alist
	  (sort
	   (mapcar (lambda (c) (cons (cdr c) (car c))) 
		   unicode-tokens-token-alist)
	   'unicode-tokens-map-ordering))
    (let ((ulist (copy-list unicode-tokens-shortcut-alist))
	  ustring shortcut)
      (setq ulist (sort ulist 'unicode-tokens-map-ordering))
      (while ulist
	(setq shortcut (caar ulist))
	(setq ustring (cdar ulist))
	(nconc unicode-tokens-quail-define-rules
	       (list (list shortcut
			   (vector ustring))))
	(setq ulist (cdr ulist))))
    (eval unicode-tokens-quail-define-rules)))



;;
;; File format for saving tokens in plain ASCII.
;;

(defvar unicode-tokens-format-entry
  '(unicode-tokens "Tokens encoding unicode characters."
		   nil
		   unicode-tokens-tokens-to-unicode
		   unicode-tokens-unicode-to-tokens
		   t nil)
  "Value for `format-alist'.")

(defun unicode-tokens-tokens-to-unicode (&optional start end)
  (save-excursion
    (goto-char (or end (point-max)))
    (save-excursion
      (let ((case-fold-search proof-case-fold-search)
	    (buffer-undo-list t)
	    (modified (buffer-modified-p)))
	(format-replace-strings unicode-tokens-token-alist nil start end)
	(set-buffer-modified-p modified)))
    (point)))
  
(defun unicode-tokens-unicode-to-tokens (&optional start end buffer)
  (let ((case-fold-search proof-case-fold-search)
	(buffer-undo-list t)
	(modified (buffer-modified-p)))
    (format-replace-strings unicode-tokens-ustring-alist nil start end)
    (set-buffer-modified-p modified)))


  

;; 
;; Minor mode
;;

(defvar unicode-tokens-mode-map (make-sparse-keymap)
  "Key map used for Unicode Tokens mode.")

(define-minor-mode unicode-tokens-mode
  "Minor mode for unicode token input."
  nil 
  " Utoks" ; input method indication already
  unicode-tokens-mode-map
  (when unicode-tokens-mode
    (if (fboundp 'set-buffer-multibyte)
	(set-buffer-multibyte t))
    (let ((inhibit-read-only t))
      ;; format is supposed to manage undo, but doesn't remap
      (setq buffer-undo-list nil) 
      (format-decode-buffer 'unicode-tokens))
    (set-input-method "Unicode tokens"))
  (unless unicode-tokens-mode
    ;; leave buffer encoding as is
    (let ((inhibit-read-only t))
      ;; format is supposed to manage undo, but doesn't remap
      (setq buffer-undo-list nil) 
      (format-encode-buffer 'unicode-tokens))
    (inactivate-input-method)))

;; 
;; Initialisation
;;
(defun unicode-tokens-initialise ()
  "Initialise tables."
  ;; Calculate max token length
  (let ((tlist unicode-tokens-token-name-alist)
	(len 0) tok)
    (while tlist
      (when (> (length (caar tlist)) 0)
	  (setq len (length (caar tlist)))
	  (setq tok (caar tlist)))
      (setq tlist (cdr tlist)))
    (setq unicode-tokens-max-token-length
	  (length (format unicode-tokens-token-format tok))))
  ;; Names from code points
  (setq unicode-tokens-codept-charname-alist
	(mapcar (lambda (namechar)
		  (cons (cdr namechar) (car namechar)))
		unicode-chars-alist))
  ;; Default assumed available glyph list based on tokens;
  ;; TODO: filter with what's really available, if can find out.
  ;; TODO: allow altering of this when the token-name-alist is reset
  ;; in proof-token-name-alist (unless test here is for specific setting)
  (unless unicode-tokens-glyph-list
    (setq unicode-tokens-glyph-list
	  (reduce (lambda (glyphs tokustring)
		    (append glyphs (string-to-list (cdr tokustring))))
		  unicode-tokens-token-name-alist
		  :initial-value nil)))
  (unicode-tokens-quail-define-rules)
  (add-to-list 'format-alist unicode-tokens-format-entry)
  ;; Key bindings
  (if (= (length unicode-tokens-token-suffix) 1)
      (define-key unicode-tokens-mode-map
	(vector (string-to-char unicode-tokens-token-suffix))
	'unicode-tokens-electric-suffix))
   (define-key unicode-tokens-mode-map [(control ?,)]
     'unicode-tokens-rotate-glyph-backward)
   (define-key unicode-tokens-mode-map [(control ?.)]
     'unicode-tokens-rotate-glyph-forward)
  ;; otherwise action on space like in X-Symbol?
  )


(provide 'unicode-tokens)

;;; unicode-tokens.el ends here
