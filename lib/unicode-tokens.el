;;; unicode-tokens.el --- Support for editing tokens for Unicode characters
;;
;; Copyright(C) 2008 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; This is a partial replacement for X-Symbol for Proof General.
;;
;; Some functions are taken from `xmlunicode.el' by Norman Walsh.
;; Created: 2004-07-21, Version: 1.6, Copyright (C) 2003 Norman Walsh
;; Inspired in part by sgml-input, Copyright (C) 2001 Dave Love
;; Inspired in part by 
;;  http://www.tbray.org/ongoing/When/200x/2003/09/27/UniEmacs
;;
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
;; TODO:
;; -- add coding/decoding for saving/reading files


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

(defvar unicode-token-name-alist nil
  "Mapping of token names to Unicode character names.")

(defvar unicode-tokens-glyph-list nil
  "List of available glyphs, as characters.
If not set, constructed to include glyphs for all tokens. ")

(defvar unicode-tokens-token-prefix nil
  "Prefix for start of tokens to insert.")

(defvar unicode-tokens-token-suffix nil
  "Suffix for end of tokens to insert.")

(defvar unicode-tokens-token-match nil
  "Regexp matching tokens")

(defvar unicode-tokens-hexcode-match nil
  "Regexp matching numeric token string")



;;
;; Variables initialised in unicode-tokens-initialise 
;;

(defvar unicode-token-name-codepoint-alist nil
  "Mapping of token names to Unicode codepoints.")

(defvar unicode-tokens-max-token-length 10
  "Maximum length of a token in underlying encoding.")


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
  "Insert a Unicode character by a token  name, with completion. 
If a prefix is given, the character will be inserted regardless
of whether or not it has a displayable glyph; otherwise, a
numeric character reference is inserted if the codepoint is not
in the unicode-tokens-glyph-list. If argname is given, it is used for
the prompt. If argname uniquely identifies a character, that
character is inserted without the prompt."
  (interactive "P")
  (let* ((stokname (if (stringp argname) argname ""))
	 (tokname
	  (if (eq (try-completion stokname unicode-token-name-alist) t)
	      stokname
	    (completing-read
	     "Token name: "
	     unicode-token-alist
	     nil t stokname)))
	 charname codepoint glyph)
    (setq charname (cdr (assoc tokame unicode-token-name-alist)))
    (setq codepoint (cdr-safe (assoc charname unicode-chars-alist)))
    (unicode-tokens-insert-char arg codepoint)))


(defun unicode-tokens-replace-token-after (length)
  (let ((bpoint (point)))
    (save-excursion
      (forward-char length)
      (save-match-data
	(while (re-search-backward 
		unicode-token-match 
		(max (- bpoint unicode-tokens-max-token-length) 
		     (point-min)) t nil)
	  (setq codept 
		(assoc (match-string 1) unicode-tokens-codept-alist))
	  (if (and codept
		   (memq (cadr codept) unicode-tokens-glyph-list))
	      (progn
		(replace-match (format "%c" (decode-char 'ucs (cadr codept))))
		;; FIXME: return correct length
		;; something like 1-length-point  modulo chars replaced
		(setq length length)))))))
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

(defun unicode-tokens-smart-suffix ()
  "Detect tokens and replace them with the appropriate char.
This can be bound to the character ending `unicode-tokens-token-suffix'
if there is such a unique character."
  (interactive)
  (let ((pos (point))
	amppos codept)
    (search-backward unicode-tokens-token-prefix nil t nil)
    (setq amppos (point))
    (goto-char pos)
    (cond
     ((unicode-tokens-looking-backward-at unicode-tokens-token-match)
      (progn
	(re-search-backward unicode-tokens-token-match nil t nil)
	(if (= amppos (point))
	    (progn
	      (setq codept 
		     (assoc (match-string 1) 
			    unicode-tokens-token-codept-alist))
	      (if (and codept
		       (memq (cdr codept) unicode-tokens-glyph-list))
		  (replace-match (format "%c" (decode-char 'ucs (cdr codept))))
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
	      (if (memq codept unicode-tokens-glyph-list)
		  (replace-match (format "%c" (decode-char 'ucs (cdr codept))))
		(progn
		  (goto-char pos)
		  (insert unicode-tokens-token-suffix))))
	  (progn
	    (goto-char pos)
	    (insert unicode-tokens-token-suffix)))))
     (t
      (insert unicode-tokens-token-suffix)))))

;;
;; Coding system for saving tokens in plain ASCII.
;;

(make-coding-system 'unicode-tokens-coding-system 
  4 ; ccl
  "Unicode token coding system"
  (cons 'unicode-tokens-ccl-decode
	'unicode-tokens-ccl-encode))


;; Emacs-Unicode/23:
;;(define-coding-system 'unicode-tokens-coding-system 
;;   "Unicode token coding system"
;;   :mnemonic ?T
;;   :coding-type 'raw-text  ; could be 'undecided/ccl
;;   ;; omit for automatic guess :eol-type 
;;   ;; :charset-list iso-20222
;;   :ascii-compatible-p t
;;   :decode-translation-table
;;   :encode-translation-table )



;;
;; Setup quail for Unicode tokens mode
;;

(require 'quail)

(quail-define-package
 "Unicode tokens" "UTF-8" "T" t
 "Unicode characters input method using application specific token names"
 nil t nil nil nil t nil nil nil nil t)

(defun unicode-tokens-quail-define-rules ()
  "Define the token input rules.
Calculated from `unicode-tokens-token-name-alist' and `unicode-tokens-glyph-list'."
  (let ((ulist unicode-tokens-token-name-alist)
      codepoint glyph tokname token
      unicode-tokens-quail-define-rules)
  (while ulist
    (setq tokname (caar ulist))
    (setq charname (cdar ulist))
    (setq codepoint (cdr (assoc charname unicode-chars-alist)))
    (unless codepoint
	(error "Unicode character %s not found" charname))
    (setq glyph (memq codepoint unicode-tokens-glyph-list))
    (setq token (format unicode-tokens-token-format tokname))
    (cond
     ((and glyph (decode-char 'ucs codepoint))
      (nconc unicode-tokens-quail-define-rules
	     (list (list token (decode-char 'ucs codepoint))))))
;     (t ; still use token if no glyph
;      (nconc unicode-tokens-quail-define-rules
;	     (list (list token (vector token))))))
    (setq ulist (cdr ulist)))
  (eval unicode-tokens-quail-define-rules)))




;; 
;; Minor mode
;;

(defvar unicode-tokens-mode-map (make-sparse-keymap)
  "Key map used for Unicode Tokens mode.")

(define-minor-mode unicode-tokens-mode
  "Minor mode for unicode token input."
  nil 
  nil ; input method indication already
  unicode-tokens-mode-map
  (when unicode-tokens-mode
    (set-buffer-multibyte t)
    (decode-coding-region (point-min) (point-max) 
			  'unicode-tokens-coding-system))
  (unless unicode-tokens-mode
    (set-buffer-multibyte nil)
    (encode-coding-region (point-min) (point-max) 
			  'unicode-tokens-coding-system))
  ;(toggle-enable-multibyte-characters unicode-tokens-mode)
  (set-input-method "Unicode tokens" unicode-tokens-mode)
  )

;; 
;; Initialisation
;;

(defun unicode-tokens-initialise ()
  "Initialise tables."
  ;; Calculate max token length
  (let ((tlist unicode-token-name-alist)
	(len 0) tok)
    (while tlist
      (when (> (length (car tlist)) 0)
	  (setq len (length (car tlist)))
	  (setq tok (car tlist)))
      (setq tlist (cdr tlist)))
    (setq unicode-tokens-max-token-length
	  (length (format unicode-tokens-token-format tok))))
  ;; Default assumed available glyph list based on tokens;
  ;; TODO: filter with what's really available, if can find out.
  (setq unicode-tokens-token-codept-alist
	(mapcar (lambda (uchar) 
		  (let ((codept (assoc (cdr uchar) unicode-chars-alist)))
		    (unless codept
		      (error "Unicode character %s unknown" uchar))
		    (cons (car uchar) (cdr codept))))
		unicode-tokens-token-name-alist))
  (unless unicode-tokens-glyph-list
    (setq unicode-tokens-glyph-list
	  (mapcar 'cdr unicode-tokens-token-codept-alist)))
  (unicode-tokens-quail-define-rules)
  ;; Keys
  (if (= (length unicode-tokens-token-suffix) 1)
      (define-key unicode-tokens-mode-map
	(vector (string-to-char unicode-tokens-token-suffix))
	'unicode-tokens-smart-suffix))
  ;; otherwise action on space like in X-Symbol?
  )


(provide 'unicode-tokens)

;;; unicode-tokens.el ends here
