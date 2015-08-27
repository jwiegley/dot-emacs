;;; parsebib.el --- A library for parsing bib files

;; Copyright (c) 2014 Joost Kremers
;; All rights reserved.

;; Author: Joost Kremers <joostkremers@fastmail.fm>
;; Maintainer: Joost Kremers <joostkremers@fastmail.fm>
;; Created: 2014
;; Version: 1.0
;; Keywords: text bibtex
;; Package-Requires: ((emacs "24.3"))

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;;
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in the
;;    documentation and/or other materials provided with the distribution.
;; 3. The name of the author may not be used to endorse or promote products
;;    derived from this software without specific prior written permission.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
;; IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
;; OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
;; IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
;; INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
;; NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES ; LOSS OF USE,
;; DATA, OR PROFITS ; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
;; THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:

;;

;;; Code:

(require 'bibtex)
(require 'cl-lib)

(defconst parsebib--bibtex-identifier "[^^\"@\\&$#%',={}() \t\n\f]*" "Regexp describing a licit BibTeX identifier.")
(defconst parsebib--key-regexp "[^^\"@\\&$#%',={} \t\n\f]*" "Regexp describing a licit key.")
(defconst parsebib--entry-start "^[ \t]*@" "Regexp describing the start of an entry.")

;; Emacs 24.3 compatibility code.
(if (version-list-< (version-to-list emacs-version) '(24 4))
    ;; This definition is simply copied from the Emacs 24.4 sources
    (defun define-error (name message &optional parent)
      "Define NAME as a new error signal.
MESSAGE is a string that will be output to the echo area if such an error
is signaled without being caught by a `condition-case'.
PARENT is either a signal or a list of signals from which it inherits.
Defaults to `error'."
      (unless parent (setq parent 'error))
      (let ((conditions
             (if (consp parent)
                 (apply #'nconc
                        (mapcar (lambda (parent)
                                  (cons parent
                                        (or (get parent 'error-conditions)
                                            (error "Unknown signal `%s'" parent))))
                                parent))
               (cons parent (get parent 'error-conditions)))))
        (put name 'error-conditions
             (delete-dups (copy-sequence (cons name conditions))))
        (when message (put name 'error-message message)))))

(define-error 'parsebib-entry-type-error "Illegal entry type" 'error)

;;;;;;;;;;;;;;;;;;;;
;; matching stuff ;;
;;;;;;;;;;;;;;;;;;;;

(defun parsebib--looking-at-goto-end (str &optional match)
  "Like `looking-at' but moves point to the end of the matching string.
MATCH acts just like the argument to MATCH-END, and defaults to
0. Comparison is done case-insensitively."
  (or match (setq match 0))
  (let ((case-fold-search t))
    (if (looking-at str)
        (goto-char (match-end match)))))

(defun parsebib--match-paren-forward ()
  "Move forward to the closing paren matching the opening paren at point.
This function handles parentheses () and braces {}. Return t if a
matching parenthesis was found. Note that this function puts
point right before the closing delimiter (unlike e.g.,
`forward-sexp', which puts it right after.)"
  (let ((result (cond
                 ((eq (char-after) ?\{)
                  (parsebib--match-brace-forward))
                 ((eq (char-after) ?\()
                  ;; This is really a hack. We want to allow unbalanced parentheses in
                  ;; field values (BibTeX does), so we cannot use forward-sexp
                  ;; here. For the same reason, looking for the matching paren by hand
                  ;; is pretty complicated. However, balanced parentheses can only be
                  ;; used to enclose entire entries (or @STRINGs or @PREAMBLEs) so we
                  ;; can be pretty sure we'll find it right before the next @ at the
                  ;; start of a line, or right before the end of the file.
                  (let ((beg (point)))
                    (re-search-forward parsebib--entry-start nil 0)
                    (skip-chars-backward "@ \n\t\f")
                    (if (eq (char-after) ?\))
                        ;; if we've found a closing paren, return t
                        t
                      ;; otherwise put the cursor back and signal an error
                      (goto-char beg)
                      (signal 'scan-error (list "Unbalanced parentheses" beg (point-max)))))))))
    (when result
      ;; move point one char back to place it where the rest of parsebib expects it
      (forward-char -1)
      ;; make sure we return t
      result)))

(defun parsebib--match-delim-forward ()
  "Move forward to the closing delimiter matching the delimiter at point.
This function handles braces {} and double quotes \"\". Return t
if a matching delimiter was found. Note that this function puts
point right before the closing delimiter (unlike e.g.,
`forward-sexp', which puts it right after.)"
  (let ((result (cond
                 ((eq (char-after) ?\{)
                  (parsebib--match-brace-forward))
                 ((eq (char-after) ?\")
                  (parsebib--match-quote-forward)))))
    (when result
      ;; move point one char back to place it where the rest of parsebib expects it
      (forward-char -1)
      ;; make sure we return t
      result)))

(defun parsebib--match-brace-forward ()
  "Move forward to the closing brace matching the opening brace at point."
  (with-syntax-table bibtex-braced-string-syntax-table
    (forward-sexp 1)
    ;; if forward-sexp does not result in an error, we want to return t
    t))

(defun parsebib--match-quote-forward ()
  "Move to the closing double quote matching the quote at point."
  (with-syntax-table bibtex-quoted-string-syntax-table
    (forward-sexp 1)
    ;; if forward-sexp does not result in an error, we want to return t
    t))


;;;;;;;;;;;;;;;;;;;;;;;;
;; parsing a bib file ;;
;;;;;;;;;;;;;;;;;;;;;;;;

(defun parsebib-find-bibtex-dialect ()
  "Find the BibTeX dialect of a file if one is set.
This function looks for a local value of the variable
`bibtex-dialect' in the local variable block at the end of the
file. Return nil if no dialect is found."
  (save-excursion
    (goto-char (point-max))
    (let ((case-fold-search t))
      (when (re-search-backward (concat parsebib--entry-start "comment") (- (point-max) 3000) t)
        (let ((comment (parsebib-read-comment)))
          (when (and comment
                     (string-match-p "\\`[ \n\t\r]*Local Variables:" comment)
                     (string-match-p "End:[ \n\t\r]*\\'" comment)
                     (string-match (concat "bibtex-dialect: " (regexp-opt (mapcar #'symbol-name bibtex-dialect-list) t)) comment))
            (intern (match-string 1 comment))))))))

(defun parsebib-find-next-item (&optional pos)
  "Find the first (potential) BibTeX item following POS.

This function simply searches for an @ at the start of a line,
possibly preceded by spaces or tabs, followed by a string of
characters as defined by `parsebib--bibtex-identifier'. When
successful, point is placed right after the item's type, i.e.,
generally on the opening brace or parenthesis following the entry
type, \"@Comment\", \"@Preamble\" or \"@String\".

The return value is the name of the item as a string, either
\"Comment\", \"Preamble\" or \"String\", or the entry
type (without the @). If an item name is found that includes an
illegal character, an error of type `parsebib-entry-type-error'
is raised. If no item is found, nil is returned and point is left
at the end of the buffer.

POS can be a number or a marker and defaults to point."
  (when pos (goto-char pos))
  (when (re-search-forward parsebib--entry-start nil 0) 
    (if (parsebib--looking-at-goto-end (concat "\\(" parsebib--bibtex-identifier "\\)" "[[:space:]]*[\(\{]") 1)
        (match-string 1)
      (signal 'parsebib-entry-type-error (list (point))))))

(defun parsebib-read-comment (&optional pos)
  "Read the @Comment beginning at the line POS is on.
Return value is the text of the @Comment or nil if no comment is
found.

POS can be a number or a marker. It does not have to be at the
beginning of a line, but the @Comment entry must start at the
beginning of the line POS is on. If POS is nil, it defaults to
point."
  (when pos (goto-char pos))
  (beginning-of-line)
  (when (parsebib--looking-at-goto-end (concat parsebib--entry-start "comment[[:space:]]*[\(\{]"))
    (let ((beg (point))) ; we are right after the opening brace / parenthesis
      (forward-char -1)  ; move back to the brace / paren
      (when (parsebib--match-paren-forward)
        (buffer-substring-no-properties beg (point))))))

(defun parsebib-read-string (&optional pos)
  "Read the @String definition beginning at the line POS is on.
If a proper abbreviation and string are found, they are returned
as a cons cell (<abbrev> . <string>). Otherwise, nil is returned.

POS can be a number or a marker. It does not have to be at the
beginning of a line, but the @String entry must start at the
beginning of the line POS is on. If POS is nil, it defaults to
point."
  (when pos (goto-char pos))
  (beginning-of-line)
  (when (parsebib--looking-at-goto-end (concat parsebib--entry-start "string[[:space:]]*[\(\{]"))
    (let ((limit (save-excursion ; find the position of the matching end parenthesis
                   (forward-char -1)
                   (parsebib--match-paren-forward)
                   (point))))
      (skip-chars-forward "\"#%'(),={} \n\t\f" limit) ; move up to the abbrev
      (let* ((beg (point))                            ; read the abbrev
             (abbr (if (parsebib--looking-at-goto-end (concat "\\(" parsebib--bibtex-identifier "\\)[ \t\n\f]*=") 1)
                       (buffer-substring-no-properties beg (point))
                     nil)))
        (when (and abbr (> (length abbr) 0)) ; if we found an abbrev
          (skip-chars-forward "^\"{" limit) ; move forward to the definition
          (let* ((beg (point))              ; read the definition
                 (string (if (parsebib--match-delim-forward)
                             (buffer-substring-no-properties beg (1+ (point))))))
            (and string (> (length string) 0)
                 (cons abbr string))))))))

(defun parsebib-read-preamble (&optional pos)
  "Read the @Preamble definition at the line POS is on.
Return the preamble as a string, or nil if none was found.

POS can be a number or a marker. It does not have to be at the
beginning of a line, but the @Preamble must start at the
beginning of the line POS is on. If POS is nil, it defaults to
point."
  (when pos (goto-char pos))
  (beginning-of-line)
  (when (parsebib--looking-at-goto-end (concat parsebib--entry-start "preamble[[:space:]]*[\(\{]"))
    (let ((beg (point)))
      (forward-char -1)
      (when (parsebib--match-paren-forward)
        (buffer-substring-no-properties beg (point))))))

(defun parsebib-read-entry (type &optional pos)
  "Read a BibTeX entry at the line POS is on.

The entry should be of type TYPE (a string, not containing the @
sign). The return value is the entry as an alist of (<field> .
<contents>) cons pairs, or nil if no entry was found. In this
alist, the entry key is provided in the field \"=key=\" and the
entry type in the field \"=type=\".

POS can be a number or a marker. It does not have to be at the
beginning of a line, but the entry must start at the beginning of
the line POS is on. If POS is nil, it defaults to point.

ENTRY should not be \"Comment\", \"Preamble\" or \"String\", but
is otherwise not limited to any set of possible entry types. If
so required, the calling function has to ensure that the entry
type is valid."
  (unless (member-ignore-case type '("comment" "preamble" "string"))
    (when pos (goto-char pos))
    (beginning-of-line)
    (when (parsebib--looking-at-goto-end (concat parsebib--entry-start type "[[:space:]]*[\(\{]"))
      ;; find the end of the entry and the beginning of the entry key
      (let* ((limit (save-excursion
                      (backward-char)
                      (parsebib--match-paren-forward)
                      (point)))
             (beg (progn
                    (skip-chars-forward " \n\t\f") ; note the space!
                    (point)))
             (key (when (parsebib--looking-at-goto-end (concat "\\(" parsebib--key-regexp "\\)[ \t\n\f]*,") 1)
                    (buffer-substring-no-properties beg (point)))))
        (or key (setq key "")) ; if no key was found, we pretend it's empty and try to read the entry anyway
        (skip-chars-forward "^," limit) ; move to the comma after the entry key
        (let ((fields (cl-loop for field = (parsebib--find-bibtex-field limit)
                               while field collect field)))
          (push (cons "=type=" type) fields)
          (push (cons "=key=" key) fields)
          (nreverse fields))))))

(defun parsebib--find-bibtex-field (limit)
  "Find the field after point.
Return a cons (FIELD . VALUE), or NIL if no field was found."
  (skip-chars-forward "\"#%'(),={} \n\t\f" limit) ; move to the first char of the field name
  (unless (>= (point) limit)   ; if we haven't reached the end of the entry
    (let ((beg (point)))
      (if (parsebib--looking-at-goto-end (concat "\\(" parsebib--bibtex-identifier "\\)[ \t\n\f]*=") 1)
          (let ((field-type (buffer-substring-no-properties beg (point))))
            (skip-chars-forward "#%'()=} \n\t\f" limit) ; move to the field contents
            (let* ((beg (point))
                   (field-contents (buffer-substring-no-properties beg (parsebib--find-end-of-field limit))))
              (cons field-type field-contents)))))))

(defun parsebib--find-end-of-field (limit)
  "Move point to the end of a field's contents and return point.
The contents of a field is delimited by a comma or by the closing brace of
the entry. The latter should be at position LIMIT."
  (while (and (not (eq (char-after) ?\,))
              (< (point) limit))
    (parsebib--match-delim-forward) ; check if we're on a delimiter and if so, jump to the matching closing delimiter
    (forward-char 1))
  (if (= (point) limit)
      (skip-chars-backward " \n\t\f"))
  (point))

(provide 'parsebib)

;;; parsebib.el ends here
