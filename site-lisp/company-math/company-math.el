;;; company-math.el --- Completion backends for unicode math symbols and latex tags
;;
;; Copyright (C) 2015 Free Software Foundation, Inc.
;; Author: Vitalie Spinu
;; URL: https://github.com/vspinu/company-math
;; Keywords:  Unicode, symbols, completion
;; Version: 1.2
;; Package-Requires: ((company "0.8.0") (math-symbol-lists "1.2"))
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This file is part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'math-symbol-lists)
(require 'company)
(require 'cl-lib)

(defgroup company-math nil
  "Completion back-ends for math symbols Unicode symbols and LaTeX tags."
  :group 'company
  :prefix "company-math-")

(defcustom company-math-symbol-prefix "\\"
  "Prefix to use for latex and unicode symbols."
  :group 'company-math
  :type 'string)

(defcustom company-math-subscript-prefix "_"
  "Prefix to use for unicode subscripts.
It will also work after `company-math-symbol-prefix'."
  :group 'company-math
  :type 'string)

(defcustom company-math-superscript-prefix "^"
  "Prefix to use for unicode subscripts.
It will also work after `company-math-symbol-prefix'."
  :group 'company-math
  :type 'string)

;; no more custom since since v.1.2
(when (boundp 'company-math-prefix-regexp)
  (warn "`company-math-prefix-regexp' is deprecated, please remove from your custom settings."))

(defvar company-math--latex-prefix-regexp (concat (regexp-quote company-math-symbol-prefix)
                                                  "[^ \t\n]+"))
(let ((psym (regexp-quote company-math-symbol-prefix))
      (psub (regexp-quote company-math-subscript-prefix))
      (psup (regexp-quote company-math-superscript-prefix)))
  (defvar company-math--unicode-prefix-regexp (concat "\\(" psym "\\|" psub "\\|" psup "\\)[^ \t\n]*")))

(defcustom company-math-allow-unicode-symbols-in-faces t
  "List of faces to allow the insertion of Unicode symbols.
When set to special value t, allow on all faces except those in
`company-math-disallow-unicode-symbols-in-faces'."
  :group 'company-math
  :type '(choice (const t)
                 (repeat :tag "Faces" symbol)))

(defcustom company-math-allow-latex-symbols-in-faces '(tex-math font-latex-math-face)
  "List of faces to disallow the insertion of latex mathematical symbols.
When set to special value t, allow on all faces except those in
`company-math-disallow-latex-symbols-in-faces'."
  :group 'company-math
  :type '(choice (const t)
                 (repeat :tag "Faces" symbol)))

(defcustom company-math-disallow-unicode-symbols-in-faces '(font-latex-math-face)
  "List of faces to disallow the insertion of Unicode symbols."
  :group 'company-math
  :type '(repeat symbol))

(defcustom company-math-disallow-latex-symbols-in-faces '()
  "List of faces to disallow the insertion of latex mathematical symbols."
  :group 'company-math
  :type '(repeat symbol))


;;; INTERNALS

(defun company-math--make-candidates (alist prefix)
  "Build a list of math symbols ready to be used in ac source.
ALIST is one of the defined alist in package `symbols'. Return a
list of LaTeX symbols with text property :symbol being the
corresponding unicode symbol."
  (delq nil
        (mapcar
         (lambda (el)
           (let* ((tex (concat prefix (substring (nth 1 el) 1)))
                  (ch (and (nth 2 el) (decode-char 'ucs (nth 2 el))))
                  (symb (and ch (char-to-string ch))))
             (propertize tex :symbol symb)))
         alist)))

(defconst company-math--latex-commands
  (mapcar (lambda (c) (concat company-math-symbol-prefix c)) math-symbol-list-latex-commands)
  "List of LaTeX math completion candidates.")

(defconst company-math--symbols
  (delete-dups
   (append (company-math--make-candidates math-symbol-list-basic company-math-symbol-prefix)
           (company-math--make-candidates math-symbol-list-extended company-math-symbol-prefix)))
  "List of LaTeX math completion candidates.")

(defconst company-math--unicode
  (append
   (append (company-math--make-candidates math-symbol-list-subscripts company-math-subscript-prefix)
           (company-math--make-candidates math-symbol-list-subscripts (concat company-math-symbol-prefix
                                                                              company-math-subscript-prefix))
           (company-math--make-candidates math-symbol-list-superscripts company-math-superscript-prefix)
           (company-math--make-candidates math-symbol-list-superscripts (concat company-math-symbol-prefix
                                                                                company-math-superscript-prefix)))
   company-math--symbols)
  "List of math completion candidates for unicode backend.")

(defun company-math--prefix (regexp allow-faces disallow-faces)
  (let* ((face (get-text-property (point) 'face))
         (face (or (car-safe face) face))
         (insertp (and (not (memq face disallow-faces))
                       (or (eq t allow-faces)
                           (memq face allow-faces)))))
    (when insertp
      (save-excursion
        (when (looking-back regexp (point-at-bol) 'greedy)
          (match-string 0))))))

(defun company-math--substitute-unicode (symbol)
  "Substitute preceding latex command with with SYMBOL."
  (let ((pos (point))
        (inhibit-point-motion-hooks t))
    (when (re-search-backward company-math--unicode-prefix-regexp) ; should always match
      (goto-char (match-beginning 0))
      ;; allow subsups to start with \
      (let ((start (max (point-min) (- (point) (length company-math-symbol-prefix)))))
        (when (string= (buffer-substring-no-properties start (point))
                       company-math-symbol-prefix)
          (goto-char start)))
      (delete-region (point) pos)
      (insert symbol))))


;;; BACKENDS

;;;###autoload
(defun company-latex-commands (command &optional arg &rest ignored)
  "Company backend for latex commands."
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-latex-commands))
    (prefix (unless (company-in-string-or-comment)
              (company-math--prefix company-math--latex-prefix-regexp t '())))
    (candidates (all-completions arg company-math--latex-commands))
    (sorted t)))

;;;###autoload
(defun company-math-symbols-latex (command &optional arg &rest ignored)
  "Company backend for LaTeX mathematical symbols."
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-math-symbols-latex))
    (prefix (unless (company-in-string-or-comment)
              (company-math--prefix company-math--latex-prefix-regexp
                                    company-math-allow-latex-symbols-in-faces
                                    company-math-disallow-latex-symbols-in-faces)))
    (annotation (concat " " (get-text-property 0 :symbol arg)))
    (candidates (all-completions arg company-math--symbols))))

;;;###autoload
(defun company-math-symbols-unicode (command &optional arg &rest ignored)
  "Company backend for insertion of Unicode mathematical symbols.
See the unicode-math page [1] for a list of fonts that have a
good support for mathematical symbols. Unicode provides only a
limited range of sub(super)scripts; see the wikipedia page [2]
for details.

 [1] http://ftp.snt.utwente.nl/pub/software/tex/help/Catalogue/entries/unicode-math.html
 [2] https://en.wikipedia.org/wiki/Unicode_subscripts_and_superscripts
"
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-math-symbols-unicode))
    (prefix (company-math--prefix company-math--unicode-prefix-regexp
                                  company-math-allow-unicode-symbols-in-faces
                                  company-math-disallow-unicode-symbols-in-faces))
    (annotation (concat " " (get-text-property 0 :symbol arg)))
    ;; Space added to ensure that completions are never typed in full.
    ;; See https://github.com/company-mode/company-mode/issues/476
    (candidates (delq nil
                      (mapcar (lambda (candidate)
                                (when (get-text-property 0 :symbol candidate)
                                  (concat candidate " ")))
                              (all-completions arg company-math--unicode))))
    (post-completion (company-math--substitute-unicode
                      (get-text-property 0 :symbol arg)))))

(provide 'company-math)
;;; company-math.el ends here
