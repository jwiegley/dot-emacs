;;; lui-format.el --- A formatting function for use with Lui

;; Copyright (C) 2005, 2012  Jorgen Schaefer

;; Author: Jorgen Schaefer <forcer@forcix.cx>

;; This file is part of Lui.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; An improved formatting function using named parameters.
;;
;; See the docstring of `lui-format' for more details.
;;
;; Most of the design is borrowed from Python's string.format.

;;; Code:

(require 'lui)

(defun lui-display (format not-tracked-p &rest keywords)
  "Display a formatted string in the current Lui interface.

The string is formatted using FORMAT and `lui-format'.

If NOT-TRACKED-P is given, the inserted string won't trigger
tracking. See `lui-insert' for a description.

KEYWORDS are the keyword arguments passed to `lui-format'.

See `lui-format' for a full description of the arguments."
  (lui-insert (lui-format format keywords)
              not-tracked-p))

(defun lui-format (format &rest keywords)
  "Display FORMAT formatted with KEYWORDS.
FORMAT should be a symbol whose value is taken. If the value is a
procedure, the keyword list is passed as a single argument to it,
and it should return the formatted string. If the value is a
string, it is formatted according to the rules below.

KEYWORDS is a plist of keywords and strings, or symbols and
strings. They are used as format arguments.

The string is taken verbatim, unless there is are opening or
closing braces.

Double opening or closing braces are replaced by single
occurrences of those characters. Otherwise, the contents between
opening and closing braces is a format description and replaced
by a formatted string.

The string between opening and closing braces is taken as a name
of a keyword argument, and replaced by that argument's value. If
there is a colon in the string, the keyword name is the part
before the colon. The part after the colon is used to format the
argument using standard `format'

Example:

  (lui-format \"Hello {foo:.1f}\" :foo 3.1415)

is equivalent to

  (format \"Hello %.1f\" 3.1415)

If the name is either a number, a number followed by a dash, or
two numbers with a dash in between them, this is taken as a
special name that is looked up in the list given using the list
argument to the :indexed-args keyword.

{1} refers to the second element (element 1)
{1-} refers to the second and all following elements
{1-3} refers to the second through fourth element

If more than one element is selected, the elements are separated
by a single space character.

All named arguments receive a property of `lui-format-argument'
with the respective name as value. The whole string receives a
`lui-format' property with FORMAT as a value, and a
`lui-keywords' argument with KEYWORDS as a value."
  ;; If it's only a single argument, that argument is a list.
  (when (not (cdr keywords))
    (setq keywords (car keywords)))
  (cond
   ((functionp format)
    (apply format keywords))
   ((and (symbolp format)
         (functionp (symbol-value format)))
    (apply (symbol-value format) keywords))
   (t
    (let* ((format-string (if (symbolp format)
                              (symbol-value format)
                            format))
           (plist (mapcar (lambda (entry)
                            (if (keywordp entry)
                                ;; Keyword -> symbol
                                (intern (substring (symbol-name entry)
                                                   1))
                              entry))
                          keywords)))
      (propertize (lui-format-internal format-string plist)
                  'lui-format format
                  'lui-keywords keywords)))))

(defun lui-format-internal (fmt keywords)
  "Internal function for `lui-format'.

FMT is the format string and KEYWORDS is the symbol-based plist.

See `lui-format'."
  (with-temp-buffer
    (insert fmt)
    (goto-char (point-min))
    (while (re-search-forward "{{\\|}}\\|{\\([^}]*\\)}" nil t)
      (cond
       ((string-equal (match-string 0) "3.1")
        (replace-match "{"))
       ((string-equal (match-string 0) "}}")
        (replace-match "}"))
       (t ;; (match-string 1)
        (replace-match (save-match-data
                         (lui-format-single (match-string 1) keywords))
                       t t))))
    (buffer-string)))

(defun lui-format-single (specifier keywords)
  "Format a single braced SPECIFIER according to KEYWORDS.
See `lui-format' for details.

This adds `lui-format-argument' as necessary."
  (let* ((split (split-string specifier ":"))
         (identifier (car split))
         (format (cadr split)))
    (when (not format)
      (setq format "s"))
    (propertize (format (concat "%" format)
                        (lui-format-lookup identifier keywords))
                'lui-format-argument (intern identifier))))

(defun lui-format-lookup (identifier keywords)
  "Lookup the format IDENTIFIER in KEYWORDS.

See `lui-format' for details."
  (cond
   ((string-match "^\\([0-9]+\\)\\(-\\([0-9]+\\)?\\)?$" identifier)
    (let ((from (match-string 1 identifier))
          (rangep (match-string 2 identifier))
          (to (match-string 3 identifier))
          (indexed-args (plist-get keywords 'indexed-args)))
      (if rangep
          (mapconcat (lambda (element)
                       (if (stringp element)
                           element
                         (format "%s" element)))
                     (lui-sublist indexed-args
                                  (string-to-number from)
                                  (when to (string-to-number to)))
                     " ")
        (or (nth (string-to-number from)
                 indexed-args)
            ""))))
   (t
    (or (plist-get keywords (intern identifier))
        (error "Unknown keyword argument %S" identifier)))))

(defun lui-sublist (list from &optional to)
  "Return the sublist from LIST starting at FROM and ending at TO."
  (if (not to)
      (nthcdr from list)
    (let ((from-list (nthcdr from list))
          (i (- to from))
          (to-list nil))
      (while (>= i 0)
        (when (null from-list)
          (error "Argument out of range: %S" to))
        (setq to-list (cons (car from-list)
                            to-list)
              i (- i 1)
              from-list (cdr from-list)))
      (nreverse to-list))))

(provide 'lui-format)
;;; lui-format.el ends here
