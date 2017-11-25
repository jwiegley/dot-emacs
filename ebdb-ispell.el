;;; ebdb-ispell.el --- Add EBDB contact names to personal dictionaries  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Free Software Foundation, Inc.

;; Author: Eric Abrahamsen <eric@ericabrahamsen.net>

;; This program is free software; you can redistribute it and/or modify
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

;; Copied from bbdb-ispell.el, originally written by Ivan Kanis.

;;; Code:

(require 'ispell)
(require 'ebdb)

(defcustom ebdb-ispell-min-word-length 2
  "Words with fewer characters are ignored."
  :group 'ebdb-utilities-ispell
  :type 'number)

(defcustom ebdb-ispell-ignore-re "[^[:alpha:]]"
  "Words matching this regexp are ignored."
  :group 'ebdb-utilities-ispell
  :type 'regexp)

;;;###autoload
(defun ebdb-ispell-export ()
  "Export EBDB records to ispell personal dictionaries."
  (interactive)
  (message "Exporting 0 words to personal dictionary...")
  ;; Collect words from EBDB records.
  (let ((word-list
	 (seq-mapcat
	  (lambda (r)
	    (ebdb-ispell-collect-words
	     (cons (ebdb-record-name r)
		   (ebdb-record-alt-names r))))
	  (ebdb-records)))
	(count 0))

    ;; Initialize variables and dicts alists
    (ispell-set-spellchecker-params)
    (ispell-init-process)
    ;; put in verbose mode
    (ispell-send-string "%\n")
    (let (new)
      (dolist (word (delete-dups word-list))
        (ispell-send-string (concat "^" word "\n"))
        (while (progn
                 (ispell-accept-output)
                 (not (string= "" (car ispell-filter)))))
        ;; remove extra \n
        (setq ispell-filter (cdr ispell-filter))
        (when (and ispell-filter
                   (listp ispell-filter)
                   (not (eq (ispell-parse-output (car ispell-filter)) t)))
          ;; ok the word doesn't exist, add it
          (ispell-send-string (concat "*" word "\n"))
	  (message "Exporting %d words to personal dictionary..."
		   (cl-incf count))
          (setq new t)))
      (when new
        ;; Save dictionary:
        ;; aspell doesn't tell us when it completed the saving.
        ;; So we send it another word for spellchecking.
        (ispell-send-string "#\n^hello\n")
        (while (progn
                 (ispell-accept-output)
                 (not (string= "" (car ispell-filter)))))))
    (message "Exporting %d words to personal dictionary...done" count)))

(defun ebdb-ispell-collect-words (strings)
  "Find all individual words in STRINGS and filter.
Removes strings that are too short
\(`ebdb-ispell-min-word-length'\) or explicitly ignored
\(`ebdb-ispell-ignore-re'\)."
  (seq-filter
   (lambda (word)
     (and (>= (length word) ebdb-ispell-min-word-length)
          (not (string-match ebdb-ispell-ignore-re word))))
   (seq-mapcat
    (lambda (s)
      (split-string s "[ ,]"))
    strings)))

(provide 'ebdb-ispell)
;;; ebdb-ispell.el ends here
