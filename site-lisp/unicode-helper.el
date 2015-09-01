;;; unicode-helper.el --- Unicode helper functions

;; Copyright (C) 2005  Jorgen Schaefer

;; Version: 1.0
;; Author: Jorgen Schaefer <forcer@forcix.cx>
;; URL: http://www.emacswiki.org/cgi-bin/wiki/download/unicode-helper.el

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301  USA

;;; Commentary:

;; This library provides some helper functions to work with Unicode
;; characters.

;;; Code:

(defgroup unicode-helper nil
  "*Unicode helper mode, helper functions for Unicode characters."
  :prefix "unicode-helper-")

(defcustom unicode-helper-data-txt "~/doc/Unicode/UNIDATA/UnicodeData.txt"
  "The Unicode data file. Available at
http://www.unicode.org/Public/UNIDATA/UnicodeData.txt"
  :type 'file
  :group 'unicode-helper)

(defvar unicode-helper-mode-prefix-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "``") (lambda () (interactive)
                                 (unicode-helper-do-insert-codepoint 8220)))
    (define-key map (kbd "''") (lambda () (interactive)
                                 (unicode-helper-do-insert-codepoint 8221)))
    (define-key map (kbd ",,") (lambda () (interactive)
                                 (unicode-helper-do-insert-codepoint 8222)))
    (define-key map (kbd ">>") (lambda () (interactive)
                                 (unicode-helper-do-insert-codepoint 187)))
    (define-key map (kbd "<<") (lambda () (interactive)
                                 (unicode-helper-do-insert-codepoint 171)))
    (define-key map (kbd "...") (lambda () (interactive)
                                  (unicode-helper-do-insert-codepoint 8230)))
    (define-key map (kbd "---") (lambda () (interactive)
                                  (unicode-helper-do-insert-codepoint 8212)))
    (define-key map (kbd "- - SPC") (lambda () (interactive)
                                      (unicode-helper-do-insert-codepoint 8211)
                                      (insert " ")))
    map)
  "The keymap used with the prefix key.")

(defvar unicode-helper-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-p") unicode-helper-mode-prefix-map)
    (define-key map (kbd "C-c C-p RET") 'unicode-helper-name-at-point)
    (define-key map (kbd "C-c C-p =") 'unicode-helper-name-at-point)
    (define-key map (kbd "C-c C-p C-c") 'unicode-helper-insert-codepoint)
    (define-key map (kbd "C-c C-p C-n") 'unicode-helper-insert-char-name)
    map)
  "The keymap used for fast-access to unicode characters.")

(define-minor-mode unicode-helper-mode
  "Helper functions for Unicode characters.
Runs the hook `unicode-helper-mode-hook' when activated.

\\{unicode-helper-mode-map}"
  :group 'unicode-helper
  :global t)

(defun unicode-helper-name-at-point ()
  "Display the Unicode name of the character at point."
  (interactive)
  (let* ((unicode (encode-char (char-after (point))
                               'ucs))
         (codepoint (if unicode
                        (format "%04X" unicode)
                      (error "Not a Unicode character"))))
    (with-current-buffer (find-file-noselect unicode-helper-data-txt)
      (goto-char (point-min))
      (if (re-search-forward (concat "^" codepoint ";\\([^;]*\\);")
                             nil t)
          (message "Codepoint %s: %s" codepoint (match-string 1))
        (message "Unknown character number %s" codepoint)))))

(defun unicode-helper-insert-codepoint ()
  "Insert an Unicode character identified by a codepoint."
  (interactive)
  (let ((char (read-char "Unicode character codepoint: "))
        (codepoint 0))
    (while (unicode-helper-hex-digit-p char)
      (setq codepoint (+ (unicode-helper-hex-digit-value char)
                         (* 16 codepoint))
            char (read-char (format "Unicode character codepoint: %x"
                                    codepoint))))
    (unicode-helper-do-insert-codepoint codepoint)))

(defun unicode-helper-insert-char-name ()
  "Insert an Unicode character identified by a name."
  (interactive)
  (unicode-helper-do-insert-codepoint
   (cdr (assoc (completing-read "Unicode character: "
                                (unicode-helper-names))
               (unicode-helper-names)))))

(defvar unicode-helper-names nil
  "The list of Unicode names.
Use the `unicode-helper-names' function to access this.")

(defun unicode-helper-names ()
  "Return a list of Unicode characters.
The list consists of (name . codepoint) pairs."
  (or unicode-helper-names
      (with-current-buffer (find-file-noselect unicode-helper-data-txt)
        (goto-char (point-min))
        (while (re-search-forward "^\\([0-9A-F]*\\);\\([^;]*\\);" nil t)
          (setq unicode-helper-names (cons
                                      (cons (match-string 2)
                                            (string-to-number (match-string 1)
                                                              16))
                                      unicode-helper-names)))
        (setq unicode-helper-names (nreverse unicode-helper-names))
        unicode-helper-names)))

(defun unicode-helper-do-insert-codepoint (codepoint)
  "Insert a Unicode codepoint as a character."
  (let ((char (decode-char 'ucs codepoint)))
    (if char
        (insert char)
      (error "Can't encode codepoint %x as Unicode" codepoint))))

(defun unicode-helper-hex-digit-p (char)
  "Return non-nil if CHAR is a hex digit."
  (or (and (<= ?0 char)
           (<= char ?9))
      (and (<= ?a char)
           (<= char ?f))
      (and (<= ?A char)
           (<= char ?F))))

(defun unicode-helper-hex-digit-value (char)
  "Return the value of the hex digit CHAR."
  (cond
   ((and (<= ?0 char)
         (<= char ?9))
    (- char ?0))
   ((and (<= ?a char)
         (<= char ?f))
    (+ 10 (- char ?a)))
   ((and (<= ?A char)
         (<= char ?F))
    (+ 10 (- char ?A)))))

(provide 'unicode-helper)
;;; unicode-helper.el ends here
