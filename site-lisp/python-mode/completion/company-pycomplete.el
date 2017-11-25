;;; company-pycomplete.el --- a company-mode completion back-end for pycomplete.el

;; Copyright (C) 2012  Urs Fleisch

;; Author: Urs Fleisch <ufleisch@users.sourceforge.net>
;; Keywords: languages, processes, python, oop

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

;; The backend can be enabled using
;; (setq company-backends '((company-pycomplete)))

;;; Code:

(require 'pycomplete)
(require 'company)

(defun company-pycomplete--grab-symbol ()
  ;; stolen from company-pysmell--grab-symbol
  (let ((symbol (company-grab-symbol)))
    (when symbol
      (cons symbol
            (save-excursion
              (let ((pos (point)))
                (goto-char (- (point) (length symbol)))
                (while (eq (char-before) ?.)
                  (goto-char (1- (point)))
                  (skip-syntax-backward "w_"))
                (- pos (point))))))))


(defun company-pycomplete-doc-buffer (candidate)
  "Return buffer with docstring of CANDIDATE if it is available."
  (let* ((full-prefix (py-complete-enhanced-symbol-before-point))
         (full-symbol (concat full-prefix (company-strip-prefix candidate)))
         (doc (py-complete-docstring-for-symbol full-symbol)))
    (when (and (stringp doc) (> (length doc) 0))
      (with-current-buffer (company-doc-buffer)
        (insert doc)
        (current-buffer)))))

(defun company-pycomplete-location (candidate)
  "Return location of CANDIDATE in cons form (FILE . LINE) if it is available."
  (let* ((full-prefix (py-complete-enhanced-symbol-before-point))
         (full-symbol (concat full-prefix (company-strip-prefix candidate))))
    (py-complete-location full-symbol)))

(defun company-pycomplete (command &optional arg &rest ignored)
  "A `company-mode' completion back-end for pycomplete."
  (interactive (list 'interactive))
  (case command
    ('interactive (company-begin-backend 'company-pycomplete))
    ('prefix (and (derived-mode-p 'python-mode)
                  (not (company-in-string-or-comment))
                  (company-pycomplete--grab-symbol)))
    ('candidates (py-complete-completions))
    ('doc-buffer (company-pycomplete-doc-buffer arg))
    ('location (company-pycomplete-location arg))))

(provide 'company-pycomplete)
;;; company-pycomplete.el ends here
