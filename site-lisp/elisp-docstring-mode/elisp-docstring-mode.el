;;; elisp-docstring-mode.el --- Major mode for editing elisp docstrings.

;; Copyright (C) 2017 Matúš Goljer

;; Author: Matúš Goljer <matus.goljer@gmail.com>
;; Maintainer: Matúš Goljer <matus.goljer@gmail.com>
;; Version: 0.0.1
;; Created:  4th March 2017
;; Package-requires: ()
;; Keywords: languages

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(defun elisp-docstring-mode--find-variable (limit)
  "Find an occurrence of a variable name.
Search up to LIMIT."
  (and (re-search-forward "\\_<[A-Z]+\\_>" limit)
       (not (nth 3 (syntax-ppss)))))

(defvar elisp-docstring-mode-font-lock-keywords
  '(
    ;; Words inside \[] tend to be for `substitute-command-keys'.
    ("\\\\\\[\\(\\(?:\\sw\\|\\s_\\)+\\)\\]" 0 font-lock-keyword-face prepend)
    ;; Words inside `' tend to be symbol names.
    ("`\\(\\(?:\\sw\\|\\s_\\)\\(?:\\sw\\|\\s_\\)+\\)'" 0 font-lock-constant-face prepend)
    ;; there are some false-positives, but for now this is good enough
    (elisp-docstring-mode--find-variable 0 font-lock-variable-name-face prepend))
   "Keywords for `font-lock-mode'.")

;;;###autoload
(define-derived-mode elisp-docstring-mode text-mode
  "Elisp docstring mode"
  "Major mode for editing Emacs Lisp docstrings."
  (set (make-local-variable 'font-lock-defaults)
       '((elisp-docstring-keywords elisp-docstring-mode-font-lock-keywords)))
  (modify-syntax-entry ?\" "\""))

(provide 'elisp-docstring-mode)
;;; elisp-docstring-mode.el ends here
