;;; auto-complete-pycomplete.el --- an auto-complete source for pycomplete.el

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

;; The ac-source can be enabled solely using
;; (setq ac-sources '(ac-source-pycomplete))
;; or before the other sources using
;; (add-to-list 'ac-sources 'ac-source-pycomplete).

;;; Code:

(require 'pycomplete)
(require 'auto-complete)

(defun ac-pycomplete-document (symbol)
  (let* ((full-prefix (py-complete-enhanced-symbol-before-point))
        (full-symbol (concat (substring full-prefix 0 (- (length ac-prefix))) symbol)))
    (py-complete-docstring-for-symbol full-symbol)))

(defun ac-pycomplete-candidates ()
  (py-complete-completions-for-symbol
   (py-complete-enhanced-symbol-before-point)))

(ac-define-source pycomplete
  '((candidates . ac-pycomplete-candidates)
    (document . ac-pycomplete-document)))

(provide 'auto-complete-pycomplete)
;;; auto-complete-pycomplete.el ends here
