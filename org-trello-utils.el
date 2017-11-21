;;; org-trello-utils.el --- Utilities namespace

;; Copyright (C) 2015-2017  Antoine R. Dumont (@ardumont) <antoine.romain.dumont@gmail.com>

;; Author: Antoine R. Dumont (@ardumont) <antoine.romain.dumont@gmail.com>
;; Keywords:

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
;;; Code:

(require 'dash)
(require 's)

(defun orgtrello-utils-replace-in-string (expression-to-replace replacement-expression string-input)
  "Given an EXPRESSION-TO-REPLACE and a REPLACEMENT-EXPRESSION, replace such in STRING-INPUT."
  (replace-regexp-in-string expression-to-replace replacement-expression string-input 'fixed-case))

(defun orgtrello-utils-symbol (sym n)
  "Compute the repetition of a symbol SYM N times as a string."
  (--> n
    (-repeat it sym)
    (s-join "" it)))

(defun orgtrello-utils-space (n)
  "Given a level, compute N times the number of spaces for an org checkbox entry."
  (orgtrello-utils-symbol " "  n))

(provide 'org-trello-utils)
;;; org-trello-utils.el ends here
