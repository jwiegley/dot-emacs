;;; org-trello-input.el --- User input related functions.

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

(require 'org-trello-log)
(require 'ido)
(require 's)

(defalias 'orgtrello-input-read-string 'read-string
  "Read input from user which can be null.
:: () -> String")

(defalias 'orgtrello-input-confirm 'y-or-n-p
  "Yes or no question.
:: () -> String")

(defun orgtrello-input-read-not-empty (prompt)
  "Read input as long as input is empty.
PROMPT is the prefix string displayed for input.
:: () -> String"
  (let ((value nil))
    (while (or (null value) (string= "" value))
      (setq value (-> (orgtrello-input-read-string prompt) s-trim)))
    value))

(defun orgtrello-input-read-string-completion (prompt choices)
  "Read input from user with completing mechanism.
PROMPT is the prompt for user to see.
CHOICES is the list of possibilities with completing properties.
:: String -> [a] -> a"
  (if (eq 'default org-trello-input-completion-mechanism)
      (ido-completing-read prompt choices nil 'do-match)
    (progn ;; Beware, the user needs to install helm first as this is
           ;; not a runtime dependency on org-trello itself
      (require 'helm)
      (helm-comp-read prompt choices))))

(provide 'org-trello-input)
;;; org-trello-input.el ends here
