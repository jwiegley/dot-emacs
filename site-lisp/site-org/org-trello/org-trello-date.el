;;; org-trello-date.el --- Date manipulation for org-trello-buffer

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

(defun orgtrello-date-convert-org-date-to-trello-date (org-date)
  "Convert the ORG-DATE deadline into a trello one."
  (if org-date
      (--> (org-parse-time-string org-date)
           (apply 'encode-time it)
           (format-time-string "%Y-%m-%dT%H:%M:%S.%3NZ" it t))
    org-date))

(defconst orgtrello-date-iso-8601-date-pattern
  "[0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\}T[0-9]\\{2\\}:[0-9]\\{2\\}:[0-9]\\{2\\}\.[0-9]\\{3\\}.*"
  "ISO-8601 date pattern trello sends.")

(defun orgtrello-date--prepare-iso-8601 (iso-8601-date)
  "Convert ISO-8601-DATE into something `parse-time-string' can parse."
  (when (string-match orgtrello-date-iso-8601-date-pattern iso-8601-date)
    (->> iso-8601-date
         (replace-regexp-in-string "T" " ")
         (replace-regexp-in-string ".000Z" " GMT"))))

(defun orgtrello-date-convert-trello-date-to-org-date (trello-date)
  "Convert the TRELLO-DATE into an `org-mode' one."
  (if trello-date
      (--> (orgtrello-date--prepare-iso-8601 trello-date)
           (parse-time-string it)
           (apply 'encode-time it)
           (format-time-string "%Y-%m-%d %a %H:%M" it))
    trello-date))

(provide 'org-trello-date)
;;; org-trello-date.el ends here
