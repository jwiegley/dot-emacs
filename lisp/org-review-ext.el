;;; org-review-ext --- Extra functions for use with Org-review -*- lexical-binding: t -*-

;; Copyright (C) 2026 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 23 Apr 2026
;; Version: 1.0
;; Keywords: org capture task todo context
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;;; Code:

(require 'cl-lib)
(eval-when-compile
  (require 'cl)
  (require 'cl-macs))

(require 'org)
(require 'org-review)

(defun org-review-ext-increment-count (&rest _)
  (interactive)
  (let* ((where (if (equal major-mode 'org-agenda-mode)
                    (or (org-get-at-bol 'org-marker)
	                (org-agenda-error))
                  (point)))
         (reviews (org-entry-get where "REVIEWS")))
    (if reviews
        (org-entry-put where "REVIEWS"
                       (number-to-string
                        (1+ (string-to-number reviews))))
      (org-entry-put where "REVIEWS" "1"))))

(defun org-remove-ext-review (&optional all)
  (org-entry-delete (point) "NEXT_REVIEW")
  (when all
    (org-entry-delete (point) "REVIEWS")
    (org-entry-delete (point) "LAST_REVIEW")
    (org-schedule '(4))
    (org-deadline '(4))))

(defun org-review-ext-reviewed-today ()
  (interactive)
  (let ((todo-state (ignore-errors (org-get-todo-state))))
    (cond ((or (null todo-state)
               (member todo-state '("NOTE" "QUOTE" "PROMPT" "LINK")))
           (org-remove-ext-review t))
          ((member todo-state '("DONE" "CANCELED" "PASS")))
          ((or todo-state
               (save-excursion
                 (goto-char (point-min))
                 (looking-at "^\\(DRAFT\\|TODO\\|TASK\\|HABIT\\|APPT\\) ")))
           (save-excursion
             (org-review-insert-last-review)
             (org-review-insert-date
              org-review-next-property-name
	      org-review-next-timestamp-format
	      (format-time-string (car org-time-stamp-formats)
                                  (current-time))))))))

(defun org-review-ext-insert-last-and-set-next-review ()
  (interactive)
  (org-review-insert-last-review)
  (call-interactively #'org-review-insert-next-review))

(defun org-review-ext-next (delay)
  (let ((org-review-delay delay))
    (org-review-insert-last-review nil)))

(defun org-review-ext-next-day ()
  (interactive)
  (org-review-ext-next "+1d")
  (message "Next review in 1 day"))
(defun org-review-ext-next-two-days ()
  (interactive)
  (org-review-ext-next "+2d")
  (message "Next review in 2 days"))
(defun org-review-ext-next-three-days ()
  (interactive)
  (org-review-ext-next "+3d")
  (message "Next review in 3 days"))
(defun org-review-ext-next-four-days ()
  (interactive)
  (org-review-ext-next "+4d")
  (message "Next review in 4 days"))
(defun org-review-ext-next-five-days ()
  (interactive)
  (org-review-ext-next "+5d")
  (message "Next review in 5 days"))
(defun org-review-ext-next-six-days ()
  (interactive)
  (org-review-ext-next "+6d")
  (message "Next review in 6 days"))
(defun org-review-ext-next-week ()
  (interactive)
  (org-review-ext-next "+1w")
  (message "Next review in 1 week"))
(defun org-review-ext-next-two-weeks ()
  (interactive)
  (org-review-ext-next "+2w")
  (message "Next review in 2 weeks"))
(defun org-review-ext-next-three-weeks ()
  (interactive)
  (org-review-ext-next "+3w")
  (message "Next review in 3 weeks"))
(defun org-review-ext-next-four-weeks ()
  (interactive)
  (org-review-ext-next "+4w")
  (message "Next review in 4 weeks"))
(defun org-review-ext-next-five-weeks ()
  (interactive)
  (org-review-ext-next "+5w")
  (message "Next review in 5 weeks"))
(defun org-review-ext-next-six-weeks ()
  (interactive)
  (org-review-ext-next "+6w")
  (message "Next review in 6 weeks"))
(defun org-review-ext-next-month ()
  (interactive)
  (org-review-ext-next "+1m")
  (message "Next review in 1 month"))
(defun org-review-ext-next-two-months ()
  (interactive)
  (org-review-ext-next "+2m")
  (message "Next review in 2 months"))
(defun org-review-ext-next-quarter ()
  (interactive)
  (org-review-ext-next "+3m")
  (message "Next review in 3 months"))
(defun org-review-ext-next-half-year ()
  (interactive)
  (org-review-ext-next "+6m")
  (message "Next review in 6 months"))
(defun org-review-ext-next-year ()
  (interactive)
  (org-review-ext-next "+1y")
  (message "Next review in 1 year"))
(defun org-review-ext-next-two-years ()
  (interactive)
  (org-review-ext-next "+2y")
  (message "Next review in 2 years"))

(provide 'org-review-ext)

;;; org-review-ext.el ends here
