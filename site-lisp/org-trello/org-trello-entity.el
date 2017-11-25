;;; org-trello-entity.el --- Predicates to determine if we are currently on a card/checklist/item + some default movments

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

(require 'org-trello-setup)
(require 'org-trello-utils)
(require 'org-element)
(require 's)

(defun orgtrello-entity-org-checkbox-p ()
  "Is there a checkbox at current point?"
  (and
   (org-at-item-checkbox-p)
   (save-excursion
     (beginning-of-line)
     (goto-char (+ (org-get-indentation) (point)))
     (org-at-item-bullet-p))))

(defun orgtrello-entity-org-heading-with-level-p (level)
  "Determine if we are currently on an entity with LEVEL."
  (let* ((elem-at-point (org-element-at-point))
         (elem-nature   (car elem-at-point)))
    (and (eq 'headline elem-nature)
         (= level (org-element-property :level elem-at-point)))))

(defun orgtrello-entity-org-card-p ()
  "Determine if we are currently on a card's first line."
  (orgtrello-entity-org-heading-with-level-p org-trello--card-level))

(defun orgtrello-entity--org-checkbox-p (indent)
  "Determine if current position is a checkbox.
Provided INDENT as the denominator for the checkbox's nature."
  (-when-let (s (buffer-substring-no-properties (point-at-bol) (point-at-eol)))
    (string-match-p
     (format "^%s%s" (orgtrello-utils-space indent) "- \\\[.?\\\].*") s)))

(defun orgtrello-entity-org-checklist-p ()
  "Given the current position, determine if we are on a checklist."
  (orgtrello-entity--org-checkbox-p org-trello--checklist-indent))

(defun orgtrello-entity-org-item-p ()
  "Given the current position, determine if we are on an item."
  (orgtrello-entity--org-checkbox-p org-trello--item-indent))

(defalias 'orgtrello-entity-back-to-card 'org-back-to-heading)

(defun orgtrello-entity-org-comment-p ()
  "Given the current position, determine if we are currently on a comment."
  (or
   (save-excursion
     (orgtrello-entity-back-to-card)
     (orgtrello-entity-org-heading-with-level-p 2))
   (->> (buffer-substring (point-at-bol) (point-at-eol))
        s-trim-left
        (s-starts-with? "** COMMENT "))))

(defun orgtrello-entity-card-start-point ()
  "Compute the begin point of a card."
  (save-excursion
    (orgtrello-entity-back-to-card)
    (org-element-property :begin (org-element-at-point))))

(defun orgtrello-entity-level ()
  "Compute the level from the actual position's beginning of line."
  (save-excursion
    (beginning-of-line)
    (cond ((orgtrello-entity-org-card-p)      org-trello--card-level)
          ((orgtrello-entity-org-checklist-p) org-trello--checklist-level)
          ((orgtrello-entity-org-item-p)      org-trello--item-level)
          ((orgtrello-entity-org-comment-p)   org-trello--comment-level)
          (t                                  -1))))

(defun orgtrello-entity-goto-next-checkbox ()
  "Go to the next checkbox.
Does not preserve the current position.
If hitting a heading or the end of the file, return nil."
  (forward-line)
  (when (and (< (point) (point-max))
             (not (orgtrello-entity-org-card-p))
             (not (orgtrello-entity-org-checkbox-p)))
    (orgtrello-entity-goto-next-checkbox)))

(defun orgtrello-entity-goto-end-card-metadata ()
  "Go to the end of the card metadata.
Does not preserve the current position.
If hitting a heading or the end of the file, return nil."
  (forward-line)
  (when (and (< (point) (point-max))
             (not (orgtrello-entity-org-card-p))
             (not (orgtrello-entity-org-checkbox-p))
             (not (orgtrello-entity-org-comment-p)))
    (orgtrello-entity-goto-end-card-metadata)))

(defun orgtrello-entity-card-metadata-end-point ()
  "Compute the card's metadata end point.
This corresponds to the card's first checkbox position."
  (save-excursion
    (orgtrello-entity-back-to-card)
    (orgtrello-entity-goto-end-card-metadata)
    (1- (point))))

(defun orgtrello-entity-card-at-pt ()
  "Determine if currently on the card region."
  (let ((pt (point)))
    (and (<= (orgtrello-entity-card-start-point) pt)
         (<= pt (orgtrello-entity-card-metadata-end-point)))))

(defun orgtrello-entity-checklist-at-pt ()
  "Determine if currently on the checklist region."
  (= (orgtrello-entity-level) org-trello--checklist-level))

(defun orgtrello-entity-item-at-pt ()
  "Determine if currently on the item region."
  (= (orgtrello-entity-level) org-trello--item-level))

(defun orgtrello-entity-card-description-start-point ()
  "Compute the first character of the card's description content."
  (save-excursion
    (orgtrello-entity-back-to-card)
    (search-forward ":END:" nil t) ;; if not found, return nil & do not move pt
    (1+ (point-at-eol))))
;; in any case, the description is then just 1 point
;; more than the current position

(defun orgtrello-entity-card-end-point ()
  "Compute the current card's end point."
  (save-excursion
    (orgtrello-entity-back-to-card)
    (org-element-property :end (org-element-at-point))))

(defun orgtrello-entity-compute-first-comment-point ()
  "Compute the card's first comment position.
Does preserve position.
If no comment is found, return the card's end region."
  (save-excursion
    (orgtrello-entity-back-to-card)
    (let ((card-region (orgtrello-entity-card-region)))
      (apply 'narrow-to-region card-region)
      (let ((next-pt (-if-let (next-pt
                               (search-forward-regexp "\\*\\* COMMENT " nil t))
                         ;; if not found, return nil and do not move point
                         (save-excursion
                           (goto-char next-pt)
                           (point-at-bol))
                       (orgtrello-entity-card-end-point))))
        (widen)
        next-pt))))

(defun orgtrello-entity-compute-checklist-header-region ()
  "Compute the checklist's region.
Only the header, without items, couple '(start end)."
  `(,(point-at-bol) ,(1+ (point-at-eol))))

(defun orgtrello-entity-goto-next-checkbox-with-same-level (level)
  "Compute the next checkbox's beginning of line (with the same LEVEL).
Does not preserve the current position.
If hitting a heading or the end of the file, return nil.
Otherwise, return the current position."
  (forward-line)
  (if (= level (orgtrello-entity-level))
      (point)
    (if (or (orgtrello-entity-org-card-p) (<= (point-max) (point)))
        nil
      (orgtrello-entity-goto-next-checkbox-with-same-level level))))

(defun orgtrello-entity-next-checklist-point ()
  "Compute the next checklist position from the current position."
  (save-excursion
    (org-end-of-item)
    (1- (point))))

(defun orgtrello-entity-compute-checklist-region ()
  "Compute the checklist's region (including the items) couple '(start end)."
  `(,(orgtrello-buffer-checklist-beginning-pt)
    ,(1- (save-excursion (org-end-of-item) (point)))))

(defun orgtrello-entity-compute-item-region ()
  "Compute the item region couple '(start end)."
  `(,(point-at-bol) ,(point-at-eol)))

(defun orgtrello-entity-card-region ()
  "Compute the card region zone couple '(start end)."
  `(,(orgtrello-entity-card-start-point) ,(orgtrello-entity-card-end-point)))

(defun orgtrello-entity-card-metadata-region ()
  "Compute the card's metadata (description) region couple '(start end)."
  `(,(orgtrello-entity-card-description-start-point)
    ,(orgtrello-entity-card-metadata-end-point)))

(defun orgtrello-entity-card-data-region ()
  "Compute the card's data region (checklists/items) couple '(start end)."
  `(,(1+ (orgtrello-entity-card-metadata-end-point))
    ,(1- (orgtrello-entity-compute-first-comment-point))))

(defun orgtrello-entity-comment-region ()
  "Compute the comment's region.
Expected to be called when the cursor is inside the comment region."
  (save-excursion
    (orgtrello-entity-back-to-card)
    (let ((elem (org-element-at-point)))
      `(,(org-element-property :begin elem) ,(org-element-property :end elem)))))

(defun orgtrello-entity-comment-description-start-point ()
  "Compute the first character of the comment's description content.
Expects the cursor to be on current comment."
  (save-excursion
    (beginning-of-line)
    (search-forward ":END:" nil t) ;; if not found, return nil & do not move pt
    (1+ (point-at-eol))))

(defun orgtrello-entity-comment-description-end-point ()
  "Compute the comment's end point."
  (org-element-property :contents-end (org-element-at-point)))

(defun orgtrello-entity-comment-description-region ()
  "Compute the comment's description region."
  `(,(orgtrello-entity-comment-description-start-point)
    ,(orgtrello-entity-comment-description-end-point)))

(provide 'org-trello-entity)
;;; org-trello-entity.el ends here
