;;; my-gnus-sieve.el --- Create Gnus sieve filter rules interactively -*- lexical-binding: t -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 05 Jan 2025
;; Version: 1.0
;; Keywords: gnus sieve filtering
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

;; This module provides an interactive function to create Gnus sieve filter
;; rules from the current article. It allows you to:
;;
;; 1. Select which fields (to, from, subject) to filter on
;; 2. Edit the pattern/regexp for each selected field
;; 3. Choose the destination mail group
;; 4. Automatically create and update sieve rules via gnus-sieve-update
;; 5. Move the current article to the chosen group
;;
;; Usage: In a Gnus summary buffer, position point on an article and run:
;;   M-x my-gnus-sieve-create-filter-from-article

;;; Code:

(require 'gnus-sum)
(require 'gnus-sieve)
(require 'message)

(defgroup my-gnus-sieve nil
  "Interactive creation of Gnus sieve filter rules"
  :group 'gnus-sieve)

(defcustom my-gnus-sieve-default-match-type 'substring
  "Default match type for sieve filter rules.
Can be 'substring for substring matching or 'regexp for regular expression matching."
  :type '(choice (const :tag "Substring" substring)
                 (const :tag "Regular Expression" regexp))
  :group 'my-gnus-sieve)

(defun my-gnus-sieve--get-article-headers ()
  "Extract to, from, and subject headers from the current article.
Returns an alist with keys 'to, 'from, and 'subject."
  (save-excursion
    (gnus-summary-select-article t t)
    (set-buffer gnus-original-article-buffer)
    (save-restriction
      (message-narrow-to-headers)
      (list (cons 'to (or (message-fetch-field "to") ""))
            (cons 'from (or (message-fetch-field "from") ""))
            (cons 'subject (or (message-fetch-field "subject") ""))))))

(defun my-gnus-sieve--select-fields (headers)
  "Prompt user to select which header fields to filter on.
HEADERS is an alist of header fields.
Returns a list of selected field symbols."
  (let* ((field-names '(("From" . from)
                        ("To" . to)
                        ("Subject" . subject)))
         (selected (completing-read-multiple
                    "Filter on fields (comma-separated): "
                    field-names
                    nil t)))
    (mapcar (lambda (name)
              (cdr (assoc name field-names)))
            selected)))

(defun my-gnus-sieve--edit-pattern (field value)
  "Prompt user to edit the filter pattern for FIELD with initial VALUE.
Returns the edited pattern string."
  (let ((prompt (format "Pattern for %s [%s]: " field value)))
    (read-string prompt value)))

(defun my-gnus-sieve--build-sieve-rule (field-patterns)
  "Build a sieve rule from FIELD-PATTERNS.
FIELD-PATTERNS is an alist of (field . pattern) pairs.
Returns a sieve rule expression suitable for gnus-parameters."
  (let ((conditions
         (mapcar (lambda (fp)
                   (let ((field (car fp))
                         (pattern (cdr fp)))
                     (pcase field
                       ('from `(from ,pattern))
                       ('to `(to ,pattern))
                       ('subject `(subject ,pattern)))))
                 field-patterns)))
    (if (= (length conditions) 1)
        (car conditions)
      `(or ,@conditions))))

(defun my-gnus-sieve--add-to-gnus-parameters (group sieve-rule)
  "Add or update gnus-parameters for GROUP with SIEVE-RULE.
This modifies the gnus-parameters variable to include the sieve rule."
  (let* ((params (copy-tree gnus-parameters))
         (group-params (assoc group params)))
    (if group-params
        ;; Group exists, update or add sieve rule
        (let ((sieve-param (assq 'sieve (cdr group-params))))
          (if sieve-param
              ;; Sieve rule exists, update it
              (setcdr sieve-param sieve-rule)
            ;; No sieve rule, add it
            (setcdr group-params
                    (append (cdr group-params)
                            (list (cons 'sieve sieve-rule))))))
      ;; Group doesn't exist, create new entry
      (setq params (append params
                           (list (list group
                                       (cons 'sieve sieve-rule))))))
    ;; Update gnus-parameters
    (setq gnus-parameters params)))

(defun my-gnus-sieve--select-destination-group ()
  "Prompt user to select a destination mail group.
Returns the selected group name."
  (gnus-completing-read "Move to group" gnus-active-hashtb
                        nil nil nil 'gnus-group-history))

;;;###autoload
(defun my-gnus-sieve-create-filter-from-article ()
  "Interactively create a sieve filter rule from the current article.

This function:
1. Extracts to, from, and subject from the current article
2. Prompts you to select which fields to filter on
3. Allows you to edit the pattern for each selected field
4. Prompts for the destination mail group
5. Creates a sieve parameter in gnus-parameters
6. Runs gnus-sieve-update to generate and update sieve rules
7. Moves the current article to the selected group

This provides a quick way to create mail filtering rules directly from
articles that should have been filtered."
  (interactive)
  (unless (derived-mode-p 'gnus-summary-mode)
    (error "This command must be run from a Gnus summary buffer"))

  (let* ((headers (my-gnus-sieve--get-article-headers))
         (selected-fields (my-gnus-sieve--select-fields headers))
         (field-patterns '())
         (dest-group nil)
         (sieve-rule nil))

    (when (null selected-fields)
      (error "No fields selected for filtering"))

    ;; For each selected field, prompt for pattern
    (dolist (field selected-fields)
      (let* ((value (cdr (assq field headers)))
             (pattern (my-gnus-sieve--edit-pattern field value)))
        (when (and pattern (not (string-empty-p pattern)))
          (push (cons field pattern) field-patterns))))

    (when (null field-patterns)
      (error "No patterns specified for filtering"))

    ;; Prompt for destination group
    (setq dest-group (my-gnus-sieve--select-destination-group))

    ;; Build sieve rule
    (setq sieve-rule (my-gnus-sieve--build-sieve-rule field-patterns))

    ;; Add to gnus-parameters
    (my-gnus-sieve--add-to-gnus-parameters dest-group sieve-rule)

    ;; Update sieve rules
    (message "Updating sieve rules...")
    (condition-case err
        (progn
          (gnus-sieve-update)
          (message "Sieve rules updated successfully"))
      (error
       (message "Warning: Failed to update sieve rules: %s" (error-message-string err))))

    ;; Move article to destination group
    (message "Moving article to %s..." dest-group)
    (gnus-summary-move-article nil dest-group)

    (message "Filter rule created and article moved to %s" dest-group)))

(provide 'my-gnus-sieve)
;;; my-gnus-sieve.el ends here
