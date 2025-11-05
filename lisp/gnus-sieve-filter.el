;;; gnus-sieve-filter.el --- Create sieve filters from articles -*- lexical-binding: t; -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Version: 1.0.0
;; Package-Requires: ((emacs "27.1") (gnus "5.13"))
;; Keywords: mail, gnus, sieve
;; URL: https://github.com/jwiegley/dot-emacs

;;; Commentary:

;; This package provides an interactive command for creating Gnus sieve
;; filters directly from articles in the summary buffer.  It allows you to:
;;
;; 1. Select filter criteria (to, from, subject) from the current article
;; 2. Edit the patterns for each selected field
;; 3. Choose a target group for filtering
;; 4. Create and apply the sieve rule
;; 5. Move the current article to the target group
;;
;; Usage:
;;
;;   M-x gnus-sieve-create-filter-from-article
;;
;; This command should be run from a Gnus summary buffer when viewing
;; an article.  It will guide you through creating a filter rule and
;; automatically apply it using gnus-sieve-update.

;;; Code:

(require 'gnus)
(require 'gnus-sum)
(require 'gnus-sieve)
(require 'message)

(defgroup gnus-sieve-filter nil
  "Create sieve filters from Gnus articles."
  :group 'gnus
  :prefix "gnus-sieve-filter-")

(defcustom gnus-sieve-filter-match-type 'address
  "Default match type for sieve rules.
Can be `address' for address matching or `header' for substring matching."
  :type '(choice (const :tag "Address match" address)
                 (const :tag "Header substring" header))
  :group 'gnus-sieve-filter)

(defcustom gnus-sieve-filter-move-after-create t
  "Whether to move the article after creating the filter.
If non-nil, the article is moved to the target group immediately
after the sieve rule is created."
  :type 'boolean
  :group 'gnus-sieve-filter)

(defun gnus-sieve-filter--get-header-value (header)
  "Get the value of HEADER from the current article.
HEADER should be a string like \"from\", \"to\", or \"subject\"."
  (gnus-summary-select-article nil 'force)
  (with-current-buffer gnus-original-article-buffer
    (save-restriction
      (widen)
      (message-narrow-to-headers)
      (message-fetch-field header))))

(defun gnus-sieve-filter--read-fields ()
  "Prompt user to select which fields to use for filtering.
Returns a list of selected fields."
  (let* ((from (gnus-sieve-filter--get-header-value "from"))
         (to (gnus-sieve-filter--get-header-value "to"))
         (subject (gnus-sieve-filter--get-header-value "subject"))
         (choices '())
         (prompt ""))

    ;; Build choices list with actual values
    (when from
      (push (cons "from" from) choices))
    (when to
      (push (cons "to" to) choices))
    (when subject
      (push (cons "subject" subject) choices))

    (unless choices
      (error "No headers available to filter on"))

    ;; Display current values in prompt
    (setq prompt
          (concat "Select fields to filter (comma-separated):\n"
                  (mapconcat (lambda (choice)
                               (format "  %s: %s"
                                       (car choice)
                                       (truncate-string-to-width
                                        (cdr choice) 60 nil nil "...")))
                             (reverse choices)
                             "\n")
                  "\n\nFields: "))

    (let* ((available-fields (mapcar #'car choices))
           (selected (completing-read-multiple
                      prompt
                      available-fields
                      nil t)))
      (unless selected
        (error "No fields selected"))
      selected)))

(defun gnus-sieve-filter--edit-pattern (field value)
  "Allow user to edit the pattern for FIELD with initial VALUE.
Returns a cons cell (FIELD . EDITED-VALUE)."
  (let* ((prompt (format "Pattern for %s [%s]: "
                         field
                         (truncate-string-to-width value 40 nil nil "...")))
         (edited (read-string prompt value)))
    (cons field edited)))

(defun gnus-sieve-filter--create-sieve-test (field pattern match-type)
  "Create a sieve test expression for FIELD matching PATTERN.
MATCH-TYPE can be `address' or `header'."
  (cond
   ((eq match-type 'address)
    ;; Address match: (address "field" "pattern")
    (list 'address field pattern))
   ((eq match-type 'header)
    ;; Substring match: (header :contains "field" "pattern")
    (list 'header :contains field pattern))
   (t
    (error "Unknown match type: %s" match-type))))

(defun gnus-sieve-filter--build-sieve-rule (patterns match-type)
  "Build a complete sieve rule from PATTERNS using MATCH-TYPE.
PATTERNS is a list of (field . pattern) cons cells.
Returns a sieve test suitable for the group parameter."
  (let ((tests (mapcar (lambda (p)
                         (gnus-sieve-filter--create-sieve-test
                          (car p) (cdr p) match-type))
                       patterns)))
    (if (= (length tests) 1)
        (car tests)
      ;; Multiple tests: combine with allof
      (cons 'allof (list tests)))))

(defun gnus-sieve-filter--select-target-group ()
  "Prompt user to select a target group for filtering.
Returns the group name."
  (let* ((completion-ignore-case t)
         (group (gnus-completing-read
                 "Move to group"
                 (mapcar (lambda (info)
                           (gnus-info-group info))
                         (cdr gnus-newsrc-alist))
                 nil nil
                 nil
                 'gnus-group-history)))
    (unless group
      (error "No target group selected"))
    group))

(defun gnus-sieve-filter--add-rule-to-group (group sieve-rule)
  "Add SIEVE-RULE to GROUP's sieve parameter.
If the group already has a sieve parameter, this combines the rules
using anyof to create an OR condition."
  (let* ((info (gnus-get-info group))
         (existing-sieve (gnus-group-find-parameter group 'sieve t)))
    (unless info
      (error "Group %s not found" group))

    (let ((new-rule
           (cond
            ;; No existing rule - use new rule directly
            ((null existing-sieve)
             sieve-rule)

            ;; Existing rule is already anyof - append to it
            ((and (listp existing-sieve)
                  (eq (car existing-sieve) 'anyof))
             (list 'anyof
                   (append (cadr existing-sieve)
                           (list sieve-rule))))

            ;; Existing rule is something else - combine with anyof
            (t
             (list 'anyof
                   (list existing-sieve sieve-rule))))))

      ;; Set the parameter
      (gnus-group-set-parameter group 'sieve new-rule)

      ;; Return the new rule for display
      new-rule)))

(defun gnus-sieve-filter--format-sieve-rule (rule)
  "Format RULE as a readable string for display."
  (prin1-to-string rule))

;;;###autoload
(defun gnus-sieve-create-filter-from-article (&optional match-type)
  "Create a sieve filter from the current article.

This interactive command guides you through creating a Gnus sieve
filter based on the headers of the current article:

1. Select which fields to filter on (from, to, subject)
2. Edit the pattern for each selected field
3. Choose a target group for the filter
4. Create and apply the sieve rule
5. Optionally move the current article to the target group

The command must be run from a Gnus summary buffer.

With prefix argument, prompt for match type (address vs substring).
Otherwise uses `gnus-sieve-filter-match-type'."
  (interactive
   (list (when current-prefix-arg
           (intern (completing-read
                    "Match type: "
                    '("address" "header")
                    nil t nil nil
                    (symbol-name gnus-sieve-filter-match-type)))))
   gnus-summary-mode)

  ;; Ensure we're in the right mode
  (unless (eq major-mode 'gnus-summary-mode)
    (error "This command must be run from a Gnus summary buffer"))

  (unless (gnus-summary-article-number)
    (error "No article selected"))

  ;; Use provided match-type or default
  (unless match-type
    (setq match-type gnus-sieve-filter-match-type))

  (let* ((article-number (gnus-summary-article-number))
         ;; Step 1: Select fields
         (selected-fields (gnus-sieve-filter--read-fields))

         ;; Step 2: Edit patterns for each field
         (patterns (mapcar (lambda (field)
                            (let ((value (gnus-sieve-filter--get-header-value field)))
                              (gnus-sieve-filter--edit-pattern field value)))
                          selected-fields))

         ;; Step 3: Select target group
         (target-group (gnus-sieve-filter--select-target-group))

         ;; Step 4: Build sieve rule
         (sieve-rule (gnus-sieve-filter--build-sieve-rule patterns match-type))

         ;; Step 5: Add rule to group
         (final-rule (gnus-sieve-filter--add-rule-to-group target-group sieve-rule)))

    ;; Display the rule that was created
    (message "Created sieve rule for %s:\n%s"
             target-group
             (gnus-sieve-filter--format-sieve-rule sieve-rule))

    ;; Step 6: Update sieve script on server
    (when (yes-or-no-p "Update sieve script on server? ")
      (condition-case err
          (progn
            (gnus-sieve-update)
            (message "Sieve script updated successfully"))
        (error
         (message "Failed to update sieve script: %s" (error-message-string err)))))

    ;; Step 7: Optionally move the article
    (when (and gnus-sieve-filter-move-after-create
               (yes-or-no-p (format "Move article to %s? " target-group)))
      (gnus-summary-move-article nil target-group))

    ;; Return the rule for programmatic use
    sieve-rule))

;;;###autoload
(defun gnus-sieve-create-simple-filter (field pattern target-group)
  "Create a simple sieve filter for FIELD matching PATTERN to TARGET-GROUP.

This is a non-interactive version for programmatic use or for users
who prefer a simpler interface.  FIELD should be \"from\", \"to\",
or \"subject\".  PATTERN is the text to match.

Example:
  (gnus-sieve-create-simple-filter \"from\" \"spam@example.com\" \"INBOX.spam\")"
  (let* ((match-type gnus-sieve-filter-match-type)
         (sieve-rule (gnus-sieve-filter--create-sieve-test field pattern match-type)))
    (gnus-sieve-filter--add-rule-to-group target-group sieve-rule)
    (message "Created sieve rule: %s" (gnus-sieve-filter--format-sieve-rule sieve-rule))
    sieve-rule))

(provide 'gnus-sieve-filter)
;;; gnus-sieve-filter.el ends here
