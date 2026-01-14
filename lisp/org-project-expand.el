;;; org-project-expand.el --- Expand Org project summaries into detailed plans -*- lexical-binding: t -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 14 Jan 2025
;; Version: 1.0
;; Keywords: org ai gptel planning
;; Package-Requires: ((emacs "27.1") (gptel "0.9.0") (org "9.5"))
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

;; This package expands Org-mode project summaries into full project plans
;; with hierarchical task breakdowns and dependency tracking via BLOCKER
;; properties.
;;
;; Usage:
;;
;;   1. Create an Org file or heading with a project description
;;   2. Call `org-project-expand' with point in the description
;;   3. The LLM will generate a full project plan with:
;;      - Hierarchical TODO task breakdown
;;      - Unique ID properties for each task
;;      - BLOCKER properties indicating task dependencies
;;      - Effort estimates where appropriate
;;
;; The generated plan uses org-depend.el conventions for BLOCKER properties:
;;   - Task IDs reference other tasks that must be DONE first
;;   - Use `previous-sibling' to depend on the task immediately above
;;
;; Example BLOCKER usage:
;;
;;   * TODO Research requirements
;;     :PROPERTIES:
;;     :ID: 550e8400-e29b-41d4-a716-446655440000
;;     :END:
;;
;;   * TODO Design system
;;     :PROPERTIES:
;;     :ID: 6ba7b810-9dad-11d1-80b4-00c04fd430c8
;;     :BLOCKER: 550e8400-e29b-41d4-a716-446655440000
;;     :END:
;;
;; Setup:
;;
;;   (use-package org-project-expand
;;     :after (gptel org)
;;     :config
;;     (org-project-expand-install-preset))

;;; Code:

(require 'cl-lib)
(require 'gptel)
(require 'org)
(require 'org-id)

(defgroup org-project-expand nil
  "Expand Org-mode project summaries into detailed plans."
  :group 'org
  :prefix "org-project-expand-")

(defcustom org-project-expand-preset 'sonnet
  "GPTel preset to use for project expansion.
Defaults to `sonnet' which uses Claude Sonnet via LiteLLM.
Set to nil to use current `gptel-backend' and `gptel-model'."
  :type '(choice (const :tag "Claude Sonnet" sonnet)
                 (const :tag "Use current defaults" nil)
                 symbol)
  :group 'org-project-expand)

(defcustom org-project-expand-include-effort t
  "Whether to include effort estimates in generated tasks.
When non-nil, the LLM will add :Effort: properties to tasks."
  :type 'boolean
  :group 'org-project-expand)

(defcustom org-project-expand-max-depth 4
  "Maximum depth of task hierarchy to generate.
Prevents overly deep nesting."
  :type 'integer
  :group 'org-project-expand)

(defun org-project-expand--generate-id ()
  "Generate a unique task ID using UUID.
Returns a UUID string suitable for use as an Org :ID: property."
  (org-id-uuid))

(defun org-project-expand--replace-uuid-placeholders (text)
  "Replace __UUID_N__ placeholders in TEXT with real UUIDs.
Each unique placeholder number gets a consistent UUID replacement,
so __UUID_1__ in an :ID: and __UUID_1__ in a :BLOCKER: get the same UUID."
  (let ((uuid-map (make-hash-table :test 'equal)))
    (replace-regexp-in-string
     "__UUID_\\([0-9]+\\)__"
     (lambda (match)
       (let ((num (match-string 1 match)))
         (or (gethash num uuid-map)
             (puthash num (org-id-uuid) uuid-map))))
     text t)))

(defun org-project-expand--replace-created-placeholders (text)
  "Replace __CREATED__ placeholders in TEXT with current timestamp.
Uses Org inactive timestamp format: [YYYY-MM-DD Day HH:MM]."
  (let ((timestamp (format-time-string "[%Y-%m-%d %a %H:%M]")))
    (replace-regexp-in-string "__CREATED__" timestamp text t t)))

(defun org-project-expand--build-instructions ()
  "Build the instructions for project expansion.
Returns a string to prepend to the user's project description."
  (let ((effort-note (if org-project-expand-include-effort
                         "- Include :Effort: estimates (HH:MM format)"
                       "")))
    (format "Please expand the following project description into a detailed Org-mode project plan.

FORMAT REQUIREMENTS:
- Output valid Org-mode syntax only (no markdown code fences)
- Use TODO headings: * TODO Phase, ** TODO Task, etc.
- Every task MUST have a :PROPERTIES: drawer with:
  - :ID: using placeholder __UUID_N__ (N = unique number)
  - :CREATED: using placeholder __CREATED__
- Add :BLOCKER: property referencing another task's __UUID_N__ when there's a dependency
- Use \"previous-sibling\" as BLOCKER if only depending on task above
%s
- Maximum %d heading levels

EXAMPLE:
* TODO Phase 1: Setup
** TODO Initialize project
   :PROPERTIES:
   :ID: __UUID_1__
   :CREATED: __CREATED__
   :Effort: 1:00
   :END:
** TODO Define requirements
   :PROPERTIES:
   :ID: __UUID_2__
   :CREATED: __CREATED__
   :BLOCKER: __UUID_1__
   :Effort: 4:00
   :END:

PROJECT DESCRIPTION:
" effort-note org-project-expand-max-depth)))

(defun org-project-expand--validate-org (text)
  "Validate that TEXT contains valid Org-mode syntax.
Returns non-nil if valid, signals an error otherwise."
  (with-temp-buffer
    (insert text)
    (org-mode)
    (goto-char (point-min))
    ;; Check for at least one TODO heading
    (unless (re-search-forward "^\\*+ TODO " nil t)
      (error "Generated content does not contain any TODO headings"))
    ;; Check for at least one ID property
    (goto-char (point-min))
    (unless (re-search-forward ":ID:.*" nil t)
      (error "Generated content does not contain any ID properties"))
    t))

(defun org-project-expand--clean-response (response)
  "Clean RESPONSE by removing markdown code fences and replacing placeholders.
Returns the cleaned response string with real UUIDs and timestamps."
  (let ((cleaned response))
    ;; Remove markdown code blocks
    (when (string-match "\\`[ \t\n]*```\\(?:org\\)?[ \t]*\n" cleaned)
      (setq cleaned (replace-match "" nil nil cleaned)))
    (when (string-match "\n```[ \t]*\\'" cleaned)
      (setq cleaned (replace-match "" nil nil cleaned)))
    ;; Remove leading/trailing whitespace
    (setq cleaned (string-trim cleaned))
    ;; Replace UUID placeholders with real UUIDs
    (setq cleaned (org-project-expand--replace-uuid-placeholders cleaned))
    ;; Replace CREATED placeholders with current timestamp
    (setq cleaned (org-project-expand--replace-created-placeholders cleaned))
    cleaned))

(defun org-project-expand--handle-response (response info)
  "Process the LLM RESPONSE and insert it into the buffer.
INFO is the plist containing buffer and position information."
  (cond
   ;; Success case - we got a string response
   ((stringp response)
    (condition-case err
        (let ((cleaned (org-project-expand--clean-response response)))
          ;; Validate the response
          (org-project-expand--validate-org cleaned)
          ;; Insert into buffer
          (with-current-buffer (plist-get info :buffer)
            (save-excursion
              (goto-char (plist-get info :position))
              ;; If we're at a heading, create a subheading
              (when (org-at-heading-p)
                (org-end-of-subtree t t)
                (or (bolp) (insert "\n")))
              (let ((start (point)))
                (insert cleaned)
                (unless (bolp) (insert "\n"))
                ;; Adjust heading levels if needed
                (let ((base-level (save-excursion
                                    (goto-char start)
                                    (if (ignore-errors (org-back-to-heading t))
                                        (org-current-level)
                                      0))))
                  (when (> base-level 0)
                    (save-excursion
                      (goto-char start)
                      (while (re-search-forward "^\\(\\*+\\) " nil t)
                        (let ((current-stars (length (match-string 1))))
                          (replace-match (concat (make-string
                                                  (+ base-level current-stars) ?*)
                                                 " ")
                                         nil t)))))))
              (message "Project plan expanded successfully"))))
      (error
       (message "Failed to process project expansion: %s" (error-message-string err)))))
   ;; Streaming complete
   ((eq response t)
    (message "Project expansion streaming complete"))
   ;; Request aborted
   ((eq response 'abort)
    (message "Project expansion aborted"))
   ;; Nil response - request failed, show the status
   ((null response)
    (message "Project expansion failed: %s" (or (plist-get info :status) "Unknown error")))
   ;; Tool call or other structured response - not expected here
   ((consp response)
    (message "Project expansion received unexpected response type: %S" (car response)))
   ;; Unknown response type
   (t
    (message "Project expansion failed with unexpected response: %S" response))))

;;;###autoload
(defun org-project-expand (beg end)
  "Expand the project description in region from BEG to END into a full plan.

Sends the selected text to an LLM configured via `org-project-expand-backend'
and `org-project-expand-model', generating a detailed project plan with
hierarchical TODO tasks, unique IDs, and BLOCKER dependencies.

When called interactively:
- If a region is active, uses the region as the project description
- Otherwise, uses the current Org subtree (if in org-mode)
- Falls back to the entire buffer

The generated plan is inserted immediately after the current position."
  (interactive
   (cond
    ((use-region-p)
     (list (region-beginning) (region-end)))
    ((and (eq major-mode 'org-mode)
          (ignore-errors (org-back-to-heading t)))
     (save-excursion
       (let ((element (org-element-at-point)))
         (list (org-element-property :begin element)
               (org-element-property :end element)))))
    (t
     (list (point-min) (point-max)))))

  (unless (and beg end)
    (user-error "No region or Org subtree found"))

  (let ((prompt (buffer-substring-no-properties beg end))
        (current-buffer (current-buffer))
        (insert-point (if (use-region-p)
                          (region-end)
                        (save-excursion
                          (goto-char end)
                          (point)))))

    (message "Expanding project plan%s..."
             (if org-project-expand-preset
                 (format " using preset '%s'" org-project-expand-preset)
               (format " using %s/%s" (gptel-backend-name gptel-backend) gptel-model)))

    ;; Check that gptel is loaded and configured
    (unless (featurep 'gptel)
      (user-error "gptel is not loaded. Please ensure gptel is configured"))

    (condition-case err
        (let ((full-prompt (concat (org-project-expand--build-instructions) prompt))
              ;; Disable thinking mode and tools - use simple text generation
              (gptel--request-params nil)
              (gptel-tools nil)
              (gptel-use-tools nil))
          (if org-project-expand-preset
              (gptel-with-preset org-project-expand-preset
                (gptel-request
                    full-prompt
                  :system nil
                  :callback #'org-project-expand--handle-response
                  :buffer current-buffer
                  :position insert-point))
            (gptel-request
                full-prompt
              :system nil
              :callback #'org-project-expand--handle-response
              :buffer current-buffer
              :position insert-point)))
      (error
       (message "Failed to send gptel request: %s" (error-message-string err))))))

;;;###autoload
(defun org-project-expand-file (file)
  "Expand the project description in FILE into a full plan.

Reads FILE, sends its contents to the LLM, and writes the expanded
project plan to a new file with '-expanded' appended to the name.

FILE should contain an Org-mode project description."
  (interactive "fProject description file: ")
  (unless (file-readable-p file)
    (user-error "Cannot read file: %s" file))

  (let* ((prompt (with-temp-buffer
                   (insert-file-contents file)
                   (buffer-string)))
         (output-file (concat (file-name-sans-extension file)
                             "-expanded"
                             (or (file-name-extension file t) ".org")))
         (output-buffer (find-file-noselect output-file)))

    (message "Expanding project plan from %s%s..."
             file
             (if org-project-expand-preset
                 (format " using preset '%s'" org-project-expand-preset)
               ""))

    (unless (featurep 'gptel)
      (user-error "gptel is not loaded. Please ensure gptel is configured"))

    (condition-case err
        (let ((full-prompt (concat (org-project-expand--build-instructions) prompt))
              ;; Disable thinking mode and tools - use simple text generation
              (gptel--request-params nil)
              (gptel-tools nil)
              (gptel-use-tools nil))
          (cl-flet ((do-request ()
                      (gptel-request
                          full-prompt
                        :system nil
                        :callback (lambda (response info)
                                    (cond
                                     ((stringp response)
                                      (condition-case err
                                          (let ((cleaned (org-project-expand--clean-response response)))
                                            (org-project-expand--validate-org cleaned)
                                            (with-current-buffer output-buffer
                                              (erase-buffer)
                                              (insert cleaned)
                                              (org-mode)
                                              (save-buffer)
                                              (message "Expanded plan written to %s" output-file)))
                                        (error
                                         (message "Failed to expand project: %s"
                                                  (error-message-string err)))))
                                     ((null response)
                                      (message "Project expansion failed: %s"
                                               (or (plist-get info :status) "Unknown error")))
                                     (t
                                      (message "Project expansion failed with response: %S" response))))
                        :buffer output-buffer
                        :position (point-min))))
            (if org-project-expand-preset
                (gptel-with-preset org-project-expand-preset
                  (do-request))
              (do-request))))
      (error
       (message "Failed to send gptel request: %s" (error-message-string err))))))

(defun org-project-expand--build-system-prompt ()
  "Build a system prompt for the project-expand preset.
This is a short system prompt suitable for use with non-thinking models."
  "You are a project planning assistant. When given a project description,
expand it into a detailed Org-mode project plan with hierarchical TODO tasks,
unique IDs using __UUID_N__ placeholders, and BLOCKER dependencies between tasks.")

(defun org-project-expand-install-preset ()
  "Install the project-expand preset into gptel.
Creates a preset optimized for project planning that can be used
independently of `org-project-expand'."
  (with-eval-after-load 'gptel
    (gptel-make-preset 'project-expand
      :description "Expand project summaries into detailed plans"
      :system (org-project-expand--build-system-prompt)
      :parents 'sonnet)))

(defun org-project-expand-test ()
  "Run a simple test to verify gptel connectivity.
Sends a minimal prompt using the configured preset and reports the result."
  (interactive)
  (message "Testing gptel connectivity...")
  (message "  Preset: %s" org-project-expand-preset)

  ;; Disable thinking mode and tools - use simple text generation
  (let ((gptel--request-params nil)
        (gptel-tools nil)
        (gptel-use-tools nil))
    (cl-flet ((do-test ()
                (gptel-request
                    "Reply with just the word 'OK' and nothing else."
                  :system nil
                  :callback (lambda (response info)
                              (message "Test result: response=%S status=%s"
                                       (if (stringp response)
                                           (substring response 0 (min 50 (length response)))
                                         response)
                                       (plist-get info :status))))))
      (if org-project-expand-preset
          (gptel-with-preset org-project-expand-preset
            (do-test))
        (do-test)))))

(provide 'org-project-expand)

;;; org-project-expand.el ends here
