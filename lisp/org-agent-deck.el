;;; org-agent-deck.el --- Org integration for agent-deck -*- lexical-binding: t; -*-

;; Copyright (C) 2026 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Keywords: outlines tools
;; URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;;; Commentary:

;; Send the current Org entry to an agent-deck session, or insert a
;; session's latest output as a NOTE.  To use agent-deck on another host:
;;
;;   (setq org-agent-deck-command '("ssh" "hera" "agent-deck"))

;;; Code:

(require 'json)
(require 'org)
(require 'org-element)
(require 'ox-md)
(require 'seq)
(require 'subr-x)

(defgroup org-agent-deck nil
  "Org integration for agent-deck sessions."
  :group 'org)

(defcustom org-agent-deck-command '("agent-deck")
  "Command prefix used for every agent-deck operation.
For a remote agent-deck on hera, use a list containing
\"ssh\", \"hera\", and \"agent-deck\", in that order."
  :type '(repeat string)
  :group 'org-agent-deck)

(defcustom org-agent-deck-pandoc-program "pandoc"
  "Pandoc executable used to convert agent output to Org."
  :type 'string
  :group 'org-agent-deck)

(defun org-agent-deck--run (command &optional input)
  "Run COMMAND synchronously with INPUT on standard input.
Return standard output, or signal a `user-error' with command diagnostics."
  (unless (and (consp command)
               (seq-every-p #'stringp command)
               (not (string-empty-p (car command))))
    (user-error "Command must be a non-empty list of strings"))
  (let ((stderr-file (make-temp-file "org-agent-deck-stderr-")))
    (unwind-protect
        (condition-case err
            (with-temp-buffer
              (let* ((status
                      (apply #'call-process-region
                             (or input "") nil (car command) nil
                             (list t stderr-file) nil (cdr command)))
                     (stdout (buffer-string))
                     (stderr
                      (with-temp-buffer
                        (insert-file-contents stderr-file)
                        (buffer-string))))
                (unless (equal status 0)
                  (let ((detail
                         (string-trim
                          (if (string-empty-p stderr)
                              stdout
                            (concat stderr
                                    (unless (string-empty-p stdout)
                                      (concat "\n" stdout)))))))
                    (user-error "%s failed (%s): %s"
                                (mapconcat #'shell-quote-argument command " ")
                                (if (integerp status)
                                    (format "exit %d" status)
                                  status)
                                (if (string-empty-p detail)
                                    "no diagnostic output"
                                  detail))))
                stdout))
          (file-missing
           (user-error "Cannot run %s: %s"
                       (car command) (error-message-string err))))
      (ignore-errors (delete-file stderr-file)))))

(defun org-agent-deck--call (input &rest arguments)
  "Run agent-deck with ARGUMENTS and optional standard INPUT."
  (org-agent-deck--run
   (append org-agent-deck-command arguments)
   input))

(defun org-agent-deck--json (text context)
  "Parse JSON TEXT or report malformed output from CONTEXT."
  (condition-case err
      (json-parse-string text)
    (json-parse-error
     (user-error "%s returned invalid JSON: %s"
                 context (error-message-string err)))))

(defun org-agent-deck--sessions ()
  "Return active agent-deck sessions as property lists."
  (let ((sessions
         (org-agent-deck--json
          (org-agent-deck--call nil "list" "--json")
          "Agent-deck list")))
    (unless (vectorp sessions)
      (user-error "Agent-deck list returned JSON other than an array"))
    (seq-keep
     (lambda (session)
       (when (and (hash-table-p session)
                  (not (eq (gethash "archived" session) t)))
         (let ((id (gethash "id" session)))
           (when (and (stringp id) (not (string-empty-p id)))
             (list :id id
                   :title (or (gethash "title" session) id)
                   :group (gethash "group" session)
                   :status (or (gethash "status" session) "unknown"))))))
     sessions)))

(defun org-agent-deck--read-session (prompt)
  "Read an active agent-deck session using PROMPT and return its ID."
  (let* ((sessions (org-agent-deck--sessions))
         (candidates
          (mapcar
           (lambda (session)
             (let ((group (plist-get session :group)))
               (cons
                (format "%s%s [%s] (%s)"
                        (plist-get session :title)
                        (if (and (stringp group) (not (string-empty-p group)))
                            (format " — %s" group)
                          "")
                        (plist-get session :status)
                        (plist-get session :id))
                (plist-get session :id))))
           sessions)))
    (unless candidates
      (user-error "No active agent-deck sessions found"))
    (cdr (assoc (completing-read prompt candidates nil t) candidates))))

(defun org-agent-deck--export-options (options _backend)
  "Force suitable Markdown export OPTIONS for the current entry."
  (dolist (setting '((:md-headline-style atx)
                     (:md-toplevel-hlevel 1)
                     (:with-tasks t)
                     (:with-todo-keywords nil)
                     (:with-toc nil)))
    (setq options (plist-put options (car setting) (cadr setting))))
  options)

(defun org-agent-deck--entry-markdown ()
  "Return the current Org entry and its subtree as Markdown."
  (save-excursion
    (org-back-to-heading t)
    (let ((mark-active nil)
          (org-export-filter-options-functions
           (cons #'org-agent-deck--export-options
                 org-export-filter-options-functions)))
      (save-restriction
        (org-narrow-to-subtree)
        (string-trim (org-export-as 'md))))))

(defun org-agent-deck--latest-output (session-id)
  "Return SESSION-ID's latest output as (TITLE . MARKDOWN)."
  (let ((output
         (org-agent-deck--json
          (org-agent-deck--call
           nil "session" "output" session-id "--json")
          "Agent-deck session output")))
    (unless (hash-table-p output)
      (user-error "Agent-deck session output returned JSON other than an object"))
    (let ((content (gethash "content" output))
          (title (gethash "session_title" output)))
      (unless (and (stringp content) (not (string-empty-p content)))
        (user-error "Session %s has no output" session-id))
      (cons (if (and (stringp title) (not (string-empty-p title)))
                title
              session-id)
            content))))

(defun org-agent-deck--markdown-to-org (markdown)
  "Convert MARKDOWN to Org with Pandoc and return the result."
  (string-trim-right
   (org-agent-deck--run
    (list org-agent-deck-pandoc-program
          "-f" "markdown-auto_identifiers" "-t" "org")
    markdown)))

(defun org-agent-deck--nest-headings (begin end level)
  "Nest Org headings between BEGIN and END beneath LEVEL."
  (save-excursion
    (save-restriction
      (narrow-to-region begin end)
      (let ((tree (org-element-parse-buffer)))
        (dolist (position
                 (reverse
                  (org-element-map tree 'headline
                    (lambda (headline)
                      (org-element-property :begin headline)))))
          (goto-char position)
          (insert (make-string level ?*)))))))

(defun org-agent-deck--insert-note (title body)
  "Insert a sibling NOTE named TITLE containing Org BODY."
  (org-back-to-heading t)
  (org-insert-heading-respect-content)
  (let ((level (org-current-level)))
    (insert "NOTE "
            (replace-regexp-in-string "[\n\r]+" " " (string-trim title))
            "\n")
    (let ((begin (point-marker)))
      (insert body)
      (unless (bolp)
        (insert ?\n))
      (let ((end (copy-marker (point) t)))
        (org-agent-deck--nest-headings begin end level)
        (goto-char end)
        (set-marker begin nil)
        (set-marker end nil)))))

;;;###autoload
(defun org-agent-deck-send-entry (&optional session-id)
  "Send the current Org entry as Markdown to SESSION-ID.
Interactively, choose a session from agent-deck's active list."
  (interactive)
  (unless (derived-mode-p 'org-mode)
    (user-error "This command requires Org mode"))
  (setq session-id
        (or session-id
            (org-agent-deck--read-session "Send entry to session: ")))
  (org-agent-deck--call
   (org-agent-deck--entry-markdown)
   "session" "send" session-id "--message-file" "-")
  (message "Sent Org entry to %s" session-id))

;;;###autoload
(defun org-agent-deck-insert-latest-output (&optional session-id)
  "Insert SESSION-ID's latest output as a sibling Org NOTE.
Interactively, choose a session from agent-deck's active list."
  (interactive)
  (unless (derived-mode-p 'org-mode)
    (user-error "This command requires Org mode"))
  (setq session-id
        (or session-id
            (org-agent-deck--read-session "Insert output from session: ")))
  (pcase-let* ((`(,title . ,markdown)
                 (org-agent-deck--latest-output session-id))
                (body (org-agent-deck--markdown-to-org markdown)))
    (atomic-change-group
      (org-agent-deck--insert-note title body)))
  (message "Inserted latest output from %s" session-id))

(provide 'org-agent-deck)

;;; org-agent-deck.el ends here
