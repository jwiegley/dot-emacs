;;; org-drafts-ext.el --- AI extensions for org-drafts -*- lexical-binding: t -*-

;; Copyright (C) 2026 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Keywords: outlines convenience ai
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

;; AI-powered extensions for `org-drafts'.  Plugs into the
;; `org-drafts-alt-task-body-function' extension point so that the
;; capital `N', `T', and `P' keys in the org-drafts hydra synthesize a
;; title via `gptel-ext-title' instead of moving the first body line into
;; the heading.  `org-drafts-ext-paste-prompt' also turns clipboard
;; Markdown into a titled PROMPT in one command.
;;
;; Setup:
;;
;;   (require 'org-drafts-ext)
;;   (org-drafts-ext-install)

;;; Code:

(require 'org-drafts)
(require 'gptel-ext)
(require 'org-element)
(require 'seq)

(declare-function iTerm2-send-to-current-window "personal" (&optional arg))
(declare-function markdown-to-org-region nil (start end))

(defun org-drafts-ext-ai-title-body-function (heading-pos _beg _end)
  "Synthesize an AI-generated title for the heading via `gptel-ext-title'.
Strips the trailing timestamp (or any other bracketed sexp) from the
heading line and then asks `gptel-ext-title' to fill in a title
asynchronously based on the entry's body content.  HEADING-POS is the
marker at the heading line.  The other arguments are unused."
  (save-excursion
    (goto-char heading-pos)
    (goto-char (line-end-position))
    (when (eq (char-before) ?\])
      (condition-case nil
          (let ((end (point)))
            (backward-sexp)
            (delete-region (point) end))
        (scan-error nil)))
    (skip-chars-backward " \t")
    (delete-region (point) (line-end-position))
    (gptel-ext-title)
    (when current-prefix-arg
      (iTerm2-send-to-current-window
       (org-ext-with-entry-narrowed
        (search-forward ":END:\n" nil t)
        (buffer-substring-no-properties (point) (point-max)))))))

;;;###autoload
(defun org-drafts-ext-paste-prompt ()
  "Yank clipboard Markdown into the current DRAFT and make it a PROMPT.
The inserted text is converted to Org with `markdown-to-org-region'.
Converted headings are nested under the DRAFT; when the result contains
only paragraphs, it is also filled.  Finally, this runs the same
alternate title action as the org-drafts `P' key."
  (interactive)
  (unless (derived-mode-p 'org-mode)
    (user-error "This command requires Org mode"))
  (org-back-to-heading t)
  (unless (equal (org-get-todo-state) "DRAFT")
    (user-error "Current entry is not a DRAFT"))
  (let ((heading (point))
        (level (org-current-level)))
    (org-end-of-meta-data t)
    (let ((beg (point-marker))
          end)
      (yank)
      (setq end (copy-marker (point) t))
      (markdown-to-org-region beg end)
      (goto-char end)
      (unless (bolp)
        (insert ?\n))
      (save-restriction
        (narrow-to-region beg end)
        (let* ((tree (org-element-parse-buffer))
               (contents (org-element-contents tree))
               (section (and (= (length contents) 1) (car contents)))
               (plain
                (and section
                     (eq (org-element-type section) 'section)
                     (seq-every-p
                      (lambda (element)
                        (eq (org-element-type element) 'paragraph))
                      (org-element-contents section)))))
          (dolist (pos (reverse (org-element-map tree 'headline
                                  (lambda (element)
                                    (org-element-property :begin element)))))
            (goto-char pos)
            (insert (make-string level ?*)))
          (when plain
            (fill-region (point-min) (point-max)))))
      (set-marker beg nil)
      (set-marker end nil))
    (goto-char heading)
    (org-drafts-prompt t)))

;;;###autoload
(defun org-drafts-ext-install ()
  "Install AI title actions and the Org `H-p' paste-prompt binding.
The capital org-drafts hydra actions synthesize titles through
`gptel-ext-title'."
  (setq org-drafts-alt-task-body-function
        #'org-drafts-ext-ai-title-body-function)
  (define-key org-mode-map (kbd "H-p") #'org-drafts-ext-paste-prompt))

(provide 'org-drafts-ext)

;;; org-drafts-ext.el ends here
