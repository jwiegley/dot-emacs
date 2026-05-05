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
;; capital `N' and `T' keys in the org-drafts hydra synthesize a title
;; via `gptel-ext-title' instead of moving the first body line into the
;; heading.
;;
;; Setup:
;;
;;   (require 'org-drafts-ext)
;;   (org-drafts-ext-install)

;;; Code:

(require 'org-drafts)
(require 'gptel-ext)

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
      (ignore-errors (backward-kill-sexp)))
    (skip-chars-backward " \t")
    (delete-region (point) (line-end-position))
    (gptel-ext-title)))

;;;###autoload
(defun org-drafts-ext-install ()
  "Wire `org-drafts-ext-ai-title-body-function' into the org-drafts hydra.
After this is called, the capital `N' and `T' hydra keys convert a
draft into NOTE/TODO with a title synthesized by `gptel-ext-title'."
  (setq org-drafts-alt-task-body-function
        #'org-drafts-ext-ai-title-body-function))

(provide 'org-drafts-ext)

;;; org-drafts-ext.el ends here
