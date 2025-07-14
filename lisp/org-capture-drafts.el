;;; org-capture-drafts --- Manage drafts using Org-capture -*- lexical-binding: t -*-

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 14 Jul 2025
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

;; I use the following Org-capture template:
;;
;;   ("d" "DRAFT" entry
;;     "path-to-inbox-file.org"
;;     "* DRAFT %U\n%?"
;;     :prepend t):
;;
;; With the following use-package declaration:
;;
;;   (use-package org-capture-drafts
;;     :after (org)
;;     :bind* ("M-M" . (lambda () (interactive) (org-capture nil "d")))
;;     :config
;;     (org-capture-drafts-install))

(require 'cl-lib)
(require 'org-macs)
(require 'org-capture)
(require 'pretty-hydra)

(defgroup org-capture-drafts nil
  "Capture drafts that begin in the Org-capture buffer"
  :group 'org)

(cl-defun org-capture-drafts-change (keyword)
  (interactive)
  (goto-char (point-min))
  (re-search-forward "^\\*+ \\(DRAFT\\) ")
  (replace-match keyword t t nil 1)
  (org-capture-finalize current-prefix-arg))

(defun org-capture-drafts-gptel ()
  (interactive)
  (goto-char (point-min))
  (forward-line)
  (let ((str (string-trim
              (buffer-substring-no-properties (point) (point-max)))))
    (org-capture-drafts-change "SCRAP")
    (corsair-open-chat-buffer t)
    (insert str)
    (gptel-send)))

(defun org-capture-drafts-kagi ()
  (interactive)
  (goto-char (point-min))
  (forward-line)
  (let ((str (string-trim
              (buffer-substring-no-properties (point) (point-max)))))
    (org-capture-drafts-change "SCRAP")
    (browse-url
     (browse-url-encode-url
      (concat "https://kagi.com/search?q=" str)))))

(defun org-capture-drafts-perplexity ()
  (interactive)
  (goto-char (point-min))
  (forward-line)
  (let ((str (string-trim
              (buffer-substring-no-properties (point) (point-max)))))
    (org-capture-drafts-change "SCRAP")
    (browse-url
     (browse-url-encode-url
      (concat "https://www.perplexity.ai/search/?q=" str "&copilot=true")))))

(pretty-hydra-define
  org-capture-drafts
  (:color teal :quit-key "q")
  ("Org"
   (("n"   (org-capture-drafts-change "NOTE") "NOTE")
    ("t"   (org-capture-drafts-change "TODO") "TODO")
    ("d"   org-capture-finalize "DRAFT")
    ("C-c" org-capture-finalize "DRAFT"))
   "Web"
   (("k"   org-capture-drafts-kagi "Kagi"))
   "AI"
   (("g"   org-capture-drafts-gptel "GPTel")
    ("p"   org-capture-drafts-perplexity "Perplexity"))))

(defun org-capture-drafts-action (&optional arg)
  (interactive "P")
  (if (save-excursion
        (goto-char (point-min))
        (looking-at-p "^\\*+ DRAFT "))
      (org-capture-drafts/body)
    (org-capture-finalize arg)))

(defun org-capture-drafts-install ()
  (define-key org-capture-mode-map (kbd "C-c C-c")
              #'org-capture-drafts-action))

(provide 'org-capture-drafts)

;;; org-capture-drafts.el ends here
