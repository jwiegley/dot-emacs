;;; muse-backlink.el --- backlinks for Muse

;; Copyright (C) 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; Author: Jim Ottaway <j.ottaway@lse.ac.uk>
;; Keywords:

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Hierarchical backlink insertion into new muse pages.
;;
;; To add:
;;
;; (require 'muse-backlink)
;; (muse-backlink-install)
;;
;; To control what gets backlinked, modify
;; `muse-backlink-exclude-backlink-regexp' and
;; `muse-backlink-exclude-backlink-parent-regexp'.
;;
;; To stop backlinking temporarily:
;; (setq muse-backlink-create-backlinks nil)
;;
;; To remove the backlink functionality completely:
;;
;; (muse-backlink-remove)

;;; Contributors:

;;; Code:

(require 'muse)
(require 'muse-project)

(eval-when-compile (require 'muse-mode))

(eval-and-compile
  (if (< emacs-major-version 22)
      (progn
        ;; Swiped from Emacs 22.0.50.4
        (defvar muse-backlink-split-string-default-separators "[ \f\t\n\r\v]+"
        "The default value of separators for `split-string'.

A regexp matching strings of whitespace.  May be locale-dependent
\(as yet unimplemented).  Should not match non-breaking spaces.

Warning: binding this to a different value and using it as default is
likely to have undesired semantics.")

        (defun muse-backlink-split-string (string &optional separators omit-nulls)
        "Split STRING into substrings bounded by matches for SEPARATORS.

The beginning and end of STRING, and each match for SEPARATORS, are
splitting points.  The substrings matching SEPARATORS are removed, and
the substrings between the splitting points are collected as a list,
which is returned.

If SEPARATORS is non-nil, it should be a regular expression matching text
which separates, but is not part of, the substrings.  If nil it defaults to
`split-string-default-separators', normally \"[ \\f\\t\\n\\r\\v]+\", and
OMIT-NULLS is forced to t.

If OMIT-NULLS is t, zero-length substrings are omitted from the list \(so
that for the default value of SEPARATORS leading and trailing whitespace
are effectively trimmed).  If nil, all zero-length substrings are retained,
which correctly parses CSV format, for example.

Note that the effect of `(split-string STRING)' is the same as
`(split-string STRING split-string-default-separators t)').  In the rare
case that you wish to retain zero-length substrings when splitting on
whitespace, use `(split-string STRING split-string-default-separators)'.

Modifies the match data; use `save-match-data' if necessary."
        (let ((keep-nulls (not (if separators omit-nulls t)))
              (rexp (or separators muse-backlink-split-string-default-separators))
              (start 0)
              notfirst
              (list nil))
          (while (and (string-match rexp string
                                    (if (and notfirst
                                             (= start (match-beginning 0))
                                             (< start (length string)))
                                        (1+ start) start))
                      (< start (length string)))
            (setq notfirst t)
            (if (or keep-nulls (< start (match-beginning 0)))
                (setq list
                      (cons (substring string start (match-beginning 0))
                            list)))
            (setq start (match-end 0)))
          (if (or keep-nulls (< start (length string)))
              (setq list
                    (cons (substring string start)
                          list)))
          (nreverse list))))
    (defalias 'muse-backlink-split-string 'split-string)))

(defgroup muse-backlink nil
  "Hierarchical backlinking for Muse."
  :group 'muse)

(defcustom muse-backlink-create-backlinks t
  "When non-nil, create hierarchical backlinks in new Muse pages.
For control over which pages will receive backlinks, see
`muse-backlink-exclude-backlink-parent-regexp' and
`muse-backlink-exclude-backlink-regexp'."
  :type 'boolean
  :group 'muse-backlink)

(defcustom muse-backlink-avoid-bad-links t
  "When non-nil, avoid bad links when backlinking."
  :type 'boolean
  :group 'muse-backlink)

;; The default for exclusion stops backlinks from being added to and
;; from planner day pages.
(defcustom muse-backlink-exclude-backlink-parent-regexp
  "^[0-9][0-9][0-9][0-9]\\.[0-9][0-9]\\.[0-9][0-9]$"
  "Regular expression matching pages whose children should not have backlinks."
  :type 'regexp
  :group 'muse-backlink)

(defcustom muse-backlink-exclude-backlink-regexp
  "^[0-9][0-9][0-9][0-9]\\.[0-9][0-9]\\.[0-9][0-9]$"
  "Regular expression matching pages that should not have backlinks."
  :type 'regexp
  :group 'muse-backlink)

(defcustom muse-backlink-separator "/"
  "String that separates backlinks.
Should be something that will not appear as a substring in an explicit
link that has no description."
  :type 'string
  :group 'muse-backlink)

(defcustom muse-backlink-before-string "backlinks: "
  "String to come before the backlink list."
  :type 'string
  :group 'muse-backlink)

(defcustom muse-backlink-after-string ""
  "String to come after the backlink list."
  :type 'string
  :group 'muse-backlink)

(defcustom muse-backlink-separator "/"
  "String that separates backlinks.
Should be something that will not appear as a substring in an explicit
link that has no description."
  :type 'string
  :group 'muse-backlink)

(defcustom muse-backlink-regexp
  (concat "^"
          (regexp-quote muse-backlink-before-string)
          "\\("
          (regexp-quote muse-backlink-separator)
          ".+\\)"
          (regexp-quote muse-backlink-after-string))
  ;; Really, I want something like this, but I can't make it work:
  ;;   (concat "^\\("
  ;;           (regexp-quote muse-backlink-separator)
  ;;           "\\(?:"
  ;;           muse-explicit-link-regexp
  ;;           "\\)\\)+")
  "Regular expression to match backlinks in a buffer.
Match 1 is the list of backlinks without `muse-backlink-before-string'
and `muse-backlink-after-string'."
  :type 'regexp
  :group 'muse-backlink)

(defun muse-backlink-goto-insertion-point ()
  "Find the right place to add backlinks."
  (goto-char (point-min))
  (when (looking-at "\\(?:^#.+[ \t]*\n\\)+")
    (goto-char (match-end 0))))

(defun muse-backlink-get-current ()
  "Return a list of backlinks in the current buffer."
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward muse-backlink-regexp nil t)
      (muse-backlink-split-string
       (match-string 1)
       (regexp-quote muse-backlink-separator) t))))

(defun muse-backlink-format-link-list (links)
  "Format the list of LINKS as backlinks."
  (concat muse-backlink-separator
          (mapconcat #'identity links muse-backlink-separator)))

(defun muse-backlink-insert-links (links)
  "Insert backlinks to LINKS into the current page.
LINKS is a list of links ordered by ancestry, with the parent as the
last element."
  (muse-backlink-goto-insertion-point)
  (insert muse-backlink-before-string
          (muse-backlink-format-link-list links)
          muse-backlink-after-string
          ;; Could have this in the after string, but they might get
          ;; deleted.
          "\n\n"))

(defun muse-backlink-unsaved-page-p (page project)
  "Return non-nil if PAGE is in PROJECT but has not been saved."
  (member
   page
   (mapcar
    #'(lambda (b)
        (with-current-buffer b
          (and (derived-mode-p 'muse-mode)
               (equal muse-current-project project)
               (not (muse-project-page-file
                     (muse-page-name)
                     muse-current-project))
               (muse-page-name))))
    (buffer-list))))

(defvar muse-backlink-links nil
  "Internal variable.
The links to insert in the forthcomingly visited muse page.")

(defvar muse-backlink-pending nil
  "Internal variable.")

(defvar muse-backlink-parent-buffer nil
  "Internal variable.
The parent buffer of the forthcomingly visited muse page.")


;;; Attach hook to the derived mode hook, to avoid problems such as
;;; planner-prepare-file thinking that the buffer needs no template.
(defun muse-backlink-get-mode-hook ()
  (derived-mode-hook-name major-mode))

(defun muse-backlink-insert-hook-func ()
  "Insert backlinks into the current buffer and clean up."
  (when (and muse-backlink-links
             muse-backlink-pending
             (string= (car muse-backlink-links) (muse-page-name)))
    (muse-backlink-insert-links (cdr muse-backlink-links))
    (when muse-backlink-avoid-bad-links
      (save-buffer)
      (when muse-backlink-parent-buffer
        (with-current-buffer muse-backlink-parent-buffer
          (font-lock-fontify-buffer))))
    (setq muse-backlink-links nil
          muse-backlink-parent-buffer nil
          muse-backlink-pending nil)
    (remove-hook (muse-backlink-get-mode-hook) #'muse-backlink-insert-hook-func)))

(defun muse-backlink-handle-link (link)
  "When appropriate, arrange for backlinks on visiting LINK."
  (when (and muse-backlink-create-backlinks
             (not muse-backlink-pending)
             (memq this-command
                   '(muse-follow-name-at-point muse-follow-name-at-mouse))
             (not muse-publishing-p)
             (not (and (boundp 'muse-colors-fontifying-p)
                       muse-colors-fontifying-p)))
    (require 'muse-mode)
    (setq
     muse-backlink-links
     (save-match-data
       (let* ((orig-link (or link (match-string 1)))
              (link (if (string-match "#" orig-link)
                        (substring orig-link 0 (match-beginning 0))
                      orig-link)))
         (unless
             (or (not muse-current-project)
                 (string-match muse-url-regexp orig-link)
                 (string-match muse-image-regexp orig-link)
                 (and (boundp 'muse-wiki-interwiki-regexp)
                      (string-match muse-wiki-interwiki-regexp
                                    orig-link))
                 ;; Don't add a backlink if the page already
                 ;; exists, whether it has been saved or not.
                 (or (muse-project-page-file link muse-current-project)
                     (muse-backlink-unsaved-page-p link muse-current-project))
                 (string-match muse-backlink-exclude-backlink-parent-regexp
                               (muse-page-name))
                 (string-match muse-backlink-exclude-backlink-regexp link))
           ;; todo: Hmm. This will only work if the child page is the
           ;; same mode as the parent page.
           (add-hook (muse-backlink-get-mode-hook) #'muse-backlink-insert-hook-func)
           (setq muse-backlink-pending t)
           (when muse-backlink-avoid-bad-links
             (setq muse-backlink-parent-buffer (current-buffer))
             (unless (muse-project-page-file
                      (muse-page-name) muse-current-project)
               ;; It must be modified...
               (save-buffer)))
           (cons link
                 (append (muse-backlink-get-current)
                         (list (muse-make-link (muse-page-name))))))))))
  ;; Make sure we always return nil
  nil)

(defun muse-backlink-install ()
  "Add backlinking functionality to muse-mode."
  (add-to-list 'muse-explicit-link-functions #'muse-backlink-handle-link))

(defun muse-backlink-remove ()
  "Remove backlinking functionality from muse-mode."
  (setq muse-explicit-link-functions
        (delq #'muse-backlink-handle-link muse-explicit-link-functions)))

(provide 'muse-backlink)
;;; muse-backlink.el ends here
