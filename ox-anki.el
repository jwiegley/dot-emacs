;;; ox-anki.el --- Org Exporter to Anki Flashcards
;;
;; Filename: ox-anki.el
;; Author: Vitalie Spinu
;; Maintainer: Vitalie Spinu
;; Copyright (C) 2014, Vitalie Spinu, all rights reserved
;; Version: 1.0
;; URL: https://github.com/vitoshka/ox-anki
;; Keywords: org, anki, outlines, flashcards
;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This file is *NOT* part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;  See https://github.com/vitoshka/ox-anki for how to install and use.
;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'ox)
(require 'ox-html)

(org-export-define-derived-backend 'anki 'html
  :translate-alist '((headline . org-anki-headline)
                     (section . org-anki-section)
                     (template . nil)
                     (inner-template . nil))
;;  :filters-alist '((:filter-parse-tree . org-anki-replicate-headlines))
  :menu-entry
  '(?a "Export to Anki"
       ((?b "As tab separated Buffer" org-anki-export-to-buffer)
	(?f "As tab separated File" org-anki-export-to-file))))

;; (defun org-anki-replicate-headlines (tree backend info)
;;   "Linearize (replicate) headers up to
;;   `org-export-headline-levels'."
;;   (let ((level 1))
;;    (dolist (el (cdr tree))
;;      (if (eq 'headline (org-element-type el))
;;          (org-anki--replicate-headline el)))
;;    tree))

;; (defun org-anki--copy-element (element)
;;   (let ((new (copy-sequence element)))
;;     ;; (org-element-put-property new :parent nil)
;;     new))

;; (defun org-anki--replicate-headline (headline)
;;   (let ((new-h (org-anki--copy-element headline)))
;;     (org-element-set-contents new-h))
;;   (let ((tt (dolist (h (cddr headline))
;;               (when (eq 'headline (org-element-type h))
;;                 (let ((new-h1 (org-anki--copy-element new-h)))
;;                   (apply #'org-element-set-contents new-h1
;;                          (org-element-contents new-h1 ))
;;                   (org-anki--copy-element h))))))))

(defun org-anki-headline (headline contents info)
  "Transcode a HEADLINE element from Org to Anki csv format.
CONTENTS holds the contents of the headline.  INFO is a plist
holding contextual information.

High level headlines up to `org-export-headline-levels' (see also
`org-export-low-level-p') are merged into an Anki question."
  ;; Simplified version of `org-html-headline'.
  (setq contents (or contents ""))

  (let ((level (org-export-get-relative-level headline info))
        (numberedp (org-export-numbered-headline-p headline info))
        ;; Create the headline text.
        (full-text
         (substring-no-properties
          (replace-regexp-in-string
           "\n" "" (org-export-data (org-element-property :title headline) info)))))
    (cond
     ;; Case 1: This is a footnote section: ignore it.
     ((org-element-property :footnote-section-p headline) nil)
     ;; Case 2. This is a deep sub-tree: export it as a list item.
     ((org-export-low-level-p headline info)
      ;; Build the real contents of the sub-tree.
      (let* ((type (if numberedp 'ordered 'unordered))
	     (itemized-body (org-html-format-list-item
			     contents type nil info nil full-text)))
	(concat
	 (and (org-export-first-sibling-p headline info)
	      (org-html-begin-plain-list type))
	 itemized-body
	 (and (org-export-last-sibling-p headline info)
	      (org-html-end-plain-list type)))))
     ;; Case 3. Standard headline.  Export it as a section.
     (t
      (let* ((last-child-level (plist-get info :last-child-level))
             (last-child (or (null last-child-level)
                             (eq last-child-level level))))
        (unless last-child-level
          (plist-put info :last-child-level level))
        (let ((front (concat full-text "\t"
                             (unless last-child-level
                               (make-string
                                (max 0 (- org-export-headline-levels level)) ?\t)))))
          (when (= level 1)
            (plist-put info :last-child-level nil))
          ;; all this mambo jambo is for replilcation of parent headlines across
          ;; the last-child headline that contains the answer
          (if last-child
              (propertize
               (concat (when (= level 1)
                         (concat (org-element-property :ID headline) "\t"))
                       front
                       (replace-regexp-in-string "\n+" "<br>" contents)
                       (when (not (= level 1)) "!@@!"))
               :aid (org-element-property :ID headline))
            (mapconcat (lambda (x)
                         (replace-regexp-in-string
                          "\n+" "<br>"
                          (if (= level 1)
                              (concat (get-text-property (1- (length x)) :aid x) "\t" front x)
                            (propertize (concat front x)
                                        :aid (get-text-property 1 :aid x)))))
                       (split-string contents "!@@!\n*" t)
                       "\n"))))))))

(defun org-anki-section (section contents info)
  "As `org-html-section' but drop white space strings."
  (unless (string-match-p "\\`[ \t\n]*\\'" contents)
    (org-html-section section contents info)))

(defun org-anki--add-UID-maybe ()
  (let ((el (org-element-at-point)))
    (when (and (eq (org-element-type el) 'headline)
               (not (org-element-property :ID el))
               (<= (org-element-property :level el)
                   org-export-headline-levels))
      ;; fixme: last child would be enough, but how to find it?
      (org-id-get-create)
      (forward-line))))

;;;###autoload
(defun org-anki-export-to-buffer
  (&optional async subtreep visible-only ext-plist)
  "Export current buffer to an Anki buffer.

If narrowing is active in the current buffer, only export its
narrowed part.

If a region is active, export that region.

A non-nil optional argument ASYNC means the process should happen
asynchronously.  The resulting buffer should be accessible
through the `org-export-stack' interface.

When optional argument SUBTREEP is non-nil, export the sub-tree
at point, extracting information from the headline properties
first.

When optional argument VISIBLE-ONLY is non-nil, don't export
contents of hidden elements.

EXT-PLIST, when provided, is a property list with external
parameters overriding Org default settings, but still inferior to
file-local settings.

Export is done in a buffer named \"*Org Anki Export*\", which
will be displayed when `org-export-show-temporary-export-buffer'
is non-nil."
  (interactive)
  (org-map-entries #'org-anki--add-UID-maybe)
  (org-export-to-buffer 'anki "*Org Anki Export*"
    async subtreep visible-only 'body-only ext-plist 'html-mode))

;;;###autoload
(defun org-anki-export-to-file
  (&optional async subtreep visible-only ext-plist)
  "Export current buffer to a Anki file.

If narrowing is active in the current buffer, only export its
narrowed part.

If a region is active, export that region.

A non-nil optional argument ASYNC means the process should happen
asynchronously.  The resulting file should be accessible through
the `org-export-stack' interface.

When optional argument SUBTREEP is non-nil, export the sub-tree
at point, extracting information from the headline properties
first.

When optional argument VISIBLE-ONLY is non-nil, don't export
contents of hidden elements.

EXT-PLIST, when provided, is a property list with external
parameters overriding Org default settings, but still inferior to
file-local settings.

Return output file's name."
  (interactive)
  (let* ((file (org-export-output-file-name ".anki" subtreep))
	 (org-export-coding-system org-html-coding-system))
    (org-map-entries #'org-anki--add-UID-maybe)
    (org-export-to-file 'anki file
      async subtreep visible-only 'body-only ext-plist)))

(provide 'ox-anki)
