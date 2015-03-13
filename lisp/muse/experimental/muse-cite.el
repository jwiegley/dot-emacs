;;; muse-cite.el --- smart citations for Muse

;; Copyright (C) 2005 Free Software Foundation, Inc.

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

;; This file is currently in experimental state.  I found it in an old
;; pre-release version of Muse and thought it might come in handy.

;;; Contributors:

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse Smart Citations
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Commentary:

;; If a footnote is of the general form "AUTHOR, TITLE, PAGES", this
;; module offers a function to more intelligently markup such
;; citations.  For LaTeX, it italicizes the TITLE and inserts correct
;; spacing and endashes in PAGES.  For HTML, it is able to convert the
;; TITLE or PAGES into a link, given knowledge of where to find known
;; texts by certain authors.
;;
;; To use this module -- since it only rewrites markup, and is not
;; particular to any style -- modify `muse-before-publish-hook':
;;
;;   (require 'muse-publish)
;;   (require 'muse-cite)
;;   (add-hook 'muse-before-publish-hook 'muse-cite-munge-footnotes)

(require 'muse-publish)

(defgroup muse-cite nil
  "Offers functionality for marking up smart citations."
  :group 'muse-publish)

(defcustom muse-cite-titles nil
  "An alist of authors and the titles they've written.
This is how titles are recognized, and marked up as links to the
title and to the specific pages referenced.

This variable is an alist of the form:

  ((AUTHOR . TITLE-LIST)
   ...)

Where AUTHOR is a string, and TITLE-LIST is a list of the form:

  ((TITLE URL [PAGE-URL])
   ...)

Where TITLE is a string, URL is a URL string, and PAGE-URL can be
nil or a URL string with %d somewhere in it -- which is substituted
with the first page number mentioned in the reference."
  :type '(alist :key-type (string :tag "Author")
                :value-type
                (repeat (list (string :tag "Title")
                              (string :tag "URL")
                              (choice (string :tag "Page URL")
                                      (const :tag "No Page URL" nil)))))
  :group 'muse-cite)

(defun muse-cite-rewrite (citation)
  "Rewrite an 'Author, Title, Pages' CITATION as an intelligent reference."
  (when (string-match
         (concat "\\([^,]+\\), *\\([^,]+\\), *"
                 "\\(pp?\\.  *\\([0-9]+\\)\\(-+[0-9]+\\)?\\)") citation)
    (let* ((author (match-string 1 citation))
           (title (match-string 2 citation))
           (pages (match-string 3 citation))
           (page (match-string 4 citation))
           (author-entry (assoc author muse-cite-titles))
           (book-entry (and author-entry
                            (assoc title (cdr author-entry))))
           (book-url (car (cdr book-entry)))
           (book-page (car (cddr book-entry))))
      (cond
       ((null book-url)
        (format "%s, *%s*, %s" author title pages))
       ((or (null book-page)
            (not (string-match "%d" book-page)))
        (format "%s, [[%s][%s]], %s" author book-url title pages))
       (t
        (setq book-page (replace-match page nil t book-page))
        (format "%s, [[%s][%s]], [[%s][%s]]"
                author book-url title book-page pages))))))

(defun muse-cite-munge-footnotes ()
  "Munge the footnote citations in the current buffer.
The author/title definitions given in `muse-cite-titles' are used
to change the citations automagically into hyperlinks.."
  (goto-char (point-max))
  (when (re-search-backward "^Footnotes" nil t)
    (while (re-search-forward "^\\[[0-9]+\\][ \t]+\\(.+\\)" nil t)
      (let ((end (copy-marker (match-end 0) t))
            (rewrite (save-match-data
                       (muse-cite-rewrite (match-string 1)))))
        (when rewrite
          (goto-char (match-beginning 1))
          (delete-region (match-beginning 1) (match-end 1))
          (insert rewrite))
        (goto-char end))))
  nil)

(provide 'muse-cite)

;;; muse-cite.el ends here
