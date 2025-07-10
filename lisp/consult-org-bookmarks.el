;;; consult-org-bookmarks.el --- Consult all links with URL properties

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 7 Jul 2025
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

;;; Code:

(require 'cl-lib)
(require 'org-ql)
(require 'consult)

(defun consult-org-bookmarks-collect-links ()
  "Collect links in properties named URL, URL2, etc., in Org agenda files.
This applies to either LINK todo items, or items with a :LINK: tag."
  (let ((items
         (org-ql-select (org-agenda-files)
           '(or (todo "LINK") (tags "LINK"))
           :action
           (lambda ()
             (cl-loop for (key . val) in (org-entry-properties)
                      when (string-match-p "^URL[0-9]*$" key)
                      collect (cons val (org-get-heading t t t t))))))
        results)
    ;; Flatten and format results as Org links
    (dolist (item items)
      (let ((url (caar item))
            (title (cdar item)))
        (setq results
              (cons (cons (format "[[%s][%s]]" url title) url) results))))
    (nreverse results)))

(defun consult-org-bookmarks ()
  "Consult interface for Org bookmarks with URL properties."
  (interactive)
  (when-let* ((candidates (consult-bookmarks-collect-org-links))
              (choice (consult--read
                       (mapcar #'car candidates)
                       :prompt "Org Bookmark: "
                       :require-match t)))
    (browse-url (cdr (assoc choice candidates)))))

(provide 'consult-org-bookmarks)

;;; consult-org-bookmarks.el ends here
