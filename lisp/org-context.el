;;; org-context --- Functions to preserve refiling context

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 30 Oct 2024
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

;; I configure this package as follows:
;;
;;   (use-package org-context
;;     :after org
;;     :demand t
;;     :bind (:map org-mode-map ("C-c C-x R" . org-context-undo))
;;     :config
;;     (org-context-install))
;;
;; Now you can customize `org-context-save-info' to decide which details about
;; the refiling context are saved (time and olpath are requried), which then
;; gives you the freedom to "un-refile" and "un-archive" entries back to their
;; source locations.
;;
;; Also see `org-context-record-predicate' to customize when refiling context
;; is saved. By default, it is not saved when refiling from a group named
;; "Inbox", or when refiling to unarchive an item.

(require 'org)
(require 'org-refile)
(require 'org-archive)
(require 'cl-lib)

(defgroup org-context nil
  "Functions to save item context and restore them to that context."
  :tag "Org-context"
  :group 'org)

(defcustom org-context-save-info
  '(time file olpath olid category todo itags)
  "See `org-archive-save-context-info'."
  :group 'org-context
  :type '(set :greedy t
	      (const :tag "Time" time)
	      (const :tag "File" file)
	      (const :tag "Category" category)
	      (const :tag "TODO state" todo)
	      (const :tag "Priority" priority)
	      (const :tag "Inherited tags" itags)
	      (const :tag "Outline path" olpath)
	      (const :tag "Outline ID" olid)
	      (const :tag "Local tags" ltags)))

(defcustom org-context-record-predicate
  (lambda (context)
    (not (or (string= "Inbox" (cdr (assq 'olpath context)))
             (org-entry-get (point) "ARCHIVE_FILE"))))
  "With point at entry, return non-nil if refile context should be save.
This function receives the context to be stored as an argument."
  :group 'org-context
  :type '(function))

(defvar org-context-last-saved nil)

(defun org-context-tag (&optional where)
  "Return string prefix of the context identified by WHERE."
  (cond
   ((or (null where) (eq where 'current)) nil)
   ((eq where 'refile) "REFILE")
   ((eq where 'archive) "ARCHIVE")
   (t where)))

(defun org-context-get (&optional where)
  "Retrieve context of the current entry.
WHERE can be any of the following:

`current'
	Current context, independent of where has been saved
`refile'
	Previously saved refile context (where it was refiled from)
`refile'
	Previously saved archive context (where it was archived from)
<string>
	Context saved under properties beginning with `<string>_`
"
  (let ((tag (org-context-tag where)))
    (if tag
        `((category . ,(org-entry-get (point) (concat tag "_CATEGORY")))
	  (file     . ,(org-entry-get (point) (concat tag "_FILE")))
	  (itags    . ,(org-entry-get (point) (concat tag "_ITAGS")))
	  (ltags    . ,(org-entry-get (point) (concat tag "_LTAGS")))
	  (olpath   . ,(org-entry-get (point) (concat tag "_OLPATH")))
	  (olid     . ,(org-entry-get (point) (concat tag "_OLID")))
	  (time     . ,(org-entry-get (point) (concat tag "_TIME")))
	  (todo     . ,(org-entry-get (point) (concat tag "_TODO"))))
      (let* ((all-tags (org-get-tags))
	     (local-tags
	      (cl-remove-if #'(lambda (tag) (get-text-property 0 'inherited tag))
			    all-tags))
	     (inherited-tags
	      (cl-remove-if-not #'(lambda (tag) (get-text-property 0 'inherited tag))
				all-tags)))
        `((category . ,(org-get-category nil 'force-refresh))
	  (file     . ,(abbreviate-file-name
	                (or (buffer-file-name (buffer-base-buffer))
	                    (error "No file associated to buffer"))))
	  (itags    . ,(mapconcat #'identity inherited-tags " "))
	  (ltags    . ,(mapconcat #'identity local-tags " "))
	  (olpath   . ,(org-format-outline-path (org-get-outline-path)))
	  (olid     . ,(org-with-wide-buffer
                        (and (org-up-heading-safe)
	                     (org-entry-get (point) "ID"))))
	  (time     . ,(format-time-string
                        (org-time-stamp-format 'with-time 'no-brackets)))
	  (todo     . ,(org-entry-get (point) "TODO")))))))

(defun org-context-show-olpath (&optional where)
  (interactive)
  (let ((context (org-context-get where)))
    (message "%s :: %s" (cdr (assq 'file context)) (cdr (assq 'olpath context)))))

(defun org-context--save-before-refile (&rest _)
  "Helper function used to save context before `org-refile'."
  (setq org-context-last-saved
        (let ((context (org-context-get)))
          (when (funcall org-context-record-predicate context)
            context))))

(defun org-context-put (where context)
  "Given a context, record it under the given properties.
See `org-context-get' for information on the WHERE parameter."
  (let ((tag (org-context-tag where)))
    (when tag
      (dolist (item org-context-save-info)
        (let ((value (cdr (assq item context))))
          (when (org-string-nw-p value)
	    (org-entry-put
	     (point)
	     (concat tag "_" (upcase (symbol-name item)))
	     value)))))))

(defun org-context--put-last-saved ()
  "Record the last saved refiling context."
  (when org-context-last-saved
    (org-context-put 'refile org-context-last-saved)
    (setq org-context-last-saved nil)))

(defun org-context-delete (where)
  "Remove the given context from the entry at POS (or point if nil).
See `org-context-get' for information on the WHERE parameter."
  (let ((tag (org-context-tag where)))
    (when tag
      (dolist (item org-context-save-info)
        (org-entry-delete
	 (point)
	 (concat tag "_" (upcase (symbol-name item))))))))

(defmacro org-context-aif (cond then &rest else)
  (declare (debug t) (indent 2))
  `(let ((it ,cond))
     (if it ,then ,@else)))

(defun org-context-restore (&optional where)
  "Restore item to its original context, clearing that saved context.
See `org-context-get' for information on the WHERE parameter."
  (interactive)
  (let* ((context (org-context-get where))
         (file (cdr (assq 'file context)))
         (olpath (cdr (assq 'olpath context)))
         (olid (cdr (assq 'olid context)))
         (args
          (cond
           (olid
            (org-context-aif (org-id-find olid)
                (cl-destructuring-bind (path . pos)
                    it
                  (list olpath path nil pos))
              (error "No Org-mode entry with ID %s" olid)))
           ((and file olpath)
            (org-context-aif
                (with-current-buffer
                    (find-file-noselect file)
                  (org-find-olp
                   (cons file (split-string olpath "/"))))
                (list olpath file nil it)
              (error "No Org-mode entry at path %s in file %s"
                     olpath file))))))
    (when args
      (org-context-delete where)
      (org-refile nil nil args)
      t)))

(defun org-context-undo-refile ()
  "Restore a refiled item to where it was refiled from."
  (interactive)
  (org-context-restore 'refile))

(defun org-context-undo-archive ()
  "Restore an archived item to where it was archived from."
  (interactive)
  (org-context-restore 'archive))

(defun org-context-undo ()
  "Restore an archived or refiled item to where it came from.
This requires that the context was previously saved. Use
`org-context-install' to ensure that context is recorded when
items are refiled."
  (interactive)
  (or (org-context-undo-archive)
      (org-context-undo-refile)))

(defun org-context-install ()
  "Install helper functions and advice to enable `org-context' to work."
  ;; Ensure that details necessary to the functioning of this module are
  ;; always present.
  (add-to-list 'org-archive-save-context-info 'file)
  (add-to-list 'org-archive-save-context-info 'olpath)
  (add-to-list 'org-context-save-info 'file)
  (add-to-list 'org-context-save-info 'olpath)

  ;; Save refiling context just before refiling is done.
  (advice-add 'org-refile :before #'org-context--save-before-refile)

  ;; After an entry is refiled, store any saved refiling context at the new
  ;; position.
  (add-hook 'org-after-refile-insert-hook #'org-context--put-last-saved))

(provide 'org-context)
