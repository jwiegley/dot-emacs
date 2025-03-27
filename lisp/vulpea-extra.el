;;; vulpea-extra --- Extra functions for use with vulpea

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 24 Jan 2025
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

(require 'cl-lib)
(eval-when-compile
  (require 'cl))

(require 'org)
(require 'org-ql)
(require 'org-roam)
(require 'org-roam-db)
(require 'org-roam-dailies)
(require 'dash)
(require 'vulpea)

(declare-function org-with-wide-buffer "org-macs")
(declare-function org-delete-all "org-macs")

(defun vulpea-buffer-p ()
  "Return non-nil if the currently visited buffer is a note."
  (and buffer-file-name
       (eq major-mode 'org-mode)
       (string-suffix-p "org" buffer-file-name)
       (string-prefix-p
        (file-truename
         (expand-file-name
          (file-name-as-directory org-roam-directory)))
        (file-truename
         (expand-file-name
          (file-name-directory buffer-file-name))))))

(defun vulpea-buffer-project-p ()
  "Return non-nil if current buffer has any todo entry.

TODO entries marked as done are ignored, meaning the this
function returns nil if current buffer contains only completed
tasks. The only exception is headings tagged as REFILE."
  (save-excursion
    (goto-char (point-min))
    (let (case-fold-search)
      (re-search-forward "\\* \\(TODO\\|DOING\\|WAIT\\|DEFER\\|TASK\\|HABIT\\)" nil t)))
  ;; (org-element-map
  ;;     (org-element-parse-buffer 'element)
  ;;     '(headline inlinetask)
  ;;   (lambda (h)
  ;;     (let ((todo-type (org-element-property :todo-type h)))
  ;;       (or
  ;;        (eq 'todo todo-type)
  ;;        ;; any non-todo headline with an active timestamp
  ;;        ;; (and
  ;;        ;;  (not (eq 'done todo-type))
  ;;        ;;  (org-element-property :contents-begin h)
  ;;        ;;  (save-excursion
  ;;        ;;    (goto-char (org-element-property :contents-begin h))
  ;;        ;;    (let ((end (save-excursion
  ;;        ;;                 ;; we must look for active timestamps only
  ;;        ;;                 ;; before then next heading, even if it's
  ;;        ;;                 ;; child, but org-element-property
  ;;        ;;                 ;; :contents-end includes all children
  ;;        ;;                 (or
  ;;        ;;                  (re-search-forward org-element-headline-re
  ;;        ;;                                     (org-element-property :contents-end h)
  ;;        ;;                                     ':noerror)
  ;;        ;;                  (org-element-property :contents-end h)))))
  ;;        ;;      (re-search-forward org-ts-regexp end 'noerror))))
  ;;        )))
  ;;   nil 'first-match)
  )

(defun vulpea-project-list ()
  "Return a list of note files containing 'todo' tag." ;
  (seq-uniq
   (seq-map
    #'car
    (org-roam-db-query
     [:select [nodes:file]
              :from tags
              :left-join nodes
              :on (= tags:node-id nodes:id)
              :where (like tag (quote "%\"todo\"%"))]))))

(defun vulpea-ensure-filetag ()
  "Add missing FILETAGS to the current note."
  (when (save-excursion
          (goto-char (point-min))
          (looking-at ":"))
    (let* ((file (buffer-file-name))
           (path-tags
            (when file
              (seq-filter
               (lambda (x) (not (string-empty-p x)))
               (split-string
                (string-remove-prefix
                 (file-truename
                  (expand-file-name org-roam-directory))
                 (file-truename
                  (expand-file-name (file-name-directory file))))
                "/"))))
           (original-tags (vulpea-buffer-tags-get))
           (tags (append original-tags path-tags)))

      ;; process projects
      (if (vulpea-buffer-project-p)
          (setq tags (cons "todo" tags))
        (setq tags (remove "todo" tags)))

      (setq tags (seq-uniq tags))

      ;; update tags if changed
      (when (or (seq-difference tags original-tags)
                (seq-difference original-tags tags))
        (apply #'vulpea-buffer-tags-set (seq-uniq tags))))))

(defun vulpea-ensure-all-filetags ()
  (interactive)
  (dolist (file (org-roam-list-files))
    (message "processing %s" file)
    (with-current-buffer
        (or (find-buffer-visiting file)
            (find-file-noselect file))
      (vulpea-ensure-filetag)
      (save-buffer))))

(defun vulpea-update-agenda-files (&rest _)
  "Update the value of `org-agenda-files'."
  (interactive)
  (setq org-agenda-files (vulpea-project-list)))

;;;###autoload
(defun vulpea-pre-save-hook ()
  "Do all the dirty stuff when file is being saved."
  (when (and (not (active-minibuffer-window))
             (vulpea-buffer-p))
    (vulpea-ensure-filetag)))

(defun vulpea-auto-update-install ()
  (add-hook 'before-save-hook #'vulpea-pre-save-hook)

  (advice-add 'org-agenda :before #'vulpea-update-agenda-files)
  (advice-add 'org-todo-list :before #'vulpea-update-agenda-files))

(defun vulpea-find-journal-by-directory ()
  (interactive)
  (let ((vulpea-select-describe-fn
         #'(lambda (note)
             (concat
              (vulpea-note-title note)
              " on "
              (format-time-string
               "%Y-%m-%d"
               (org-encode-time
                (org-parse-time-string
                 (cdr (assoc "CREATED" (vulpea-note-properties note)))))))))
        (vulpea-select-annotate-fn
         #'(lambda (note)
             (let* ((tags-str (mapconcat
                               (lambda (x) (concat "#" x))
                               (delete "todo"
                                       (vulpea-note-tags note))
                               " ")))
               (if (string-empty-p tags-str)
                   ""
                 (concat " " tags-str)))))
        vertico-sort-function)
    (vulpea-find
     :require-match t
     :candidates-fn
     #'(lambda (filter)
         (seq-sort-by
          #'(lambda (note)
              (org-encode-time
               (org-parse-time-string
                (cdr (assoc "CREATED" (vulpea-note-properties note))))))
          #'time-greater-p
          (vulpea-db-query filter)))
     :filter-fn
     #'(lambda (note)
         ;; primary-title is set only when title is one of the
         ;; aliases
         (and (= (vulpea-note-level note) 0)
              (string-match "/journal/" (vulpea-note-path note)))))))

(defsubst vulpea-note-created-time (note)
  (org-encode-time
   (org-parse-time-string
    (cdr (assoc "CREATED" (vulpea-note-properties note))))))

(defsubst vulpea-note-date-time (note)
  (org-encode-time
   (org-parse-time-string
    (or (caar (vulpea-note-file-date note))
        (cdr (assoc "CREATED" (vulpea-note-properties note)))))))

(defsubst vulpea-note-file-date (note)
  (org-roam-db-query
   [:select [note-date] :from file-dates
            :where (= note-id $s1)]
   (vulpea-note-id note)))

;;;###autoload
(defun vulpea-extra-db-setup-dates ()
  "Setup dates table in Vulpea DB."
  (vulpea-db-define-table
   ;; name
   'file-dates
   ;; version
   1
   ;; schema
   '([(note-id :unique :primary-key)
      note-date]
     ;; useful to automatically cleanup your table whenever a note/node/file is removed
     (:foreign-key [note-id] :references nodes [id] :on-delete :cascade))
   ;; index
   '((note-date-id-index [note-id])))

  ;; (add-hook 'vulpea-db-insert-note-functions #'vulpea-extra-db-insert-date)
  (advice-add 'org-roam-db-insert-file-node :after #'vulpea-extra-db-insert-date))

(defun vulpea-extra-db-insert-date ()
  (let ((path (buffer-file-name (buffer-base-buffer)))
        (id (org-id-get)))
    (message "Determing date info for: %s" path)
    (org-roam-db-query
     [:delete :from file-dates :where (= note-id $s1)] id)
    (when-let ((str (vulpea-buffer-prop-get "date")))
      (org-roam-db-query!
       (lambda (err)
         (lwarn 'org-roam :warning "%s for date '%s' in %s (%s)"
                (error-message-string err)
                str
                path
                id))
       [:insert :into file-dates :values $v1]
       (vector id (org-read-date nil nil str))))))

(defun vulpea-extra-db-insert-date-every (note)
  ;; (message "Determing date info for: %s" (vulpea-note-path note))
  (org-roam-db-query
   [:delete :from file-dates
            :where (= note-id $s1)]
   (vulpea-note-id note))
  (vulpea-utils-with-note note
    (when-let ((str (vulpea-buffer-prop-get "date")))
      (org-roam-db-query!
       (lambda (err)
         (lwarn 'org-roam :warning "%s for date '%s' in %s (%s) %s"
                (error-message-string err)
                str
                (vulpea-note-title note)
                (vulpea-note-id note)
                (vulpea-note-path note)))
       [:insert :into file-dates
                :values $v1]
       (vector (vulpea-note-id note)
               (org-read-date nil nil str))))))

(defun vulpea-find-journal ()
  (interactive)
  (let ((vulpea-select-describe-fn
         #'(lambda (note)
             (concat (vulpea-note-title note)
                     " on "
                     (format-time-string
                      "%Y-%m-%d"
                      (vulpea-note-date-time note)))))
        (vulpea-select-annotate-fn
         #'(lambda (note)
             (let* ((tags-str
                     (mapconcat
                      (lambda (x) (concat "#" x))
                      (org-delete-all '("todo"
                                        "meeting"
                                        "assembly")
                                      (vulpea-note-tags note))
                      " ")))
               (if (string-empty-p tags-str)
                   ""
                 (concat " " tags-str)))))
        vertico-sort-function)
    (vulpea-find
     :require-match t
     :candidates-fn
     #'(lambda (filter)
         (seq-filter filter
                     (seq-sort-by
                      #'vulpea-note-date-time
                      #'time-greater-p
                      (vulpea-db-query-by-tags-some
                       '("meeting" "assembly")))))
     :filter-fn
     #'(lambda (note)
         (and (= (vulpea-note-level note) 0)
              (string-match "/\\(meeting\\|assembly\\)/"
                            (vulpea-note-path note)))))))

;;;###autoload
(defun vulpea-tags-add ()
  "Add a tag to current note."
  (interactive)
  (org-with-point-at 1
    (when (call-interactively #'org-roam-tag-add)
      (vulpea-ensure-filetag))))

;;;###autoload
(defun vulpea-tags-delete ()
  "Delete a tag from current note."
  (interactive)
  (call-interactively #'org-roam-tag-remove))

;;;###autoload
(defun vulpea-alias-add ()
  "Add an alias to current note."
  (interactive)
  (call-interactively #'org-roam-alias-add))

;;;###autoload
(defun vulpea-alias-delete ()
  "Delete an alias from current note."
  (interactive)
  (call-interactively #'org-roam-alias-remove))

(provide 'vulpea-extra)
