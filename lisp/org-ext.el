;;; org-ext --- Extra functions for use with Org-mode

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 9 Apr 2023
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
  (require 'cl)
  (require 'cl-macs))

(require 'rx)
(require 'org-constants)
(require 'org)
(require 'org-agenda)
(require 'org-ql)
(require 'dash)
(require 'simple)

(defconst org-ext-ts-regexp
  "[[<]\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} [^]>\r\n]*?\\)[]>]"
  "Regular expression for fast inactive time stamp matching.")

(declare-function org-with-wide-buffer "org-macs")

(defgroup org-ext nil
  "Extra functions for use with Org-mode"
  :group 'org)

(defalias 'org-ext-up-heading #'outline-up-heading)

(defun org-ext-goto-inbox-heading ()
  (set-buffer (get-buffer (file-name-nondirectory org-constants-todo-path)))
  (goto-char (point-min))
  (while (looking-at "^[:#]")
    (forward-line 1))
  (unless (looking-at "^$")
    (error "Missing blank line after file header in %s"
           (file-name-nondirectory org-constants-todo-path)))
  (forward-line 1)
  (unless (looking-at "^\\* Inbox$")
    (error "Missing Inbox heading at start of %s"
           (file-name-nondirectory org-constants-todo-path))))

(defun org-ext-goto-inbox (&optional func)
  (interactive)
  (with-current-buffer
      (funcall (if func
                   #'find-file-noselect
                 #'find-file)
               org-constants-todo-path)
    (if func
        (save-excursion
          (org-ext-goto-inbox-heading)
          (forward-line 1)
          (while (looking-at "^:")
            (forward-line 1))
          (funcall func))
      (org-ext-goto-inbox-heading)
      (forward-line 1)
      (while (looking-at "^:")
        (forward-line 1)))))

(defun org-ext-reformat-draft ()
  ;; If there is a URL, this is a LINK.
  (when (re-search-forward ":LOCATION:\\s-*0.0,.+\n" nil t)
    (delete-region (match-beginning 0) (match-end 0)))
  (when (re-search-forward "^\\(:URL:\\s-*\\)?\\(http.+?\\)\n?" nil t)
    (let ((url (match-string 2)))
      (delete-region (match-beginning 0) (match-end 0))
      (org-set-property "URL" url)
      (goto-char (point-min))
      (when (re-search-forward "SCHEDULED: .+\n")
        (delete-region (match-beginning 0) (match-end 0)))
      (goto-char (point-min))
      (when (re-search-forward " TODO ")
        (replace-match " LINK " nil nil nil 0))))
  ;; If there is a note tag, this is a NOTE.
  (goto-char (point-min))
  (when (re-search-forward
         ":TAGS:\\s-+.+?\\(\\<note\\>\\(,\\s-*\\)?\\|,\\s-*\\<note\\>$\\)" nil t)
    (delete-region (match-beginning 1) (match-end 1))
    (goto-char (point-min))
    (when (re-search-forward " TODO ")
      (replace-match " NOTE " nil nil nil 0))
    (goto-char (point-min))
    (when (re-search-forward "SCHEDULED: .+\n")
      (delete-region (match-beginning 0) (match-end 0))))
  ;; If there are no tags, delete that property.
  (goto-char (point-min))
  (when (re-search-forward ":TAGS:\\s-+\n" nil t)
    (delete-region (match-beginning 0) (match-end 0)))) 

(defun org-ext-fit-agenda-window ()
  "Fit the window to the buffer size."
  (and (memq org-agenda-window-setup '(reorganize-frame))
       (fboundp 'fit-window-to-buffer)
       (fit-window-to-buffer)))

(defadvice org-agenda (around fit-windows-for-agenda activate)
  "Fit the Org Agenda to its buffer and import any pending Drafts."
  (let ((notes
         (ignore-errors
           (directory-files "~/Drafts" t "[0-9].*\\.txt\\'" nil)))
        url)
    (when notes
      (org-ext-goto-inbox
       (lambda ()
         (dolist (note notes)
           (when (ignore-errors
                   (insert
                    (with-temp-buffer
                      (insert-file-contents note)
                      (goto-char (point-min))
                      (org-ext-reformat-draft)
                      (goto-char (point-max))
                      (unless (bolp)
                        (insert ?\n))
                      (buffer-string)))
                   t)
             (delete-file note t)))
         (when (buffer-modified-p)
           (save-buffer))))))
  ad-do-it
  (org-ext-fit-agenda-window))

(defun org-ext-agenda-show (&optional arg)
  "Display the Org file which contains the item at point."
  (interactive "P")
  (let ((win (selected-window)))
    (if (and (window-live-p org-agenda-show-window)
	     (eq this-command last-command))
	(progn
	  (select-window org-agenda-show-window)
	  (ignore-errors (scroll-up)))
      (org-agenda-goto)
      (org-fold-show-entry 'hide-drawers)
      (narrow-to-region (org-entry-beginning-position)
			(org-entry-end-position))
      (setq org-agenda-show-window (selected-window)))
    (select-window win)))

(defun org-ext-agenda-show-and-scroll-up (&optional arg)
  "Display the Org file which contains the item at point.

When called repeatedly, scroll the window that is displaying the buffer.

With a `\\[universal-argument]' prefix argument, display the item, but \
fold drawers."
  (interactive "P")
  (let ((win (selected-window)))
    (if (and (window-live-p org-agenda-show-window)
	     (eq this-command last-command))
	(progn
	  (select-window org-agenda-show-window)
	  (ignore-errors (scroll-up)))
      (org-agenda-goto t)
      (org-fold-show-entry 'hide-drawers)
      (if arg
          (org-with-wide-buffer
	   (narrow-to-region (org-entry-beginning-position)
			     (org-entry-end-position))
	   (org-fold-show-all '(drawers)))
	(org-cycle-hide-drawers 'children))
      (setq org-agenda-show-window (selected-window)))
    (select-window win)))

(defun org-ext-prep-window (wind)
  (select-window wind)
  (org-fit-window-to-buffer wind)
  (ignore-errors
    (window-resize
     wind
     (- 100 (window-width wind)) t)))

(defun org-ext-jump-to-agenda ()
  (interactive)
  (push-window-configuration)
  (let ((buf (or (get-buffer "*Org Agenda*")
                 (get-buffer "*Org Agenda(a)*"))))
    (if buf
        (let ((win (get-buffer-window buf)))
          (if win
              (progn
                (when (called-interactively-p 'any)
                  (funcall #'org-ext-prep-window win))
                (select-window win))
            (funcall #'org-ext-prep-window
                     (if (called-interactively-p 'any)
                         (display-buffer buf t t)
                       (display-buffer buf)))))
      (require 'org-agenda)
      (mapc #'find-file-noselect org-agenda-files)
      (call-interactively #'org-agenda-list)
      (org-agenda-filter '(64))
      (funcall #'org-ext-prep-window (selected-window)))))

(defun org-ext-agenda-redo (&optional all)
  (interactive)
  (org-agenda-redo all)
  (push-window-configuration)
  (let ((wind (selected-window)))
    (with-selected-window wind
      (org-fit-window-to-buffer wind)
      (ignore-errors
        (window-resize wind (- 100 (window-width wind)) t)))))

(defun org-ext-entire-properties-block ()
  "Return the entire properties block, inclusive of :PROPERTIES:...:END:."
  (save-excursion
    (org-back-to-heading)
    (let* ((entry-end (save-excursion
                        (outline-next-heading)
                        (point)))
           (beg (and (search-forward ":PROPERTIES:" entry-end t)
                     (match-beginning 0)))
           (end (and (re-search-forward ":END:\\s-*\n" entry-end t)
                     (match-end 0))))
      (cons beg end))))

(defun org-ext-move-properties-drawer ()
  "Move the PROPERTIES drawer to its proper location.
Returns nil if nothing was moved, otherwise it returns point
after :END:."
  (interactive)
  (save-excursion
    (org-back-to-heading-or-point-min)
    (let* ((beg (point))
           (end (save-excursion
                  (org-next-visible-heading 1)
                  (point)))
           (before-sha (sha1 (buffer-substring-no-properties beg end)))
           (modified (buffer-modified-p)))
      (save-restriction
        (narrow-to-region beg end)
        (pcase (org-ext-entire-properties-block)
          (`(,beg . ,end)
           (let ((entries-block (buffer-substring beg end)))
             (delete-region beg end)
             ;; Create a new properties block
             (org-get-property-block nil 'force)
             (pcase (org-ext-entire-properties-block)
               (`(,new-beg . ,new-end)
                (goto-char new-beg)
                (delete-region new-beg new-end)
                (insert entries-block)))))
          (_ nil))
        (if (equal before-sha (sha1 (buffer-substring-no-properties beg end)))
            (set-buffer-modified-p modified))))))

(defun org-ext-fix-all-properties ()
  (interactive)
  (while (re-search-forward "^\\*" nil t)
    (ignore-errors
      (org-ext-move-properties-drawer))
    (forward-line 1)))

(defun org-ext-update-date-field ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^#\\+date:\\s-*\\(.+\\)" nil t)
      (delete-region (match-beginning 1) (match-end 1))
      (org-insert-time-stamp (current-time) t t))))

(defun org-ext-reformat-time (&optional beg end)
  (interactive "r")
  (let ((date-string (buffer-substring beg end)))
    (save-excursion
      (goto-char beg)
      (delete-region beg end)
      (insert
       (format-time-string
        (org-time-stamp-format 'long 'inactive)
        (org-encode-time (parse-time-string date-string)))))))

(defun org-ext-todoize (&optional arg)
  "Add standard metadata to a headline.
With `C-u', regenerate ID even if one already exists.
With `C-u C-u', set the keyword to TODO, without logging.
If the headline title end with a (HH:MM) style time offset, this
text will be moved into an OFFSET property."
  (interactive "P")
  (save-excursion
    (goto-char (line-beginning-position))
    (when (re-search-forward " (\\([0-9:]+\\))" (line-end-position) t)
      (let ((offset (match-string 1)))
        (delete-region (match-beginning 0) (match-end 0))
        (org-entry-put (point) "OFFSET" offset))))
  (when (equal arg '(16))
    (let ((org-inhibit-logging t))
      (org-todo "TODO")))
  (run-hooks 'org-capture-before-finalize-hook))

(defun org-ext-switch-todo-link (&optional arg)
  "Switch a LINK to a TODO with a LINK tag, and vice-versa."
  (interactive "P")
  (let ((org-inhibit-logging t))
    (if (member "LINK" (org-get-tags))
        (progn
          (org-set-tags (delete "LINK" (org-get-tags)))
          (org-todo "LINK"))
      (org-todo "TODO")
      (org-set-tags (delete-dups (cons "LINK" (org-get-tags)))))))

(defun org-ext-todoize-region (&optional beg end arg)
  "Add standard metadata to headlines in region.
See `org-ext-todoize'."
  (interactive "r\nP")
  (save-excursion
    (goto-char beg)
    (let ((end-marker (copy-marker end)))
      (while (< (point) end-marker)
        (goto-char (line-end-position))
        (org-ext-todoize arg)
        (ignore-errors
          (org-next-visible-heading 1))))))

(defvar org-ext-property-search-name nil)

(defun org-ext-with-property-search (property value)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive
   (list (setq org-ext-property-search-name (org-read-property-name))
         (completing-read "Value: "
                          (org-property-values org-ext-property-search-name))))
  (let ((org-use-property-inheritance
         (append org-use-property-inheritance '("WITH"))))
    (org-tags-view
     t (format "%s={%s}&TODO={TODO\\|WAIT\\|TASK}" property value))))

(defun org-ext-created-from-stamp ()
  (interactive)
  (let* ((name (file-name-nondirectory (buffer-file-name)))
         (year (string-to-number (substring name 0 4)))
         (mon (string-to-number (substring name 4 6)))
         (day (string-to-number (substring name 6 8))))
    (org-entry-put (point) "CREATED"
                   (with-temp-buffer
                     (org-insert-time-stamp
                      (org-encode-time (list 0 0 0 day mon year)) nil t)
                     (buffer-string)))))

(defun org-ext-insert-structure-template-and-yank (type)
  (interactive
   (list (pcase (org--insert-structure-template-mks)
	   (`("\t" . ,_) (read-string "Structure type: "))
	   (`(,_ ,choice . ,_) choice))))
  (org-insert-structure-template type)
  (yank))

(defun org-ext-parent-priority ()
  (save-excursion
    (org-up-heading-safe)
    (save-match-data
      (beginning-of-line)
      (and (looking-at org-heading-regexp)
	   (org-get-priority (match-string 0))))))

(defsubst org-ext-agenda-files-except (&rest args)
  (cl-set-difference org-agenda-files args))

(defun org-ext-entry-get-immediate (property)
  (save-excursion
    (let ((local (org--property-local-values property nil)))
      (and local (mapconcat #'identity
                            (delq nil local)
                            (org--property-get-separator property))))))

(defsubst org-ext-category-p ()
  "A category is any heading that has a CATEGORY property."
  (not (null (org-ext-entry-get-immediate "CATEGORY"))))

(defun org-ext--first-child-todo (&optional pred)
  (save-excursion
    (when (org-goto-first-child)
      (cl-loop for loc = (or (and (org-entry-is-todo-p)
                                  (or (null pred) (funcall pred))
                                  (point))
                             (org-ext--first-child-todo))
               if loc
               do (throw 'has-child-todo loc)
               while (org-get-next-sibling)))))

(defsubst org-ext-first-child-todo (&optional pred)
  (catch 'has-child-todo (org-ext--first-child-todo pred)))

(defsubst org-ext-project-p ()
  "A project is any open todo that has child tasks at any level."
  (and (org-entry-is-todo-p)
       (not (null (org-ext-first-child-todo)))))

(defsubst org-ext-top-level-project-p ()
  "A top-level project is not the child of another project."
  (and (org-ext-project-p)
       (not (org-ext-subtask-p))))

(defun org-ext-subtask-p ()
  "A subtask is any open todo that is a child of another open todo.
This is true even if there are intervening categories or other headings."
  (and (org-entry-is-todo-p)
       (save-excursion
         (cl-loop while (org-up-heading-safe)
                  if (org-entry-is-todo-p) return t))))

(defalias 'org-ext-task-p #'org-entry-is-todo-p)

(defalias 'org-ext-habit-p #'org-is-habit-p)

(defun org-ext-has-preceding-todo-p ()
  (let ((here (point)))
    (save-excursion
      (when (org-up-heading-safe)
        (let ((first-child (and (org-ext-task-p)
                                (org-ext-first-child-todo))))
          (and first-child
               (or (/= first-child here)
                   (org-ext-has-preceding-todo-p))))))))

(defun org-ext-agenda-files-but-not-meetings ()
  (cl-delete-if
   (apply-partially #'string-match-p
                    "/\\(meeting\\|local-spiritual-assembly\\)/")
   (org-agenda-files)))

(defun org-ext-team-files ()
  (directory-files (expand-file-name "kadena/team" org-directory)
                   t "\\.org\\'"))

(defun org-ext-refine-refile-targets (orig-func &optional default-buffer)
  (let ((targets (funcall orig-func default-buffer)))
    (cl-delete-if
     #'(lambda (target)
         (not (string-match-p
               `(rx
                 (group
                  (or "/"
                      (seq bos
                           ,(file-name-nondirectory
                             org-constants-plain-org-path)
                           eos))))
               (car target))))
     targets)))

(defun org-ext-refile-heading-p ()
  (let ((refile (org-ext-entry-get-immediate "REFILE")))
    (if refile
        (not (string= refile "no"))
      (or (org-ext-category-p)
          (org-ext-project-p)))))

(defun org-ext-sort-all ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^\\*+ " nil t)
      (goto-char (match-beginning 0))
      (when (org-ext-refile-heading-p)
        (condition-case _err
            (progn
              (org-sort-entries t ?p)
              (org-sort-entries t ?o))
          (error nil)))
      (forward-line))))

(defun org-ext-id-copy ()
  (interactive)
  (org-id-copy)
  (message "Copied id:%s to the kill ring" (car kill-ring)))

;;; From https://gist.github.com/MenacingMecha/11bd07daaaac790620b5fe0437e96a4c
(defun org-ext-set-blocker-from-clipboard-id ()
  "Adds the id in the clipboard (obtained using `org-id-copy') to
the current headlines BLOCKER property."
  (interactive)
  (if (not (derived-mode-p 'org-mode))
      (message "Not in org buffer.")
    (let* ((blocker-prop "BLOCKER")
	   (blocker-prop-existing (org-entry-get nil blocker-prop 'selective))
	   (blocker-prop-base (or blocker-prop-existing "ids()"))
	   (blocker-value
            (with-temp-buffer
              (insert blocker-prop-base)
	      (backward-char)
	      (when blocker-prop-existing
		(insert " "))
	      (insert "id:" (car kill-ring))
	      (buffer-string))))
      (org-set-property blocker-prop blocker-value)
      (message "Task is now blocked on %s" blocker-value))))

;;; From https://mbork.pl/2024-08-19_Opening_all_links_in_an_Org_subtree
(defun org-ext-open-all-links-in-subtree ()
  "Open all the links in the current subtree.
Note: this uses Org's internal variable `org-link--search-failed'."
  (interactive)
  (save-excursion
    (save-restriction
      (org-narrow-to-subtree)
      (goto-char (point-min))
      (let ((inhibit-message t)
            (message-log-max nil))
        (setq org-link--search-failed nil)
        (while (progn (org-next-link)
                      (not org-link--search-failed))
          (org-open-at-point))))))

(defun org-ext-get-properties (&rest props)
  (cons (org-current-level)
        (mapcar #'(lambda (prop)
                    (if (string= "ITEM_BY_ID" prop)
                        (format "[[id:%s][%s]]"
                                (org-entry-get (point) "ID")
                                (org-entry-get (point) "ITEM"))
                      (org-entry-get (point) prop)))
                props)))

(defun org-ext-needs-review-p ()
  "Return non-nil if a review is needed for task at point.
A review may be needed if:
1. There is no LAST_REVIEW property, meaning this task has never
   been reviewed.
2. The NEXT_REVIEW property indicates a date in the past."
  (or (not (org-review-last-review-prop nil))
      (org-review-toreview-p)))

(defun org-ext-report-items-to-be-reviewed ()
  "Report items pending review after one second."
  (run-with-timer
   1 nil
   #'(lambda ()
       (message
        "There are %s items pending review"
        (length
         (org-ql-query
           :select '(point-marker)
           :from (org-agenda-files)
           :where
           '(and (todo)
                 (not (or (tags "ARCHIVE")
                          (ancestors (or (todo) (tags "ARCHIVE")))
                          (scheduled)
                          (deadline)
                          (ts-active)))
                 (org-ext-needs-review-p))))))))

(defun org-dblock-write:ql-columnview (params)
  "Create a table view of an org-ql query.

Example:

#+begin: ql-columnview :query \"(and (tags \\\"John\\\") (todo))\" :properties \"TODO ITEM_BY_ID LAST_REVIEW NEXT_REVIEW TAGS\" :sort-idx 4
#+end:

The :sort-idx takes the 1-indexed column mentioned in
:properties, interprets it as an Org-time, and sorts the
resulting table on that column, ascending."
  (let* ((columns (split-string (or (plist-get params :properties)
                                    "TODO ITEM_BY_ID TAGS")
                                " "))
         (sort-index (plist-get params :sort-idx))
         (table
          (org-ql-select
            'org-agenda-files
            `(and ,(let ((query (plist-get params :query))
                         (who (plist-get params :who)))
                     (when who
                       (setq who (format "(tasks-for \"%s\")" who)))
                     (read (if (and query who)
                               (format "(or %s %s)" who query)
                             (or query who))))
                  (not (or (org-ext-project-p)
                           (org-ext-category-p))))
            :action `(org-ext-get-properties ,@columns)
            :sort
            #'(lambda (x y)
                (when sort-index
                  (let ((x-value (nth sort-index x))
                        (y-value (nth sort-index y)))
                    (when (and x-value y-value)
                      (time-less-p
                       (org-encode-time
                        (org-parse-time-string x-value))
                       (org-encode-time
                        (org-parse-time-string y-value))))))))))
    ;; Add column titles and a horizontal rule in front of the table.
    (setq table (cons columns (cons 'hline table)))
    (let ((hlines nil)
          new-table)
      ;; Copy header and first rule.
      (push (pop table) new-table)
      (push (pop table) new-table)
      (dolist (row table (setq table (nreverse new-table)))
        (let ((level (car row)))
	  (when (and (not (eq (car new-table) 'hline))
		     (or (eq hlines t)
			 (and (numberp hlines) (<= level hlines))))
	    (push 'hline new-table))
	  (push (cdr row) new-table))))
    (save-excursion
      ;; Insert table at point.
      (insert
       (mapconcat (lambda (row)
		    (if (eq row 'hline) "|-|"
		      (format "|%s|" (mapconcat #'identity row "|"))))
		  table
		  "\n")))
    (org-table-align)))

(defcustom org-ext-link-names nil
  "A list of ids and their associated names used by `org-ext-edit-link-name'."
  :group 'org-ext
  :type '(repeat (cons string string)))

(defun org-ext-edit-link-name (name)
  (interactive
   (list (completing-read "Name: " (mapcar #'car org-ext-link-names))))
  (save-excursion
    (goto-char (line-beginning-position))
    (when (re-search-forward "\\[\\[\\([^]]+?\\)\\]\\[\\([^]]+?\\)\\]\\]" nil t)
      (replace-match name t t nil 2))))

(defun org-ext-fixup-slack (&optional arg)
  (interactive "P")
  (whitespace-cleanup)
  (goto-char (point-min))
  (while (search-forward "\n\n \n\n" nil t)
    (replace-match ": "))
  (goto-char (point-min))
  (while (search-forward " " nil t)
    (replace-match " "))
  (goto-char (point-min))
  (while (search-forward " (edited)" nil t)
    (delete-region (match-beginning 0) (match-end 0)))
  (goto-char (point-min))
  (while (re-search-forward "\\[\\[https://.*emoji-assets[^]]+?\\.png\\]\\]" nil t)
    (delete-region (match-beginning 0) (match-end 0)))
  (goto-char (point-min))
  (while (re-search-forward
          "^\\( *\\)\\[\\[https://kadena-io\\.slack\\.com[^]]+?\\]\\[\\(\\(Today at \\)?[0-9:]+ [AP]M\\)\\]\\]\\(\n+\\)" nil t)
    (replace-match ": " t t nil 4)
    (replace-match "Me" t t nil 2)
    (delete-region (match-beginning 1) (match-end 1)))
  (whitespace-cleanup)
  (unless arg
    (goto-char (point-min))
    (while (looking-at "^#")
      (forward-line 1))
    (fill-region (point) (point-max))))

;;; This function was inspired by Sacha Chua at:
;;; https://sachachua.com/blog/2024/10/org-mode-prompt-for-a-heading-and-then-refile-it-to-point/
(defun org-ext-move-subtree-to-point (uuid)
  "Prompt for a heading and refile it to point."
  (interactive (list (vulpea-note-id (vulpea-select "Heading"))))
  (cl-destructuring-bind (file . pos)
      (org-id-find uuid)
    (save-excursion
      (with-current-buffer
          (find-file-noselect file 'noward)
        (save-excursion
          (save-restriction
            (widen)
            (goto-char pos)
            (org-copy-subtree 1 t))))
      (org-paste-subtree nil nil nil t))))

(defun org-ext-prune-log-entries (days)
  (interactive "Number of days to keep: ")
  (save-excursion
    (org-back-to-heading)
    (re-search-forward "^:LOGBOOK:\n")
    (let ((beg (point)) end)
      (re-search-forward "^:END:\n")
      (setq end (match-beginning 0))
      (save-restriction
        (narrow-to-region beg end)
        (goto-char (point-min))
        (while (re-search-forward "- State.*\\(\\[[-:0-9A-Z ]+\\]\\)" nil t)
          (let* ((start (match-beginning 0)) (date (match-string 1))
                 (age (- (time-to-days (current-time))
                         (time-to-days (org-encode-time
                                        (org-parse-time-string date))))))
            (if (> age days)
                (delete-region start (point-max)))))))))

(defun org-ext-prune-ninety-days-of-logs ()
  (interactive)
  (org-ext-prune-log-entries 90))

(defun org-ext-read-names (file)
  (with-temp-buffer
    (insert-file-contents-literally file)
    (goto-char (point-min))
    (let (result)
      (while (re-search-forward
              "^| \\[\\[\\(id:.+?\\)\\]\\[\\(.+?\\)\\]\\]\\s-+|\\s-+\\(\\[.+\\]\\)?\\s-+|"
              nil t)
        (let ((link (match-string-no-properties 1))
              (name (match-string-no-properties 2))
              (one-on-one-page (match-string-no-properties 3)))
          (push (cons name (list link one-on-one-page)) result)))
      result)))

(defun org-ext-update-team ()
  (interactive)
  (let ((file (org-file org-constants-kadena-team-file)))
    (setq org-ext-link-names (org-ext-read-names file))
    (with-current-buffer (find-file-noselect file)
      (save-excursion
        (while (re-search-forward
                "^| \\[\\[id:.+?\\]\\[\\(.+?\\)\\]\\].+|\\s-+\\([A-Za-z0-9_]\\)\\s-+|$" nil t)
          (let ((name (match-string-no-properties 1))
                (key (match-string-no-properties 2)))
            (define-key org-mode-map (kbd (concat "s-" key))
                        `(lambda () (interactive) (org-ext-edit-link-name ,name)))))))
    (message "Team names and quick keys updated")))

(defun org-ext-update-team-after-save ()
  (when (and (eq major-mode 'org-mode)
             (string-match org-constants-kadena-team-file (buffer-file-name)))
    (org-ext-update-team)))

(defun org-ext-unlink-region (&optional beg end)
  (interactive)
  (save-restriction
    (narrow-to-region (or beg (point-min)) (or end (point-max)))
    (goto-char (point-min))
    (while (re-search-forward org-link-bracket-re nil t)
      (replace-match (match-string 2)))))

(defun org-ext-follow-tag-link (tag)
  "Display a list of TODO headlines with tag TAG.
With prefix argument, also display headlines without a TODO keyword."
  (org-tags-view (null current-prefix-arg) tag))

(defun org-ext-yank-link ()
  (interactive)
  (org-insert-all-links nil "*** " "\n"))

(defun org-ext-gnus-drop-link-parameter (param)
  (setq org-link-parameters
        (cl-delete-if #'(lambda (x) (string= (car x) param))
                      org-link-parameters)))

(defun org-ext-message-reply ()
  (interactive)
  (let* ((org-marker (get-text-property (point) 'org-marker))
         (author (org-entry-get (or org-marker (point)) "Author"))
         (subject (if org-marker
                      (with-current-buffer (marker-buffer org-marker)
                        (goto-char org-marker)
                        (nth 4 (org-heading-components)))
                    (nth 4 (org-heading-components)))))
    (setq subject (replace-regexp-in-string "\\`(.*?) " "" subject))
    (compose-mail-other-window author (concat "Re: " subject))))

(defun org-ext-sort-done-tasks ()
  (interactive)
  (goto-char (point-min))
  (org-sort-entries t ?F #'org-get-inactive-time #'<)
  (goto-char (point-min))
  (while (re-search-forward "


+" nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (insert "
"))
  (let (after-save-hook)
    (save-buffer))
  (org-overview))

(defun org-ext-get-message-link (&optional title)
  (let (message-id subject)
    (with-current-buffer gnus-original-article-buffer
      (setq message-id (substring (message-field-value "message-id") 1 -1)
            subject (or title (message-field-value "subject"))))
    (org-link-make-string (concat "message://" message-id)
                          (rfc2047-decode-string subject))))

(defun org-ext-insert-message-link (&optional arg)
  (interactive "P")
  (insert (org-ext-get-message-link (if arg "writes"))))

(defun org-ext-set-message-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Message" (org-ext-get-message-link)))

(defun org-ext-get-message-sender ()
  (with-current-buffer gnus-original-article-buffer
    (message-field-value "from")))

(defun org-ext-set-message-sender ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Submitter" (org-ext-get-message-sender)))

(defun org-ext-set-url-from-clipboard ()
  "Set a property for the current headline."
  (interactive)
  (org-back-to-heading)
  (org-set-property (if (org-entry-get (point-marker) "URL") "URL2" "URL")
                    (gui--selection-value-internal 'CLIPBOARD))
  (org-toggle-tag "LINK" 'on))

(defun org-ext-get-inactive-time ()
  (float-time (org-time-string-to-time
               (or (org-entry-get (point) "TIMESTAMP")
                   (org-entry-get (point) "TIMESTAMP_IA")
                   (org-entry-get (point) "CREATED")
                   (debug)))))

(defun org-ext-open-map-link ()
  (interactive)
  (let ((location (org-entry-get (point) "LOCATION")))
    (if location
        (if (featurep 'osm)
            (pcase (split-string location ",")
              (`(,lat ,lon)
               (osm-goto (string-to-number lat) (string-to-number lon) nil)))
          (browse-url (concat "https://maps.apple.com/?q=org&ll=" location)))
      (error "Entry has no location set"))))

(defun org-ext-linkify ()
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward " \\(\\(VER\\|SDK\\)-\\([0-9]+\\)\\) " nil t)
    (replace-match (format " [[%s:\\3][\\2-\\3]] " (downcase (match-string 2))) t)
    (goto-char (match-end 0)))
  (while (re-search-forward " \\(\\(quill\\)#\\([0-9]+\\)\\) " nil t)
    (replace-match (format " [[%s:\\3][\\2#\\3]] " (downcase (match-string 2))) t)
    (goto-char (match-end 0))))

(defun org-ext-save-org-mode-files ()
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq major-mode 'org-mode)
        (if (and (buffer-modified-p) (buffer-file-name))
            (save-buffer))))))

(defun org-ext-current-tags (depth)
  (save-excursion
    (ignore-errors
      (let (should-skip)
        (while (and (> depth 0)
                    (not should-skip)
                    (prog1
                        (setq depth (1- depth))
                      (not (org-up-element))))
          (if (looking-at "^\*+\\s-+")
              (setq should-skip (org-get-tags))))
        should-skip))))

(defun org-ext-ancestor-keywords ()
  (save-excursion
    (let ((had-parent (org-up-heading-safe)))
      (delete nil
              (cons (org-get-todo-state)
                    (when had-parent
                      (org-ext-ancestor-keywords)))))))

(defun org-ext-insert-code-block ()
  "Replace ``` with an Org code block."
  (when (let* ((keys (recent-keys))
               (n (length keys)))
          (and (eq ?` (aref keys (- n 1)))
               (eq ?` (aref keys (- n 2)))
               (eq ?` (aref keys (- n 3)))))
    (backward-delete-char 3)
    (let ((language
           (or (save-excursion
                 (re-search-backward "#\\+begin_src \\([^ \t\n]+\\)" nil t)
                 (match-string 1))
               "sh")))
      (insert "#+begin_src " language "\n\n#+end_src")
      (forward-line -1))))

(defsubst org-ext-setup-insert-code-block ()
  (add-hook 'post-self-insert-hook #'org-ext-insert-code-block nil t))

(provide 'org-ext)

;;; org-ext.el ends here
