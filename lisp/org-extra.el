;;; org-extra --- Extra functions for use with Org-mode

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
(require 'org)

(declare-function org-with-wide-buffer "org-macs")

(defgroup org-extra nil
  "Extra functions for use with Org-mode"
  :group 'org)

(defun org-extra-up-heading ()
  (call-interactively #'outline-up-heading))

(defun org-extra-goto-inbox-heading ()
  (set-buffer (get-buffer "todo.org"))
  (goto-char (point-min))
  (while (looking-at "^[:#]")
    (forward-line 1))
  (unless (looking-at "^$")
    (error "Missing blank line after file header in todo.org"))
  (forward-line 1)
  (unless (looking-at "^\\* Inbox$")
    (error "Missing Inbox heading at start of todo.org")))

(defun org-extra-goto-inbox (&optional func)
  (interactive)
  (with-current-buffer
      (funcall (if func
                   #'find-file-noselect
                 #'find-file)
               (expand-file-name "todo.org" org-directory))
    (if func
        (save-excursion
          (org-extra-goto-inbox-heading)
          (forward-line 1)
          (while (looking-at "^:")
            (forward-line 1))
          (funcall func))
      (org-extra-goto-inbox-heading)
      (forward-line 1)
      (while (looking-at "^:")
        (forward-line 1)))))

(defun org-extra-reformat-draft ()
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

(defadvice org-agenda (around fit-windows-for-agenda activate)
  "Fit the Org Agenda to its buffer."
  (let ((notes
         (ignore-errors
           (directory-files "~/Drafts" t "[0-9].*\\.txt\\'" nil)))
        url)
    (when notes
      (org-extra-goto-inbox
       (lambda ()
         (dolist (note notes)
           (when (ignore-errors
                   (insert
                    (with-temp-buffer
                      (insert-file-contents note)
                      (goto-char (point-min))
                      (org-extra-reformat-draft)
                      (goto-char (point-max))
                      (unless (bolp)
                        (insert ?\n))
                      (buffer-string)))
                   t)
             (delete-file note t)))
         (when (buffer-modified-p)
           (save-buffer))))))
  ad-do-it
  (org-fit-agenda-window))

(defun org-extra-agenda-show (&optional arg)
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

(defun org-extra-agenda-show-and-scroll-up (&optional arg)
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

(defun org-extra-jump-to-agenda ()
  (interactive)
  (push-window-configuration)
  (cl-flet ((prep-window
              (wind)
              (select-window wind)
              (org-fit-window-to-buffer wind)
              (ignore-errors
                (window-resize
                 wind
                 (- 100 (window-width wind)) t))))
    (let ((buf (or (get-buffer "*Org Agenda*")
                   (get-buffer "*Org Agenda(a)*"))))
      (if buf
          (let ((win (get-buffer-window buf)))
            (if win
                (progn
                  (when (called-interactively-p 'any)
                    (funcall #'prep-window win))
                  (select-window win))
              (funcall #'prep-window
                       (if (called-interactively-p 'any)
                           (display-buffer buf t t)
                         (display-buffer buf)))))
        (require 'org-agenda)
        (mapc #'find-file-noselect org-agenda-files)
        (call-interactively #'org-agenda-list)
        (org-agenda-filter '(64))
        (funcall #'prep-window (selected-window))))))

(defun org-extra-agenda-redo (&optional all)
  (interactive)
  (org-agenda-redo all)
  (push-window-configuration)
  (let ((wind (selected-window)))
    (with-selected-window wind
      (org-fit-window-to-buffer wind)
      (ignore-errors
        (window-resize
         wind
         (- 100 (window-width wind)) t)))))

(defun org-extra-entire-properties-block ()
  "Return the entire properties block, inclusive of :PROPERTIES:...:END:."
  (save-excursion
    (org-back-to-heading)
    (let ((entry-end (save-excursion
                       (outline-next-heading)
                       (point)))
          beg end)
      (when (search-forward ":PROPERTIES:" end t)
        (setq beg (match-beginning 0)))
      (when (re-search-forward ":END:\\s-*\n" end t)
        (setq end (match-end 0)))
      (cons beg end))))

(defun org-extra-move-properties-drawer ()
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
        (pcase (org-extra-entire-properties-block)
          (`(,beg . ,end)
           (let ((entries-block (buffer-substring beg end)))
             (delete-region beg end)
             ;; Create a new properties block
             (org-get-property-block nil 'force)
             (pcase (org-extra-entire-properties-block)
               (`(,new-beg . ,new-end)
                (goto-char new-beg)
                (delete-region new-beg new-end)
                (insert entries-block)))))
          (_ nil))
        (if (equal before-sha (sha1 (buffer-substring-no-properties beg end)))
            (set-buffer-modified-p modified))))))


(defun org-extra-fix-all-properties ()
  (interactive)
  (while (re-search-forward "^\\*" nil t)
    (ignore-errors
      (org-extra-move-properties-drawer))
    (forward-line 1)))

(defun org-extra-update-date-field ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^#\\+date:\\s-*\\(.+\\)" nil t)
      (delete-region (match-beginning 1) (match-end 1))
      (org-insert-time-stamp (current-time) t t))))

(defun org-extra-reformat-time (&optional beg end)
  (interactive "r")
  (let ((date-string (buffer-substring beg end)))
    (save-excursion
      (goto-char beg)
      (delete-region beg end)
      (insert
       (format-time-string
        (org-time-stamp-format 'long 'inactive)
        (org-encode-time (parse-time-string date-string)))))))

(defun org-extra-todoize (&optional arg)
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
  (org-id-get-create arg)
  (unless (org-entry-get (point) "CREATED")
    (org-entry-put (point) "CREATED"
                   (format-time-string (org-time-stamp-format t t)))))

(defun org-extra-todoize-region (&optional beg end arg)
  "Add standard metadata to headlines in region.
See `org-extra-todoize'."
  (interactive "r\nP")
  (with-restriction beg end
    (save-excursion
      (goto-char beg)
      (while (not (eobp))
        (goto-char (line-end-position))
        (org-extra-todoize arg)
        (ignore-errors
          (org-next-visible-heading 1))))))

(defvar org-extra-fixup-slack-history nil)

(defun org-extra-fixup-slack ()
  (interactive)
  (goto-char (point-min))
  (while (search-forward "\n\n \n\n" nil t)
    (replace-match ": "))
  (goto-char (point-min))
  (while (re-search-forward "^\\[\\[\\(https:.+?\\)\\]\\[.+?\\]\\]: " nil t)
    (replace-match
     (concat "[["
             (match-string 1)
             "]["
             ;; (read-string "Author: " "Me" org-extra-fixup-slack-history)
             "Me"
             "]]: "))))

(defvar org-extra-property-search-name nil)

(defun org-extra-with-property-search (property value)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive
   (list (setq org-extra-property-search-name (org-read-property-name))
         (completing-read "Value: "
                          (org-property-values org-extra-property-search-name))))
  (let ((org-use-property-inheritance
         (append org-use-property-inheritance '("WITH"))))
    (org-tags-view
     t (format "%s={%s}&TODO={TODO\\|WAITING\\|DELEGATED}" property value))))

(defun org-extra-created-from-stamp ()
  (interactive)
  (let* ((name (file-name-nondirectory (buffer-file-name)))
         (year (string-to-number (substring name 0 4)))
         (mon (string-to-number (substring name 4 6)))
         (day (string-to-number (substring name 6 8))))
    (org-set-property
     "CREATED"
     (with-temp-buffer
       (org-insert-time-stamp
        (org-encode-time (list 0 0 0 day mon year)) nil t)
       (buffer-string)))))

(defun org-extra-insert-structure-template-and-yank (type)
  (interactive
   (list (pcase (org--insert-structure-template-mks)
	   (`("\t" . ,_) (read-string "Structure type: "))
	   (`(,_ ,choice . ,_) choice))))
  (org-insert-structure-template type)
  (yank))

(defun org-extra-id-copy ()
  (interactive)
  (org-id-copy)
  (message "Copied id:%s to the kill ring" (car kill-ring)))

(defun org-extra-parent-keyword ()
  (save-excursion
    (org-up-heading-safe)
    (org-get-todo-state)))

(defun org-extra-parent-priority ()
  (save-excursion
    (org-up-heading-safe)
    (save-match-data
      (beginning-of-line)
      (and (looking-at org-heading-regexp)
	   (org-get-priority (match-string 0))))))

(defun org-extra-agenda-files-except (&rest args)
  (let ((result org-agenda-files))
    (dolist (arg args)
      (setq result (delete arg result)))
    result))

(defun org-extra-task-p (&optional keyword)
  (member (or keyword (org-get-todo-state))
          '("TODO" "DOING" "WAIT" "TASK" "DEFER" "CANCELED" "DONE")))

(defun org-extra-subtask-p ()
  (and (org-extra-task-p)
       (let ((keyword (org-extra-parent-keyword)))
         (and keyword (org-extra-task-p keyword)))))

(defun org-extra-project-task-p ()
  (and (org-extra-task-p)
       (member (org-extra-parent-keyword) '("PROJECT"))))

;;; From https://gist.github.com/MenacingMecha/11bd07daaaac790620b5fe0437e96a4c
(defun org-extra-set-blocker-from-clipboard-id ()
  "Adds the id in the clipboard (obtained using `org-id-copy') to
the current headlines BLOCKER property."
  (interactive)
  (if (not (derived-mode-p 'org-mode))
      (message "Not in org buffer.")
    (let* ((blocker-prop "BLOCKER")
	   (blocker-prop-existing (org-entry-get nil blocker-prop 'selective))
	   (blocker-prop-base (or blocker-prop-existing "ids()"))
	   (blocker-value (with-temp-buffer (insert blocker-prop-base)
					    (backward-char)
					    (when blocker-prop-existing
					      (insert " "))
					    (insert "id:" (car kill-ring))
					    (buffer-string))))
      (org-set-property blocker-prop blocker-value))))



;;; From https://mbork.pl/2024-08-19_Opening_all_links_in_an_Org_subtree
(defun org-extra-open-all-links-in-subtree ()
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

(defun org-extra-sync ()
  (interactive)
  (let ((agenda-buf (get-buffer "*Org Agenda*")))
    (when agenda-buf
      (kill-buffer agenda-buf)))
  (message "Synchronizing CalDAV...")
  (org-caldav-sync)
  (message "Sorting Org-mode files...")
  (redisplay t)
  (dolist (file org-agenda-files)
    (with-current-buffer (find-file-noselect file)
      (goto-char (point-min))
      (org-sort-all)
      (org-cycle-content 5)
      (org-align-tags t)))
  (save-org-mode-files)
  (message "Updating Org-roam todo cookies...")
  (redisplay t)
  (my/org-roam-update-todo-files)
  (save-org-mode-files)
  (message "Updating Org-mode ID locations...")
  (redisplay t)
  (org-id-update-id-locations)
  (message "Clearing Org-mode refile cache...")
  (redisplay t)
  (ignore-errors (org-refile-cache-clear))
  (message "Clear Org-contacts and diary cache...")
  (setq org-contacts-last-update nil
        org--diary-sexp-entry-cache (make-hash-table :test #'equal))
  (message "Syncing Org-roam database...")
  (redisplay t)
  (org-roam-db-sync)
  (org-roam-update-org-id-locations)
  (require 'xeft)
  (require 'xapian-lite)
  (message "Rebuilding Xeft database...")
  (redisplay t)
  (xeft-full-reindex)
  (xeft--front-page-cache-refresh)
  (message "Running syncup...")
  (redisplay t)
  (let ((default-directory "~"))
    (async-shell-command "syncup ; echo FINISHED")
    (display-buffer "*Async Shell Command*"))
  (message "Jumping to agenda! Sync complete.")
  (redisplay t))

(defun org-extra-columns--capture-view
    (maxlevel match skip-empty exclude-tags format local)
  (org-columns (not local) format)
  (goto-char org-columns-top-level-marker)
  (let ((columns (length org-columns-current-fmt-compiled))
	(has-item (assoc "ITEM" org-columns-current-fmt-compiled))
	table)
    (org-map-entries
     (lambda ()
       (when (get-char-property (point) 'org-columns-key)
	 (let (row)
	   (dotimes (i columns)
	     (let* ((col (+ (line-beginning-position) i))
		    (p (get-char-property col 'org-columns-key)))
	       (push (org-quote-vert
		      (get-char-property col
					 (if (string= p "ITEM")
					     'org-columns-value
					   'org-columns-value-modified)))
		     row)))
	   (unless (or
		    (and skip-empty
			 (let ((r (delete-dups (remove "" row))))
			   (or (null r) (and has-item (= (length r) 1)))))
		    (and exclude-tags
			 (cl-some (lambda (tag) (member tag exclude-tags))
				  (org-get-tags))))
	     (push (cons (org-reduced-level (org-current-level)) (nreverse row))
		   table)))))
     (if match
         (concat match (and maxlevel (format "+LEVEL<=%d" maxlevel)))
       (and maxlevel (format "LEVEL<=%d" maxlevel)))
     (and local 'tree)
     'archive 'comment)
    (org-columns-quit)
    table))

(defun org-dblock-write:agenda-columnview (params)
  "See documentation for `org-dblock-write:agenda-columnview`.
This dynamic block does not accept an `:id` parameter, however,
and simply iterates over all files in `org-agenda-files`."
  (let ((table
         (apply #'nconc
                (delete
                 nil
                 (mapcar
                  #'(lambda (view-file)
                      (with-current-buffer
                          (org-get-agenda-file-buffer view-file)
	                (org-with-wide-buffer
                         (org-extra-columns--capture-view
                          (plist-get params :maxlevel)
		          (plist-get params :match)
		          (plist-get params :skip-empty-rows)
		          (plist-get params :exclude-tags)
		          (plist-get params :format)
		          nil))))
                  org-agenda-files)))))
    ;; Add column titles and a horizontal rule in front of the table.
    (setq table
          (cons (mapcar #'cadr org-columns-current-fmt-compiled)
	        (cons 'hline (nreverse table))))
    (when table
      ;; Prune level information from the table.  Also normalize
      ;; headings: remove stars, add indentation entities, if
      ;; required, and possibly precede some of them with a horizontal
      ;; rule.
      (let ((item-index
	     (let ((p (assoc "ITEM" org-columns-current-fmt-compiled)))
	       (and p (cl-position p
				   org-columns-current-fmt-compiled
				   :test #'equal))))
	    (hlines (plist-get params :hlines))
	    (indent (plist-get params :indent))
	    new-table)
	;; Copy header and first rule.
	(push (pop table) new-table)
	(push (pop table) new-table)
	(dolist (row table (setq table (nreverse new-table)))
          (setq row
                (list (nth 0 row)
                      (nth 1 row)
                      (format "[[id:%s][%s]]" (nth 1 row) (nth 2 row))
                      (nth 3 row)))
          (let ((level (car row)))
	    (when (and (not (eq (car new-table) 'hline))
		       (or (eq hlines t)
			   (and (numberp hlines) (<= level hlines))))
	      (push 'hline new-table))
	    (when item-index
	      (let ((item (org-columns--clean-item (nth item-index (cdr row)))))
		(setf (nth item-index (cdr row))
		      (if (and indent (> level 1))
			  (concat "\\_" (make-string (* 2 (1- level)) ?\s) item)
			item))))
	    (push (cdr row) new-table))))
      (when (plist-get params :vlines)
	(setq table
	      (let ((size (length org-columns-current-fmt-compiled)))
		(append (mapcar (lambda (x) (if (eq 'hline x) x (cons "" x)))
				table)
			(list (cons "/" (make-list size "<>")))))))
      (let ((content-lines (org-split-string (plist-get params :content) "\n"))
	    recalc)
	;; Insert affiliated keywords before the table.
	(when content-lines
	  (while (string-match-p "\\`[ \t]*#\\+" (car content-lines))
	    (insert (pop content-lines) "\n")))
	(save-excursion
	  ;; Insert table at point.
	  (insert
	   (mapconcat (lambda (row)
			(if (eq row 'hline) "|-|"
			  (format "|%s|" (mapconcat #'identity row "|"))))
		      table
		      "\n"))
	  ;; Insert TBLFM lines following table.
	  (let ((case-fold-search t))
	    (dolist (line content-lines)
	      (when (string-match-p "\\`[ \t]*#\\+TBLFM:" line)
		(insert "\n" line)
		(unless recalc (setq recalc t))))))
	(when recalc (org-table-recalculate 'all t))
	(org-table-align)))))

(provide 'org-extra)

;;; org-extra.el ends here
