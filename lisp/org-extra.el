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

(defgroup org-extra nil
  "Capture Gnus messages as tasks, with context"
  :group 'org)

(defun org-extra-start-of-inbox ()
  (goto-char (point-min))
  (re-search-forward "^\\* Inbox$")
  (re-search-forward "^:END:")
  (forward-line 1))

(defun org-extra-goto-inbox (&optional func)
  (interactive)
  (with-current-buffer (funcall (if func
                                    #'find-file-noselect
                                  #'find-file)
                                "~/org/area/todo.org")
    (if func
        (save-excursion
          (org-extra-start-of-inbox)
          (funcall func))
      (org-extra-start-of-inbox))))

(defun org-extra-reformat-draft ()
  ;; If there is a URL, this is a LINK.
  (setq url nil)
  (when (re-search-forward ":URL:\\s-*\\(.+?\\)\n" nil t)
    (setq url (match-string 1))
    (delete-region (match-beginning 0) (match-end 0))
    (org-set-property "URL" url)
    (goto-char (point-min))
    (when (re-search-forward "SCHEDULED: .+\n")
      (delete-region (match-beginning 0) (match-end 0)))
    (goto-char (point-min))
    (when (re-search-forward " TODO ")
      (replace-match " LINK " nil nil nil 0)))
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
           (directory-files
            "~/Library/Mobile Documents/iCloud~com~agiletortoise~Drafts5/Documents"
            t "[0-9].*\\.txt\\'" nil)))
        url)
    (when notes
      (org-extra-goto-inbox
       (lambda ()
         (dolist (note notes)
           (insert
            (with-temp-buffer
              (insert-file-contents note)
              (goto-char (point-min))
              (org-extra-reformat-draft)
              (goto-char (point-max))
              (unless (bolp)
                (insert ?\n))
              (buffer-string)))
           (delete-file note t))
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

(defun org-extra-agenda-add-overlays (&optional line)
  "Add overlays found in OVERLAY properties to agenda items.
Note that habitual items are excluded, as they already
extensively use text properties to draw the habits graph.

For example, for work tasks I like to use a subtle, yellow
background color; for tasks involving other people, green; and
for tasks concerning only myself, blue.  This way I know at a
glance how different responsibilities are divided for any given
day.

To achieve this, I have the following in my todo file:

  * Work
  :PROPERTIES:
  :CATEGORY: Work
  :OVERLAY:  (face (:background \"#fdfdeb\"))
  :END:
  ** TODO Task
  * Family
  :PROPERTIES:
  :CATEGORY: Personal
  :OVERLAY:  (face (:background \"#e8f9e8\"))
  :END:
  ** TODO Task
  * Personal
  :PROPERTIES:
  :CATEGORY: Personal
  :OVERLAY:  (face (:background \"#e8eff9\"))
  :END:
  ** TODO Task

The colors (which only work well for white backgrounds) are:

  Yellow: #fdfdeb
  Green:  #e8f9e8
  Blue:   #e8eff9

To use this function, add it to `org-agenda-finalize-hook':

  (add-hook 'org-agenda-finalize-hook 'org-agenda-add-overlays)"
  (let ((inhibit-read-only t)
        (buffer-invisibility-spec '(org-link)))
    (save-excursion
      (goto-char (if line (line-beginning-position) (point-min)))
      (while (not (eobp))
        (let ((org-marker (get-text-property (point) 'org-marker)))
          (when (and org-marker
                     (null (overlays-at (point)))
                     (not (get-text-property (point) 'org-habit-p))
                     (get-text-property (point) 'type)
                     (string-match "\\(sched\\|dead\\|todo\\)"
                                   (get-text-property (point) 'type)))
            (let ((overlays
                   (or (org-entry-get org-marker "OVERLAY" t)
                       (with-current-buffer (marker-buffer org-marker)
                         (org-get-global-property "OVERLAY")))))
              (when overlays
                (goto-char (line-end-position))
                (let ((rest (- (window-width) (current-column))))
                  (if (> rest 0)
                      (insert (make-string rest ? ))))
                (let ((ol (make-overlay (line-beginning-position)
                                        (line-end-position)))
                      (proplist (read overlays)))
                  (while proplist
                    (overlay-put ol (car proplist) (cadr proplist))
                    (setq proplist (cddr proplist))))))))
        (forward-line)))))

(defun org-extra-agenda-skip-if-not-within (days)
  "Skip entry if it wasn't created within the given number of DAYS."
  (ignore-errors
    (let ((subtree-end (save-excursion (org-end-of-subtree t)))
          (day
           (time-to-days
            (org-time-string-to-time
             (org-entry-get nil "CREATED"))))
          (now (time-to-days (current-time))))
      (and day
           (> (- now day) days)
           subtree-end))))

(defun org-extra-agenda-skip-if-within (days)
  "Skip entry if it wasn't created within the given number of DAYS."
  (ignore-errors
    (let ((subtree-end (save-excursion (org-end-of-subtree t)))
          (day
           (time-to-days
            (org-time-string-to-time
             (org-entry-get nil "CREATED"))))
          (now (time-to-days (current-time))))
      (and day
           (<= (- now day) days)
           subtree-end))))

(defun org-extra-jump-to-agenda ()
  (interactive)
  (push-window-configuration)
  (cl-flet ((prep-window
              (wind)
              (with-selected-window wind
                (org-fit-window-to-buffer wind)
                (ignore-errors
                  (window-resize
                   wind
                   (- 100 (window-width wind)) t)))))
    (let ((buf (or (get-buffer "*Org Agenda*")
                   (get-buffer "*Org Agenda(a)*"))))
      (if buf
          (let ((win (get-buffer-window buf)))
            (if win
                (when (called-interactively-p 'any)
                  (funcall #'prep-window win))
              (if (called-interactively-p 'any)
                  (funcall #'prep-window (display-buffer buf t t))
                (funcall #'prep-window (display-buffer buf)))))
        (require 'org-agenda)
        (mapc #'find-file-noselect org-agenda-files)
        (call-interactively 'org-agenda-list)
        (funcall #'prep-window (selected-window))))))

(defun org-extra-basic-properties ()
  (org-set-property "ID" (substring (shell-command-to-string "uuidgen") 0 -1))
  (org-set-property "CREATED" (with-temp-buffer
                                (org-insert-time-stamp (current-time) t t))))

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

(provide 'org-extra)

;;; org-extra.el ends here
