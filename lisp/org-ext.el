;;; org-ext --- Extra functions for use with Org-mode -*- lexical-binding: t -*-

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
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

;;; Code:

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
(declare-function org-smart-capture "org-smart-capture")

(defgroup org-ext nil
  "Extra functions for use with Org-mode."
  :group 'org)

(defalias 'org-ext-up-heading #'outline-up-heading)

(defun org-ext-goto-inbox-heading ()
  "Move to Inbox heading in file specified by `org-constants-drafts-path'.
Checks for proper file structure: blank line after header, Inbox heading
at top level. Signals error if formatting is incorrect."
  (let ((path (file-name-nondirectory org-constants-drafts-path)))
    (set-buffer (find-file-noselect org-constants-drafts-path))
    (goto-char (point-min))
    (while (looking-at "^[:#]")
      (forward-line 1))
    (unless (looking-at "^$")
      (error "Missing blank line after file header in %s" path))
    (forward-line 1)
    (unless (looking-at "^\\* Inbox$")
      (error "Missing Inbox heading at start of %s" path))))

(defun org-ext-goto-inbox (&optional func)
  "Navigate to the Inbox section in todo file.
When optional FUNC is provided, execute it within the Inbox context.
Interactively opens the file and positions cursor at first todo item."
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
  "Convert Drafts.app content into org link/note format.
Handles URL conversion, note tagging, and removes empty TAGS lines.
Intended for use with `org-capture' templates."
  ;; If there is a URL, this is a LINK.
  (when (re-search-forward ":LOCATION:\\s-*0.0,.+\n" nil t)
    (delete-region (match-beginning 0) (match-end 0)))
  (when (re-search-forward "^\\(:URL:\\s-*\\)?\\(http.+\\)\n?" nil t)
    (let ((url (match-string 2)))
      (delete-region (match-beginning 0) (match-end 0))
      (org-set-property "URL" url)
      (goto-char (point-min))
      (when (re-search-forward "SCHEDULED: .+\n" nil t)
        (delete-region (match-beginning 0) (match-end 0)))
      (goto-char (point-min))
      (when (re-search-forward " TODO " nil t)
        (replace-match " LINK " nil nil nil 0))))
  ;; If there is a note tag, this is a NOTE.
  (goto-char (point-min))
  (when (re-search-forward
         ":TAGS:\\s-+.+?\\(\\<note\\>\\(,\\s-*\\)?\\|,\\s-*\\<note\\>$\\)" nil t)
    (delete-region (match-beginning 1) (match-end 1))
    (goto-char (point-min))
    (when (re-search-forward " TODO " nil t)
      (replace-match " NOTE " nil nil nil 0))
    (goto-char (point-min))
    (when (re-search-forward "SCHEDULED: .+\n" nil t)
      (delete-region (match-beginning 0) (match-end 0))))
  ;; If there are no tags, delete that property.
  (goto-char (point-min))
  (when (re-search-forward ":TAGS:\\s-+\n" nil t)
    (delete-region (match-beginning 0) (match-end 0))))

(defun org-ext-move-recording-audio (txt-file)
  "Move audio file corresponding to TXT-FILE to ~/Audio/Recordings.
Searches for audio files with the same basename as TXT-FILE but with
common audio extensions (.m4a, .mp3, .wav, .aac, .flac). If found,
moves the audio file to ~/Audio/Recordings."
  (let* ((basename (file-name-sans-extension txt-file))
         (audio-extensions '(".m4a" ".mp3" ".wav" ".aac" ".flac" ".ogg"))
         (audio-dest-dir (expand-file-name "~/Audio/Recordings"))
         audio-file)
    ;; Find the first matching audio file
    (setq audio-file
          (cl-find-if #'file-exists-p
                      (mapcar (lambda (ext) (concat basename ext))
                              audio-extensions)))
    ;; Move audio file if found
    (when audio-file
      (unless (file-directory-p audio-dest-dir)
        (make-directory audio-dest-dir t))
      (let ((dest-path (expand-file-name
                        (file-name-nondirectory audio-file)
                        audio-dest-dir)))
        (rename-file audio-file dest-path t)
        (message "Moved audio file to %s" dest-path)))))

(defun org-ext-reformat-recording ()
  "Convert Just Press Record content into org TODO format.
If the content doesn't already have a heading, creates one from the
first line of text or the content summary."
  ;; If there's no DRAFT heading, create one
  (goto-char (point-min))
  (unless (looking-at "^\\*\\* DRAFT ")
    (goto-char (point-min))
    (insert "** DRAFT ")
    (org-insert-time-stamp (current-time) t t)
    (insert "\n")))

(defun org-ext-fit-agenda-window ()
  "Fit the window to the buffer size."
  (and (memq org-agenda-window-setup '(reorganize-frame))
       (fboundp 'fit-window-to-buffer)
       (fit-window-to-buffer)))

(defadvice org-agenda (around fit-windows-for-agenda activate)
  "Fit the Org Agenda to its buffer and import any pending Drafts and Recordings."
  (let ((draft-notes (directory-files "~/Drafts" t "[0-9].*\\.txt\\'" nil))
        (recording-notes (directory-files "~/Recordings" t ".*\\.txt\\'" nil)))
    (when (or draft-notes recording-notes)
      (org-ext-goto-inbox
       (lambda ()
         ;; Process Drafts notes
         (dolist (note draft-notes)
           (insert
            (with-temp-buffer
              (org-mode)
              (insert-file-contents note)
              (goto-char (point-min))
              ;; Format draft as TODO entry (I know, it's confusing)
              (org-ext-reformat-draft)
              (goto-char (point-max))
              (unless (bolp)
                (insert ?\n))
              (buffer-string)))
           (delete-file note t))
         ;; Process Recording notes
         (dolist (note recording-notes)
           ;; Insert the text content and add metadata
           (let ((start-pos (point)))
             (insert
              (with-temp-buffer
                (org-mode)
                (insert-file-contents note)
                (goto-char (point-min))
                ;; Format recording as DRAFT entry
                (org-ext-reformat-recording)
                (goto-char (point-max))
                (unless (bolp)
                  (insert ?\n))
                (buffer-string)))
             ;; Now we're back in the inbox file buffer, add metadata
             (save-excursion
               (goto-char start-pos)
               (when (re-search-forward "^\\*\\* DRAFT " nil t)
                 (beginning-of-line)
                 (run-hooks 'org-capture-before-finalize-hook))))
           ;; Move corresponding audio file to ~/Audio/Recordings
           (org-ext-move-recording-audio note)
           ;; Delete the text file
           (delete-file note t))
         (when (buffer-modified-p)
           (save-buffer))))))
  ad-do-it
  (org-ext-fit-agenda-window))

(defun org-ext-agenda-show (&optional _arg)
  "Display Org file containing item at point."
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
  "Display Org file containing item at point.
When called repeatedly, scroll the window that is displaying the buffer.
With a `\\[universal-argument]' prefix argument ARG, display the item,
but fold drawers."
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
  "Adjust window size and layout of WIND for optimal agenda viewing.
Resizes specified window to 100 columns and fits buffer content."
  (select-window wind)
  (org-fit-window-to-buffer wind)
  (ignore-errors
    (window-resize
     wind
     (- 100 (window-width wind)) t)))

(defun org-ext-jump-to-agenda ()
  "Navigate to org agenda window, creating one if needed.
Preserves window configuration and ensures proper display setup. Uses
variable `org-agenda-files' for content sourcing."
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
  "Refresh agenda view and optimize window layout.
When ALL is non-nil, forces full refresh of all agenda buffers."
  (interactive)
  (org-agenda-redo all)
  (push-window-configuration)
  (let ((wind (selected-window)))
    (with-selected-window wind
      (org-fit-window-to-buffer wind)
      (ignore-errors
        (window-resize wind (- 100 (window-width wind)) t)))))

(defun org-ext-entry-span ()
  "Return a cons cell (START . END) that spans the current Org entry.
START is the point at the beginning of the heading, obtained by
`org-back-to-heading' inside a `save-excursion'. END is the position of
the entry’s end, as returned by `org-entry-end-position'."
  (cons (save-excursion
          (or (ignore-errors (org-back-to-heading-or-point-min))
              (point-min)))
        (org-entry-end-position)))

(defmacro org-ext-with-entry-narrowed (&rest body)
  "Execute BODY with the buffer narrowed to the current Org entry.
The macro obtains the entry’s start and end positions via
`org-ext-entry-span', temporarily restricts the buffer using
`save-restriction' and `narrow-to-region', evaluates BODY, and then
restores the original restriction."
  `(cl-destructuring-bind (beg . end)
       (org-ext-entry-span)
     (save-restriction
       (narrow-to-region beg end)
       ,@body)))

(defun org-ext-entire-properties-block ()
  "Return the entire properties block, inclusive of :PROPERTIES:...:END:."
  (org-ext-with-entry-narrowed
   (goto-char (point-min))
   (cons (and (search-forward ":PROPERTIES:" nil t)
              (match-beginning 0))
         (and (re-search-forward ":END:\\s-*\n" nil t)
              (match-end 0)))))

(defun org-ext-move-properties-drawer ()
  "Move the PROPERTIES drawer to its proper location.
Returns nil if nothing was moved, otherwise it returns point
after :END:."
  (interactive)
  (org-ext-with-entry-narrowed
   (let* ((before-sha (sha1 (buffer-string)))
          (modified (buffer-modified-p)))
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
     (if (equal before-sha (sha1 (buffer-string)))
         (set-buffer-modified-p modified)))))

(defun org-ext-fix-all-properties ()
  "Reposition properties blocks throughout current buffer.
Scans all headlines and fixes misplaced property drawers."
  (interactive)
  (while (re-search-forward "^\\*" nil t)
    (ignore-errors
      (org-ext-move-properties-drawer))
    (forward-line 1)))

(defun org-ext-update-date-field ()
  "Set #+date property based on file's name timestamp.
Extracts date from filename pattern YYYYMMDD and formats as inactive timestamp."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^#\\+date:\\s-*\\(.+\\)" nil t)
      (delete-region (match-beginning 1) (match-end 1))
      (org-insert-time-stamp (current-time) t t))))

(defun org-ext-reformat-time (&optional beg end)
  "Reformat time string in selected region (BEG to END) to org standard.
Converts arbitrary time formats into canonical inactive timestamps.
Operates on region when called interactively."
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
With \\[universal-argument] ARG, regenerate ID — even if one already exists.
If ARG is repeated twice, set keyword to TODO, without logging.
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

(defun org-ext-switch-todo-link (&optional _arg)
  "Switch LINK to TODO with LINK tag, and vice-versa."
  (interactive "P")
  (let ((org-inhibit-logging t))
    (if (member "LINK" (org-get-tags))
        (progn
          (org-set-tags (delete "LINK" (org-get-tags)))
          (org-todo "LINK"))
      (org-todo "TODO")
      (org-set-tags (delete-dups (cons "LINK" (org-get-tags)))))))

(defun org-ext-todoize-region (&optional beg end arg)
  "Add standard metadata to headlines in region BEG to END.
See `org-ext-todoize', which uses argument ARG."
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
  "Search for PROPERTY, having VALUE."
  (interactive
   (list (setq org-ext-property-search-name (org-read-property-name))
         (completing-read "Value: "
                          (org-property-values org-ext-property-search-name))))
  (let ((org-use-property-inheritance
         (append org-use-property-inheritance '("WITH"))))
    (org-tags-view
     t (format "%s={%s}&TODO={TODO\\|WAIT\\|TASK}" property value))))

(defun org-ext-created-from-stamp ()
  "Set CREATED property using filename-based timestamp.
Derives date from YYYYMMDD filename pattern for journal entries."
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
  "Insert org structure template having TYPE and paste content.
Intended for use with yasnippet or similar expansion systems."
  (interactive
   (list (pcase (org--insert-structure-template-mks)
	   (`("\t" . ,_) (read-string "Structure type: "))
	   (`(,_ ,choice . ,_) choice))))
  (org-insert-structure-template type)
  (yank))

(defun org-ext-parent-priority ()
  "Get priority from closest parent heading.
Returns priority letter (A-C) or nil if none found."
  (save-excursion
    (org-up-heading-safe)
    (save-match-data
      (beginning-of-line)
      (and (looking-at org-heading-regexp)
	   (org-get-priority (match-string 0))))))

(defsubst org-ext-agenda-files-except (&rest args)
  "Return agenda files excluding those matching ARGS.
Used to filter out special directories from agenda views."
  (cl-set-difference org-agenda-files args))

(defun org-ext-entry-get-immediate (property)
  "Get PROPERTY value without inheritance.
Returns first matching property in current entry."
  (save-excursion
    (let ((local (org--property-local-values property nil)))
      (and local (mapconcat #'identity
                            (delq nil local)
                            (org--property-get-separator property))))))

(defun org-ext-category-p ()
  "A category is any heading that has a CATEGORY property."
  (ignore-errors
    (and (not (org-entry-is-todo-p))
         (org-ext-entry-get-immediate "CATEGORY"))))

(defun org-ext--first-child-todo (&optional pred)
  "Internal function to find child todo entries.
Optionally accepts PRED to filter child entries."
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
  "Return point of first child todo entry.
Useful for determining project status in org hierarchy.
Optionally accepts PRED to filter child entries."
  (catch 'has-child-todo (org-ext--first-child-todo pred)))

(defun org-ext-project-p ()
  "A project is any open todo that has child tasks at any level."
  (ignore-errors
    (and (org-entry-is-todo-p)
         (org-ext-first-child-todo))))

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
  "Return non-nil if current heading has a preceding TODO in parent.
Checks ancestors for todo entries while avoiding infinite recursion loops.
Uses `org-up-heading-safe' and `org-ext-task-p' for heading validation."
  (let ((here (point)))
    (save-excursion
      (when (org-up-heading-safe)
        (let ((first-child (and (org-ext-task-p)
                                (org-ext-first-child-todo))))
          (and first-child
               (or (/= first-child here)
                   (org-ext-has-preceding-todo-p))))))))

(defun org-ext-agenda-files-but-not-meetings ()
  "Return agenda files excluding meeting and Assembly directories.
Filters out files matching regex patterns from the function
`org-agenda-files'. Uses `cl-delete-if' and `string-match-p' for path
filtering."
  (cl-delete-if
   (apply-partially #'string-match-p
                    "/\\(meeting\\|local-spiritual-assembly\\)/")
   (org-agenda-files)))

(defun org-ext-team-files ()
  "Get all .org files in positron/team directory as agenda files.
Expands path from `org-directory' variable and returns file names.
Uses `directory-files' with full path and .org extension filter."
  (directory-files (expand-file-name "positron/team" org-directory)
                   t "\\.org\\'"))

(defun org-ext-refine-refile-targets (orig-func &optional default-buffer)
  "Refine refile targets to include only files matching the pattern.
Uses rx syntax to match either '/' or specific org directory name.
Removes invalid targets via `cl-delete-if'.
This is intended to be used by `advice-add', so that ORIG-FUNC is called
with the passed argument DEFAULT-BUFFER."
  (let ((targets (funcall orig-func default-buffer)))
    (cl-delete-if
     #'(lambda (target)
         (not (string-match-p
               (eval `(rx
                       (group
                        (or "/"
                            (seq bos
                                 ,(file-name-nondirectory
                                   org-constants-plain-org-path)
                                 eos)))))
               (car target))))
     targets)))

(defun org-ext-refile-heading-p ()
  "Check if current heading is a valid refile target heading.
Returns t when either has explicit REFILE property with value
other than \"no\", or is a category or project heading."
  (let ((refile (org-ext-entry-get-immediate "REFILE")))
    (if refile
        (not (string= refile "no"))
      (or (org-ext-category-p)
          (org-ext-project-p)))))

(defun org-ext-sort-all ()
  "Sort all valid headings in the buffer by priority and order.
Iterates through headlines and sorts TODO entries by property values.
Silently handles errors during sorting operations."
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
  "Copy current entry's ID to kill ring and display notification.
If no ID exists, creates one before copying. Shows message with the copied ID."
  (interactive)
  (org-id-copy)
  (message "Copied id:%s to the kill ring" (car kill-ring)))

;;; From https://gist.github.com/MenacingMecha/11bd07daaaac790620b5fe0437e96a4c
(defun org-ext-set-blocker-from-clipboard-id ()
  "Add id in clipboard (obtained using `org-id-copy') to BLOCKER property."
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

(defun org-ext-chain-blockers-in-region (beg end)
  "Chain tasks in region BEG to END with BLOCKER dependencies.
Each task blocked by previous task. Creates IDs if needed.
Returns count of tasks chained."
  (interactive "r")
  (unless (derived-mode-p 'org-mode)
    (user-error "Not in org buffer"))
  (save-excursion
    (goto-char beg)
    (let ((end-marker (copy-marker end))
          (ids nil)
          (count 0)
          (first-heading t))
      ;; First pass: collect heading IDs
      (while (and (< (point) end-marker)
                  (re-search-forward org-heading-regexp end-marker t))
        (save-excursion
          (org-back-to-heading t)
          (push (org-id-get-create) ids)))
      (setq ids (nreverse ids))
      ;; Second pass: set BLOCKER properties
      (goto-char beg)
      (while (and (< (point) end-marker)
                  (re-search-forward org-heading-regexp end-marker t))
        (save-excursion
          (org-back-to-heading t)
          (if first-heading
              (setq first-heading nil)
            (let* ((prev-id (car ids))
                   (blocker-prop "BLOCKER")
                   (blocker-existing (org-entry-get nil blocker-prop 'selective))
                   (blocker-base (or blocker-existing "ids()"))
                   (blocker-value
                    (with-temp-buffer
                      (insert blocker-base)
                      (backward-char)
                      (when blocker-existing
                        (insert " "))
                      (insert "id:" prev-id)
                      (buffer-string))))
              (org-set-property blocker-prop blocker-value)
              (setq count (1+ count))))
          (setq ids (cdr ids))))
      (set-marker end-marker nil)
      (message "Chained %d task%s with blocker dependencies"
               count (if (= count 1) "" "s"))
      count)))

;;; From https://mbork.pl/2024-08-19_Opening_all_links_in_an_Org_subtree
(defun org-ext-open-all-links-in-subtree ()
  "Open all links in current subtree.
Uses internal `org-link--search-failed' variable.
Silently opens all links until no more can be opened. For link navigation."
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
  "Get current entry's level and specified PROPS as list.
Converts \"ITEM_BY_ID\" prop to a link using ID and ITEM properties.
Returns cons cell: (level . property-values)"
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
1. There is no LAST_REVIEW property
2. The NEXT_REVIEW property has passed"
  (or (not (org-review-last-review-prop nil))
      (org-review-toreview-p)))

(defun org-ext-report-items-to-be-reviewed ()
  "Report items pending review after one second.
Uses `org-ql-query' to find tasks that need review based on:
- Active todo status
- Missing ARCHIVE tag
- Presence of SCHEDULED/DEADLINE or active timestamp"
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

(defcustom org-ext-link-names nil
  "A list of ids and their associated names used by `org-ext-edit-link-name'."
  :group 'org-ext
  :type '(repeat (cons string string)))

(defun org-ext-edit-link-name (name)
  "Replace current Org link description with NAME while preserving ID.
NAME is selected via completion from `org-ext-link-names' list.
Interactive: selects from available link names."
  (interactive
   (list (completing-read "Name: " (mapcar #'car org-ext-link-names))))
  (save-excursion
    (goto-char (line-beginning-position))
    (when (re-search-forward "\\[\\[\\([^]]+?\\)\\]\\[\\([^]]+?\\)\\]\\]" nil t)
      (replace-match name t t nil 2))))

(defun org-ext-swap-link-name ()
  (interactive)
  (save-excursion
    (goto-char (line-beginning-position))
    (when (re-search-forward
           "\\[\\[\\([^]]+?\\)\\]\\[\\([^]]+?\\)\\]\\]: \\(\\([A-Za-z -]+ *\\)[^\n]*\n+\\)" nil t)
      (let* ((name (string-trim (match-string 4)))
             (parts (save-match-data (split-string name))))
        (when (> (length parts) 2)
          (setq name (mapconcat #'identity
                                (list (nth 0 parts) (nth 1 parts)) " ")))
        (replace-match name t t nil 2)
        (delete-region (match-beginning 3) (match-end 3))))))

(defun org-ext-fixup-slack (&optional arg)
  "Convert Slack web export format to clean Org mode conversation format.

Transforms Slack export structure where each message consists of:
  - Timestamp link: [[https://...slack.com/.../p<timestamp>][TIME]]
  - Author name on separate line(s) (may be absent for continuation)
  - Message content after blank lines

Into compact format:
  [[timestamp-url][Author Name]]: message content...

Handles continuation messages (same author posting multiple times in quick
succession) by detecting when a timestamp has no author name following it
and using the previous message's author.

Performs these transformations:
  - Combines timestamp link + author + content into single attribution line
  - Merges consecutive messages from the same author
  - Replaces \"John Wiegley\" with \"Me\" in author names
  - Converts #+begin_src blocks to #+begin_example blocks
  - Removes emoji reaction images (slack-edge.com/emoji-assets)
  - Removes avatar images (ca.slack-edge.com user photos)
  - Removes Slack link unfurl images and metadata
  - Removes \"(edited)\" markers and inline reaction counts
  - Removes \"Saved for later\" lines
  - Removes thread reply indicators and date separators
  - Removes file attachment blocks (Binary markers + file links)
  - Removes link unfurl attributions (\"Name:\" followed by URL)
  - Preserves @mention links and code blocks
  - Joins orphan punctuation to preceding lines
  - Normalizes blank lines (single blank between messages)
  - Works with any .slack.com domain

When ARG is non-nil, skips final `fill-region' call for
multi-line preservation."
  (interactive "P")

  ;; Phase 1: Initial cleanup of noise patterns from Slack export
  (save-excursion
    ;; 1a. Non-breaking spaces
    (goto-char (point-min))
    (while (search-forward " " nil t)
      (replace-match " "))
    (whitespace-cleanup)

    ;; 1b. "(edited)" markers (with or without leading space)
    (goto-char (point-min))
    (while (re-search-forward " ?(edited)" nil t)
      (replace-match ""))

    ;; 1c. "Saved for later" lines
    (goto-char (point-min))
    (while (re-search-forward "^Saved for later\\.?\\s-*$" nil t)
      (delete-region (match-beginning 0)
                     (min (1+ (match-end 0)) (point-max))))

    ;; 1d. Emoji reaction images (inline emoji from slack-edge.com)
    (goto-char (point-min))
    (while (re-search-forward
            "\\[\\[https://[^]]*?slack-edge\\.com/[^]]*?emoji[^]]+?\\]\\]"
            nil t)
      (delete-region (match-beginning 0) (match-end 0)))

    ;; 1e. Avatar images (ca.slack-edge.com user photos, typically small)
    (goto-char (point-min))
    (while (re-search-forward
            "\\[\\[https://ca\\.slack-edge\\.com/[^]]+\\]\\]"
            nil t)
      (delete-region (match-beginning 0) (match-end 0)))

    ;; 1f. Slack link unfurl preview images (slack-imgs.com)
    (goto-char (point-min))
    (while (re-search-forward
            "\\[\\[https://slack-imgs\\.com/[^]]+\\]\\]"
            nil t)
      (delete-region (match-beginning 0) (match-end 0)))

    ;; 1g. Duplicate timestamp text after links (e.g., "]]11:50 AM.")
    (goto-char (point-min))
    (while (re-search-forward "\\]\\][0-9]+:[0-9]+ [AP]M\\.?" nil t)
      (replace-match "]]"))

    ;; 1h. Service attribution lines (Created by...|...|Added by...)
    (goto-char (point-min))
    (while (re-search-forward "^.*Created by .+|.+|.*Added by.*$" nil t)
      (delete-region (line-beginning-position)
                     (min (1+ (line-end-position)) (point-max))))

    ;; 1i. Thread reply indicators -- "N replies" and "Last reply...View thread"
    (goto-char (point-min))
    (while (re-search-forward "^[0-9]+ repl\\(?:y\\|ies\\)\\s-*$" nil t)
      (delete-region (match-beginning 0)
                     (min (1+ (match-end 0)) (point-max))))
    (goto-char (point-min))
    (while (re-search-forward "^Last reply.*$" nil t)
      (delete-region (match-beginning 0)
                     (min (1+ (match-end 0)) (point-max))))

    ;; 1j. Date separator lines (standalone day names)
    (goto-char (point-min))
    (while (re-search-forward
            (concat "^\\(?:"
                    "Today\\|Yesterday"
                    "\\|Monday\\|Tuesday\\|Wednesday"
                    "\\|Thursday\\|Friday\\|Saturday\\|Sunday"
                    "\\)\\s-*$")
            nil t)
      (delete-region (match-beginning 0)
                     (min (1+ (match-end 0)) (point-max))))

    ;; 1k. Trailing reaction/attachment/link count summaries
    ;; e.g., ".1 reaction, 1 attachment.1 link,"
    (goto-char (point-min))
    (while (re-search-forward
            "[.,]?[0-9]+ \\(?:reactions?\\|attachments?\\|links?\\)[.,].*$"
            nil t)
      (replace-match ""))

    ;; 1l. Standalone reaction counts (just a number on its own line)
    (goto-char (point-min))
    (while (re-search-forward "^[0-9]+\\s-*$" nil t)
      (delete-region (match-beginning 0)
                     (min (1+ (match-end 0)) (point-max))))

    ;; 1m. File attachment blocks -- multi-line links to files.slack.com
    ;; These often appear as broken multi-line org links in the export
    (goto-char (point-min))
    (while (re-search-forward
            "\\[\\[https://files\\.slack\\.com/" nil t)
      (let ((start (match-beginning 0)))
        ;; Find the closing ]] which may be on a later line
        (if (re-search-forward "\\]\\]" nil t)
            (delete-region start (match-end 0))
          ;; No closing brackets found; delete to end of line
          (delete-region start (line-end-position)))))

    ;; 1n. Standalone "Binary" lines (file attachment markers)
    (goto-char (point-min))
    (while (re-search-forward "^Binary\\s-*$" nil t)
      (delete-region (match-beginning 0)
                     (min (1+ (match-end 0)) (point-max))))

    ;; 1o. Stray closing brackets from broken multi-line links
    (goto-char (point-min))
    (while (re-search-forward "^\\]\\]\\s-*$" nil t)
      (delete-region (match-beginning 0)
                     (min (1+ (match-end 0)) (point-max))))

    ;; 1p. Link unfurl attributions: "Name:" line followed by a URL-only line.
    ;; Only remove "Name:" when the next non-blank line is a standalone link
    ;; whose display text is also a URL (indicating a Slack link unfurl, not
    ;; real content).
    (goto-char (point-min))
    (let ((case-fold-search nil))
    (while (re-search-forward
            "^[A-Z][a-z'-]\\{1,20\\}\\(?: [A-Z][a-z'-]\\{1,20\\}\\)*:\\s-*$"
            nil t)
      (let ((name-start (match-beginning 0))
            (name-end (match-end 0)))
        (save-excursion
          (goto-char name-end)
          (skip-chars-forward " \t\n")
          (if (looking-at
               "\\[\\[https?://[^]]+\\]\\[https?://[^]]+\\]\\]\\s-*$")
              ;; Remove both the "Name:" line and the unfurl URL line
              (delete-region name-start
                            (min (1+ (match-end 0)) (point-max)))
            ;; Not followed by URL -- leave it alone
            (goto-char name-end))))))

    ;; 1q. Join orphan punctuation to previous line
    (goto-char (point-min))
    (while (re-search-forward "\n\n\\([?!.]\\)\\s-*$" nil t)
      (replace-match "\\1"))

    ;; 1r. Interim cleanup of excessive blank lines
    (goto-char (point-min))
    (while (re-search-forward "\n\n\n+" nil t)
      (replace-match "\n\n")))

  ;; Phase 2: Structure transformation - parse and rebuild messages
  (save-excursion
    (let ((messages nil)
          (known-authors (make-hash-table :test 'equal))
          (last-author nil)
          (todo-line nil))

      ;; Preserve "* TODO" line at start if present
      (goto-char (point-min))
      (when (looking-at "^\\*+ TODO.*\n")
        (setq todo-line (match-string 0))
        (delete-region (match-beginning 0) (match-end 0)))

      ;; Parse all messages from buffer
      (goto-char (point-min))
      (while (re-search-forward
              "^\\[\\[\\(https://[^]]*?\\.slack\\.com/archives/[^]]+?\\)\\]\\[\\([^]]+?\\)\\]\\]"
              nil t)
        (let* ((timestamp-url (match-string 1))
               (msg-start (match-end 0))
               (author nil)
               (content nil)
               (next-timestamp-pos
                (save-excursion
                  (if (re-search-forward
                       "^\\[\\[https://[^]]*?\\.slack\\.com/archives/"
                       nil t)
                      (match-beginning 0)
                    (point-max)))))

          (goto-char msg-start)
          (forward-line 1)
          ;; Skip blank lines after timestamp
          (while (and (< (point) next-timestamp-pos)
                      (looking-at "^[[:space:]]*$"))
            (forward-line 1))

          (when (< (point) next-timestamp-pos)
            (let* ((first-line
                    (string-trim
                     (buffer-substring-no-properties
                      (line-beginning-position) (line-end-position))))
                   (is-continuation nil)
                   ;; Author detection: 1-4 capitalized words, each starting
                   ;; with uppercase, optionally containing hyphens/apostrophes.
                   ;; Must be short, must not contain content markers, and must
                   ;; be followed by a blank line (author lines always are in
                   ;; Slack exports).
                   ;; N.B. case-fold-search must be nil so [A-Z] won't match
                   ;; lowercase letters.
                   (looks-like-author
                    (let ((case-fold-search nil))
                      (and (< (length first-line) 40)
                           (string-match-p
                            "^[A-Z][a-z'-]+\\(?: [A-Z][a-z'-]+\\)*$"
                            first-line)
                           ;; Exclude lines containing content markers
                           (not (string-match-p "[][#:>=;()\"]" first-line))
                           ;; Exclude known non-author words that happen to
                           ;; be capitalized
                           (not (member first-line
                                        '("Binary" "Today" "Yesterday"
                                          "Monday" "Tuesday" "Wednesday"
                                          "Thursday" "Friday" "Saturday"
                                          "Sunday" "Edited" "View")))
                           ;; Author lines in Slack export are always followed
                           ;; by a blank line before content
                           (save-excursion
                             (forward-line 1)
                             (or (>= (point) next-timestamp-pos)
                                 (looking-at "^[[:space:]]*$")))))))

              (if looks-like-author
                  (progn
                    (setq author first-line)
                    (when (string-equal author "John Wiegley")
                      (setq author "Me"))
                    (puthash first-line t known-authors)
                    (setq last-author author)
                    (forward-line 1)
                    ;; Skip blank lines after author
                    (while (and (< (point) next-timestamp-pos)
                                (looking-at "^[[:space:]]*$"))
                      (forward-line 1)))
                (setq author (or last-author "Unknown"))
                (setq is-continuation t))

              (when (< (point) next-timestamp-pos)
                (setq content
                      (string-trim
                       (buffer-substring-no-properties
                        (point) next-timestamp-pos))))

              (when (and author (or content (not messages)))
                (push (list :url timestamp-url
                            :author author
                            :content (or content "")
                            :continuation is-continuation)
                      messages))))))

      ;; Rebuild buffer with transformed messages
      (setq messages (nreverse messages))
      (when messages
        (delete-region (point-min) (point-max))
        ;; Restore TODO line if it was present
        (when todo-line
          (insert todo-line))
        (let ((first-msg t))
          (dolist (msg messages)
            (let ((author (plist-get msg :author))
                  (url (plist-get msg :url))
                  (content (plist-get msg :content))
                  (is-continuation (plist-get msg :continuation)))
              (if is-continuation
                  (when (and content (not (string-empty-p content)))
                    (insert "\n\n" content))
                (unless first-msg
                  (insert "\n\n"))
                (insert "[[" url "][" author "]]: " content)
                (setq first-msg nil))))))))

  ;; Phase 3: Convert src blocks to example blocks
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^#\\+begin_src\\(?: +[^ \n]+\\)?\\s-*$" nil t)
      (replace-match "#+begin_example"))
    (goto-char (point-min))
    (while (re-search-forward "^#\\+end_src\\s-*$" nil t)
      (replace-match "#+end_example")))

  ;; Phase 4: Final cleanup
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "\n\n\n+" nil t)
      (replace-match "\n\n"))
    (whitespace-cleanup)
    (goto-char (point-max))
    (delete-blank-lines)
    (unless (bolp)
      (insert "\n")))

  ;; Optional: Fill paragraphs (skip if ARG provided)
  (unless arg
    (save-excursion
      (goto-char (point-min))
      (while (looking-at "^#")
        (forward-line 1))
      (fill-region (point) (point-max)))))

;;; This function was inspired by Sacha Chua at:
;;; https://sachachua.com/blog/2024/10/org-mode-prompt-for-a-heading-and-then-refile-it-to-point/
(defun org-ext-move-subtree-to-point (uuid)
  "Prompt for a heading and refile it to point using UUID.
Narrows to heading with `org-id-find', copies subtree, and pastes at
current location."
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
  "Remove LOGBOOK entries older than DAYS days.
Narrow to LOGBOOK section and delete entries beyond age threshold.
DAYS is the number of days to retain history."
  (interactive "Number of days to keep: ")
  (org-ext-with-entry-narrowed
   (goto-char (point-min))
   (let* ((beg (progn
                 (re-search-forward "^:LOGBOOK:\n")
                 (point)))
          (end (progn
                 (re-search-forward "^:END:\n")
                 (match-beginning 0))))
     (save-restriction
       (narrow-to-region beg end)
       (goto-char (point-min))
       (while (re-search-forward "- State.*\\(\\[[-:0-9A-Z ]+\\]\\)" nil t)
         (let* ((start (match-beginning 0))
                (date (match-string 1))
                (age (- (time-to-days (current-time))
                        (time-to-days (org-encode-time
                                       (org-parse-time-string date))))))
           (if (> age days)
               (delete-region start (point-max)))))))))

(defun org-ext-prune-ninety-days-of-logs ()
  "Prune log entries older than 90 days.
Calls `org-ext-prune-log-entries' with fixed 90-day parameter."
  (interactive)
  (org-ext-prune-log-entries 90))

(defun org-ext-read-names (file)
  "Read link names from FILE's table and return as list.
Parses table entries in format [[id:...][NAME]] with optional page links.
Used to populate `org-ext-link-names' list."
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
  "Update `org-ext-link-names' and keybindings from team.org file.
Reads names from file and defines s-KEY shortcuts to call
`org-ext-edit-link-name' with the appropriate name."
  (interactive)
  (let ((file (org-file org-constants-positron-team-file)))
    (setq org-ext-link-names (org-ext-read-names file))
    (with-current-buffer (find-file-noselect file)
      (save-excursion
        (while (re-search-forward
                "^| \\[\\[id:.+?\\]\\[\\(.+?\\)\\]\\].+|\\s-+\\([A-Za-z0-9_]\\)\\s-+|$" nil t)
          (let ((name (match-string-no-properties 1))
                (key (match-string-no-properties 2)))
            (org-defkey org-mode-map (kbd (concat "s-" key))
                        `(lambda ()
                           (interactive)
                           (org-ext-edit-link-name ,name)))))))
    (message "Team names and quick keys updated")))

(defun org-ext-update-team-after-save ()
  "Hook function to update team when team.org is saved.
Checks buffer filename against `org-constants-positron-team-file' to avoid
processing unrelated buffers."
  (when (and (eq major-mode 'org-mode)
             (string-match org-constants-positron-team-file (buffer-file-name)))
    (org-ext-update-team)))

(defun org-ext-unlink-region (&optional beg end)
  "Remove Org link markup in region from BEG to END.
If BEG and END not specified, operates on entire buffer.
Replaces [[link][description]] with plain description."
  (interactive)
  (save-restriction
    (narrow-to-region (or beg (point-min)) (or end (point-max)))
    (goto-char (point-min))
    (while (re-search-forward org-link-bracket-re nil t)
      (replace-match (match-string 2)))))

(defun org-ext-follow-tag-link (tag)
  "Display a list of TODO headlines with TAG.
With prefix argument, also display headlines without TODO keyword.
Uses `org-tags-view' for filtering."
  (org-tags-view (null current-prefix-arg) tag))

(defun org-ext-yank-link ()
  "Insert all clipboard links as plain text with custom formatting.
Uses `org-insert-all-links' with headline prefix *** and line break."
  (interactive)
  (org-insert-all-links nil "*** " "\n"))

(defun org-ext-gnus-drop-link-parameter (param)
  "Remove PARAM from `org-link-parameters'.
Prevents org-link from interpreting specific link types.
Useful for cleaning up custom link handlers."
  (setq org-link-parameters
        (cl-delete-if #'(lambda (x) (string= (car x) param))
                      org-link-parameters)))

(defun org-ext-message-reply ()
  "Compose email reply to message linked in current Org entry.
Extracts Author and Subject properties from the entry for email header."
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
  "Sort DONE tasks by inactive timestamp and clean empty lines.
Groups completed tasks together and removes extra newlines.
Intended for task management workflow optimization."
  (interactive)
  (goto-char (point-min))
  (org-sort-entries t ?F #'org-ext-get-inactive-time #'<)
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
  "Create message:// link for current Gnus article.
TITLE optionally specifies the link description text."
  (let (message-id subject)
    (with-current-buffer gnus-original-article-buffer
      (setq message-id (substring (message-field-value "message-id") 1 -1)
            subject (or title (message-field-value "subject"))))
    (org-link-make-string (concat "message://" message-id)
                          (rfc2047-decode-string subject))))

(defun org-ext-insert-message-link (&optional arg)
  "Insert message link at point with optional label.
With prefix ARG, uses \"writes\" as link label instead of subject."
  (interactive "P")
  (insert (org-ext-get-message-link (if arg "writes"))))

(defun org-ext-set-message-link ()
  "Set Message property to message:// link of current article.
Associates Org entry with Gnus email for reference tracking."
  (interactive)
  (org-set-property "Message" (org-ext-get-message-link)))

(defun org-ext-get-message-sender ()
  "Get sender of current Gnus article.
Returns raw From: header for use in Org property storage."
  (with-current-buffer gnus-original-article-buffer
    (message-field-value "from")))

(defun org-ext-set-message-sender ()
  "Set Submitter property to current article's sender.
Stores the Gnus From: header as Org property."
  (interactive)
  (org-set-property "Submitter" (org-ext-get-message-sender)))

(defun org-ext-set-url-from-clipboard (&optional arg)
  "Set URL property from clipboard content.
If ARG is non-nil, uses stored links instead of clipboard. Toggles LINK tag.
Preserves existing URL2 property when URL exists."
  (interactive "P")
  (org-back-to-heading)
  (org-set-property (if (org-entry-get (point-marker) "URL") "URL2" "URL")
                    (if (and arg org-stored-links)
                        (concat "[[" (caar org-stored-links) "]]")
                      (gui--selection-value-internal 'CLIPBOARD)))
  (org-toggle-tag "LINK" 'on))

(defun org-ext-set-stored-link ()
  "Set a property for the current headline."
  (interactive)
  (org-ext-todoize)
  (org-set-property (if (org-entry-get (point-marker) "URL") "URL2" "URL")
                    (format "[[%s][%s]] "
                            (caar org-stored-links)
                            (cdar org-stored-links)))
  (org-toggle-tag "LINK" 'on))

(defun org-ext-capture-link-to-entry ()
  "Capture a new task linked back to the current Org entry.
Uses `org-smart-capture' to start a new capture, then sets the :LINK:
tag and :URL: property pointing to the current entry via its ID."
  (interactive)
  (unless (derived-mode-p 'org-mode)
    (user-error "Not in an Org buffer"))
  (org-back-to-heading t)
  (let* ((id (org-id-get-create))
         (title (org-get-heading t t t t))
         (url (format "[[id:%s][%s]]" id title)))
    (org-smart-capture)
    (org-set-property "URL" url)
    (org-toggle-tag "LINK" 'on)
    (insert " ")))

(defun org-ext-get-inactive-time ()
  "Get time of last state change or creation as float.
Uses `org-encode-time' and `org-time-string-to-time' for conversion.
Falls back to current time when no valid timestamp found."
  (float-time (org-time-string-to-time
               (or (org-entry-get (point) "TIMESTAMP")
                   (org-entry-get (point) "TIMESTAMP_IA")
                   (org-entry-get (point) "CREATED")
                   (debug)))))

(defun org-ext-open-map-link ()
  "Open Apple Maps with location coordinates from LOCATION property.
Requires Apple Maps on macOS and osm package for alternative view.
Error when no LOCATION property exists."
  (interactive)
  (let ((location (org-entry-get (point) "LOCATION")))
    (if location
        (if (featurep 'osm)
            (pcase (split-string location ",")
              (`(,lat ,lon)
               (funcall #'osm-goto (string-to-number lat)
                        (string-to-number lon) nil)))
          (browse-url (concat "https://maps.apple.com/?q=org&ll=" location)))
      (error "Entry has no location set"))))

(defun org-ext-linkify ()
  "Convert plain text references to Org links.
Handles:
- VER/SDK references (e.g., \"VER-123\")
- Quill issue references (e.g., \"quill#123\")"
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward " \\(\\(VER\\|SDK\\)-\\([0-9]+\\)\\) " nil t)
    (replace-match (format " [[%s:\\3][\\2-\\3]] " (downcase (match-string 2))) t)
    (goto-char (match-end 0)))
  (while (re-search-forward " \\(\\(quill\\)#\\([0-9]+\\)\\) " nil t)
    (replace-match (format " [[%s:\\3][\\2#\\3]] " (downcase (match-string 2))) t)
    (goto-char (match-end 0))))

(defun org-ext-save-org-mode-files ()
  "Save all modified Org-mode buffers with associated files.
Intended for use in buffer management hooks to auto-save changes."
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq major-mode 'org-mode)
        (if (and (buffer-modified-p) (buffer-file-name))
            (save-buffer))))))

(defun org-ext-current-tags (depth)
  "Get tags at DEPTH levels up in heading hierarchy.
Returns nil if current heading lacks tags at specified depth.
Used for contextual tag inheritance."
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
  "Collect todo keywords from ancestor headings in hierarchy.
Returns list of todo states from parent headings above current entry.
Uses recursive ascent with `org-up-heading-safe'."
  (save-excursion
    (let ((had-parent (org-up-heading-safe)))
      (delete nil
              (cons (org-get-todo-state)
                    (when had-parent
                      (org-ext-ancestor-keywords)))))))

(defun org-ext-insert-code-block ()
  "Convert triple-backtick to Org code block.
Triggers when three backticks are typed in sequence. Sets appropriate language."
  (when (let* ((keys (recent-keys))
               (n (length keys)))
          (and (eq ?` (aref keys (- n 1)))
               (eq ?` (aref keys (- n 2)))
               (eq ?` (aref keys (- n 3)))))
    (delete-char -3)
    (let ((language
           (or (save-excursion
                 (re-search-backward "#\\+begin_src \\([^ \t\n]+\\)" nil t)
                 (match-string 1))
               "sh")))
      (insert "#+begin_src " language "\n\n#+end_src")
      (forward-line -1))))

(defsubst org-ext-setup-insert-code-block ()
  "Setup hook to auto-create code blocks after triple-backtick.
Adds `org-ext-insert-code-block' to `post-self-insert-hook'."
  (add-hook 'post-self-insert-hook #'org-ext-insert-code-block nil t))

(defun org-ext-get-all-categories (&optional files)
  "Return a list of all unique categories used in org FILES.
If FILES is nil, use `org-agenda-files'.
Uses org-ql for efficient searching."
  (interactive)
  (let* ((files (or files (org-agenda-files)))
         (categories '()))
    ;; Use org-ql to search all entries and collect their categories
    (org-ql-select files
      '(category) ;; Match all entries with any category
      :action (lambda ()
                (when-let ((cat (org-get-category)))
                  (cl-pushnew cat categories :test #'string=))))
    ;; Sort the categories alphabetically
    (sort categories #'string<)))

(defun org-ext-get-all-categories-detailed (&optional files include-counts)
  "Return all unique categories used in org FILES.
If FILES is nil, use `org-agenda-files'.
If INCLUDE-COUNTS is non-nil, return an alist of (category . count) pairs.
Uses org-ql for efficient searching."
  (interactive (list nil t))
  (let* ((files (or files (org-agenda-files)))
         (categories (if include-counts
                         (make-hash-table :test #'equal)
                       '())))
    ;; Use org-ql to search all entries
    (org-ql-select files
      t ;; Match all entries
      :action (lambda ()
                (when-let ((cat (org-get-category)))
                  (if include-counts
                      (puthash cat (1+ (gethash cat categories 0)) categories)
                    (cl-pushnew cat categories :test #'string=)))))
    ;; Process and return results
    (if include-counts
        (let ((result '()))
          (maphash (lambda (cat count)
                     (push (cons cat count) result))
                   categories)
          (sort result (lambda (a b) (string< (car a) (car b)))))
      (sort categories #'string<))))

(defun org-ext-get-categories-by-file (&optional files)
  "Return an alist of (file . categories) for org FILES.
If FILES is nil, use `org-agenda-files'.
Each file is mapped to a list of unique categories used in that file."
  (interactive)
  (let* ((files (or files (org-agenda-files)))
         (result '()))
    (dolist (file files)
      (let ((file-categories '()))
        (org-ql-select file
          t ;; Match all entries
          :action (lambda ()
                    (when-let ((cat (org-get-category)))
                      (cl-pushnew cat file-categories :test #'string=))))
        (when file-categories
          (push (cons file (sort file-categories #'string<)) result))))
    (nreverse result)))

(defun org-ext-show-all-categories ()
  "Display all categories used in the current Org project.
Shows categories with their usage counts in a temporary buffer."
  (interactive)
  (let* ((categories-with-counts (org-ext-get-all-categories-detailed nil t))
         (total-categories (length categories-with-counts))
         (total-entries (apply #'+ (mapcar #'cdr categories-with-counts))))
    (with-current-buffer (get-buffer-create "*Org Categories*")
      (erase-buffer)
      (insert (format "Org Categories Summary\n"))
      (insert (format "======================\n"))
      (insert (format "Total categories: %d\n" total-categories))
      (insert (format "Total categorized entries: %d\n\n" total-entries))
      (insert "Category                     Count\n")
      (insert "--------                     -----\n")
      (dolist (cat-count categories-with-counts)
        (insert (format "%-28s %5d\n" (car cat-count) (cdr cat-count))))
      (goto-char (point-min))
      (read-only-mode 1)
      (display-buffer (current-buffer)))))

(defvar org-ext-category-history nil)

(defun org-ext-set-category (category)
  "Set the category of the current Org-mode element to CATEGORY."
  (interactive
   (list (completing-read "Category: " (org-ext-get-all-categories)
                          nil nil nil 'org-ext-category-history)))
  (org-set-property "CATEGORY" category))

(defun org-ext-set-id-and-created (&optional arg)
  (org-id-get-create arg)
  (unless (org-entry-get (point) "CREATED")
    (org-entry-put (point) "CREATED"
                   (format-time-string (org-time-stamp-format t t)))))

(defun org-ext-quickping (host)
  (= 0 (call-process "ping" nil nil nil "-c1" "-W5" "-q" host)))

(defun org-ext-get-location ()
  "If possible, add location info. We know the location at home always."
  (if (and nil (org-ext-quickping "192.168.3.2"))
      '("38.569498" "-121.388618")
    (let ((strs
           (split-string
            (string-trim
             (shell-command-to-string "CoreLocationCLI")))))
      (if (= 2 (length strs))
          strs
        (message "Failed to obtain Lat/Lon!")
        '("" "")))))

(defun org-ext-set-location (&optional _arg)
  "If possible, add location info. We know the location at home always."
  (cl-destructuring-bind (lat lon)
      (org-ext-get-location)
    (unless (string= lat "")
      (org-entry-put (point) "LOCATION" (concat lat "," lon)))))

(defun org-ext-set-basic-properties (&optional _arg)
  (interactive "P")
  (save-excursion
    (org-ext-set-id-and-created)
    (org-ext-set-location)))

(defun org-ext-cleanup-whitespace (&optional _arg)
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (search-forward " " nil t)
      (replace-match  " "))
    (whitespace-cleanup)
    (goto-char (point-max))
    (delete-blank-lines)
    (if (looking-at "^$")
        (delete-char -1))))

(defun org-ext-fill-body ()
  "Fill body paragraph of the current Org heading, skipping properties.

Moves to the first body paragraph after the heading and any properties
drawer, then applies `org-fill-paragraph' to reflow the text while
preserving the current position."
  (interactive)
  (save-excursion
    (forward-line)
    (when (looking-at-p ":PROPERTIES:")
      (re-search-forward ":END:")
      (forward-line))
    (org-fill-paragraph)))

(provide 'org-ext)

;;; org-ext.el ends here
