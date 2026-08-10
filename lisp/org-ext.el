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
(declare-function org-contacts-filter "org-contacts")
(declare-function org-ql-ext-get-all-verbs "org-ql-ext")
(declare-function mdformat-buffer "mdformat")
(declare-function org-capture-get "org-capture" (&optional key local))
(defvar org-export-filter-options-functions)

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
    (widen)
    (goto-char (point-min))
    (while (looking-at "^[:#]")
      (forward-line 1))
    (unless (looking-at "^$")
      (error "Missing blank line after file header in %s" path))
    (forward-line 1)
    (unless (looking-at "^\\* Inbox$")
      (error "Missing Inbox heading at start of %s" path))))

(defun org-ext-goto-inbox (&optional func)
  "Navigate to the Inbox section in the drafts file.
When optional FUNC is provided, execute it within the Inbox context.
Interactively opens the file and positions cursor at first todo item."
  (interactive)
  (with-current-buffer
      (funcall (if func
                   #'find-file-noselect
                 #'find-file)
               org-constants-drafts-path)
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

(defcustom org-ext-recording-queue-directory
  (expand-file-name "~/.local/share/recording-transcripts")
  "Local directory containing recording transcripts awaiting Org import."
  :type 'directory
  :group 'org-ext)

(defcustom org-ext-recording-receipt-directory
  (expand-file-name ".imported" org-ext-recording-queue-directory)
  "Private acknowledgement directory for imported recording transcripts."
  :type 'directory
  :group 'org-ext)

(defcustom org-ext-recording-inbox-directories
  (list org-ext-recording-queue-directory
        (expand-file-name "~/Recordings"))
  "Directories containing recording transcript files awaiting Org import."
  :type '(repeat directory)
  :group 'org-ext)

(defun org-ext-recording-note-files ()
  "Return sorted recording transcripts awaiting Org import."
  (sort
   (delete-dups
    (cl-mapcan
     (lambda (directory)
       (and (file-directory-p directory)
            (directory-files directory t ".*\\.txt\\'" nil)))
     org-ext-recording-inbox-directories))
   #'string-lessp))

(defun org-ext-move-recording-audio (txt-file)
  "Move audio file corresponding to TXT-FILE to ~/Audio/Recordings.
Searches for audio files with the same basename as TXT-FILE but with
common audio extensions (.m4a, .mp3, .wav, .aac, .flac). If found,
moves the audio file to ~/Audio/Recordings."
  (let* ((basename (file-name-sans-extension txt-file))
         (audio-extensions '(".m4a" ".mp3" ".wav" ".aac" ".flac" ".ogg"))
         (audio-dest-dir (expand-file-name "~/Audio/Recordings"))
         ;; A transcript named "x.m4a.txt" strips to "x.m4a", so the
         ;; audio file is the stripped name itself.  Test it directly when
         ;; it already carries a supported audio extension, before
         ;; trying the synthesized "<base>.<ext>" candidates.
         (candidates
          (append
           (let ((ext (file-name-extension basename)))
             (and ext
                  (member (downcase (concat "." ext)) audio-extensions)
                  (list basename)))
           (mapcar (lambda (ext) (concat basename ext))
                   audio-extensions)))
         audio-file)
    ;; Find the first matching audio file
    (setq audio-file (cl-find-if #'file-exists-p candidates))
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
If the buffer already starts with a `** DRAFT ' or `** TODO ' heading,
do nothing (idempotent).

Otherwise, if the trimmed buffer contents are a single non-empty line
shorter than 67 characters, replace the buffer with a `** TODO <line>'
heading and no body.

In all other cases, prepend a `** DRAFT ' heading with an inactive
timestamp (including HH:MM) at point-min, leaving the body intact."
  (goto-char (point-min))
  (unless (looking-at "^\\*\\* \\(DRAFT\\|TODO\\) ")
    (let ((trimmed (string-trim (buffer-string))))
      (if (and (> (length trimmed) 0)
               (< (length trimmed) 67)
               (not (string-match-p "\n" trimmed)))
          (progn
            (erase-buffer)
            (insert "** TODO " trimmed "\n"))
        (goto-char (point-min))
        (insert "** DRAFT ")
        (org-insert-time-stamp (current-time) t t)
        (insert "\n")))))

(defun org-ext-recording-file-hash (note)
  "Return the SHA-256 digest of recording transcript NOTE contents."
  (with-temp-buffer
    (insert-file-contents-literally note)
    (secure-hash 'sha256 (current-buffer))))

(defun org-ext-recording-receipt-file (note)
  "Return the acknowledgement path for local queue transcript NOTE."
  (when (file-in-directory-p note org-ext-recording-queue-directory)
    (expand-file-name
     (concat (file-name-nondirectory note) ".sha256")
     org-ext-recording-receipt-directory)))

(defun org-ext-recording-imported-p (hash)
  "Return non-nil when the current Org buffer already records HASH."
  (save-excursion
    (goto-char (point-min))
    (re-search-forward
     (concat "^:RECORDING_TRANSCRIPT_SHA256:[ \t]+"
             (regexp-quote hash) "[ \t]*$")
     nil t)))

(defun org-ext-write-recording-receipt (note hash)
  "Atomically acknowledge imported queue transcript NOTE with HASH."
  (when-let ((receipt (org-ext-recording-receipt-file note)))
    (make-directory org-ext-recording-receipt-directory t)
    (set-file-modes org-ext-recording-receipt-directory #o700)
    (let ((temporary
           (make-temp-file
            (expand-file-name ".recording-import-"
                              org-ext-recording-receipt-directory))))
      (unwind-protect
          (progn
            (write-region (concat hash "\n") nil temporary nil 'silent)
            (set-file-modes temporary #o600)
            (rename-file temporary receipt t))
        (when (file-exists-p temporary)
          (delete-file temporary))))))

(defun org-ext--recording-hashes ()
  "Return hashes already recorded in the current Org buffer."
  (let ((hashes (make-hash-table :test #'equal)))
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward
              "^:RECORDING_TRANSCRIPT_SHA256:[ \t]+\\([[:xdigit:]]\\{64\\}\\)[ \t]*$"
              nil t)
        (puthash (match-string-no-properties 1) t hashes)))
    hashes))

(defun org-ext--insert-recording-note (note hash)
  "Insert recording transcript NOTE and associate it with HASH."
  (let ((start-pos (point)))
    (insert
     (with-temp-buffer
       (org-mode)
       (insert-file-contents note)
       (goto-char (point-min))
       (org-ext-reformat-recording)
       (goto-char (point-max))
       (unless (bolp)
         (insert ?\n))
       (buffer-string)))
    (save-excursion
      (goto-char start-pos)
      (when (re-search-forward "^\\*\\* \\(DRAFT\\|TODO\\) " nil t)
        (beginning-of-line)
        (run-hooks 'org-capture-before-finalize-hook)
        (org-set-property "RECORDING_TRANSCRIPT_SHA256" hash)))))

(defun org-ext--consume-recording-note (note hash)
  "Acknowledge imported recording NOTE with HASH, then consume it."
  (org-ext-write-recording-receipt note hash)
  (org-ext-move-recording-audio note)
  (delete-file note t))

(defun org-ext-import-recording-note (note)
  "Import recording transcript NOTE, save, acknowledge, then consume it."
  (let ((hash (org-ext-recording-file-hash note)))
    (unless (org-ext-recording-imported-p hash)
      (org-ext--insert-recording-note note hash))
    (when buffer-file-name
      (save-buffer))
    (org-ext--consume-recording-note note hash)))

(defun org-ext-fit-agenda-window ()
  "Fit the window to the buffer size."
  (and (memq org-agenda-window-setup '(reorganize-frame))
       (fboundp 'fit-window-to-buffer)
       (fit-window-to-buffer)))

(defun org-ext--import-agenda-notes (draft-notes recording-notes)
  "Import DRAFT-NOTES and RECORDING-NOTES into the current inbox.
Draft sources are deleted only after the destination buffer has been
saved successfully."
  (let ((drafts-to-consume nil)
        (recordings-to-consume nil)
        (imported (and recording-notes (org-ext--recording-hashes))))
    (dolist (note draft-notes)
      (insert
       (with-temp-buffer
         (org-mode)
         (insert-file-contents note)
         (goto-char (point-min))
         (org-ext-reformat-draft)
         (goto-char (point-max))
         (unless (bolp)
           (insert ?\n))
         (buffer-string)))
      (push note drafts-to-consume))
    (dolist (note recording-notes)
      (let ((hash (org-ext-recording-file-hash note)))
        (unless (gethash hash imported)
          (org-ext--insert-recording-note note hash)
          (puthash hash t imported))
        (push (cons note hash) recordings-to-consume)))
    (when (buffer-modified-p)
      (save-buffer))
    (dolist (recording (nreverse recordings-to-consume))
      (org-ext--consume-recording-note (car recording) (cdr recording)))
    (dolist (note (nreverse drafts-to-consume))
      (delete-file note t))))

(defadvice org-agenda (around fit-windows-for-agenda activate)
  "Fit the Org Agenda to its buffer and import any pending Drafts and Recordings."
  (let ((draft-notes
         (and (file-directory-p "~/Drafts")
              (directory-files "~/Drafts" t "[0-9].*\\.txt\\'" nil)))
        (recording-notes (org-ext-recording-note-files)))
    (when (or draft-notes recording-notes)
      (org-ext-goto-inbox
       (lambda ()
         (org-ext--import-agenda-notes draft-notes recording-notes)))))
  ad-do-it
  (org-ext-fit-agenda-window))

(defun org-ext-agenda-show (&optional _arg)
  "Display Org file containing item at point."
  (interactive "P")
  (let ((win (selected-window)))
    (unwind-protect
        (if (and (window-live-p org-agenda-show-window)
                 (eq this-command last-command))
            (progn
              (select-window org-agenda-show-window)
              (ignore-errors (scroll-up)))
          (org-agenda-goto)
          (org-with-wide-buffer
           (org-fold-show-entry 'hide-drawers))
          (setq org-agenda-show-window (selected-window)))
      (when (window-live-p win)
        (select-window win)))))

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
          (org-cycle-hide-drawers 'children)
        (org-with-wide-buffer
	   (narrow-to-region (org-entry-beginning-position)
			     (org-entry-end-position))
	   (org-fold-show-all '(drawers))))
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
`org-agenda-files' to expand list-file and directory entries."
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
      (mapc #'find-file-noselect (org-agenda-files))
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
  "Return (BEG . END) spanning the entry's :PROPERTIES:...:END: block.
Return nil unless the entry has an ordered, line-anchored property
drawer.  Property-like text inside example blocks is ignored."
  (or (when-let ((body (org-get-property-block)))
        (cons (save-excursion
                (goto-char (car body))
                (forward-line -1)
                (point))
              (save-excursion
                (goto-char (cdr body))
                (line-end-position))))
      (org-ext-with-entry-narrowed
       (goto-char (point-min))
       (catch 'drawer
         (while (re-search-forward "^:PROPERTIES:[ \t]*$" nil t)
           (let* ((beg (match-beginning 0))
                  (element (save-excursion
                             (goto-char beg)
                             (org-element-at-point))))
             (when (and (= beg (org-element-property :begin element))
                        (or (eq (org-element-type element) 'property-drawer)
                            (and (eq (org-element-type element) 'drawer)
                                 (string= (org-element-property :drawer-name element)
                                          "PROPERTIES"))))
               (goto-char beg)
               (when (re-search-forward "^:END:[ \t]*$"
                                        (org-element-property :end element) t)
                 (throw 'drawer (cons beg (match-end 0)))))))))))

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
Scans all headlines from `point-min' and fixes misplaced property
drawers."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^\\*" nil t)
      (ignore-errors
        (org-ext-move-properties-drawer))
      (forward-line 1))))

(defun org-ext-update-date-field ()
  "Set #+date field from the file's leading YYYYMMDD name timestamp.
Extract the leading eight digits from `buffer-file-name', validate
them as a calendar date, and replace the value of the first
`#+date:' line with that date as an inactive timestamp.  When the
base name has no leading YYYYMMDD, or the digits do not form a
valid date, the field is left untouched — `current-time' is never
substituted, so a mocked \"today\" cannot mismatch the filename."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^#\\+date:\\s-*\\(.+\\)" nil t)
      (let ((beg (match-beginning 1))
            (end (match-end 1))
            (name (and buffer-file-name
                   (file-name-nondirectory buffer-file-name))))
        (when (and name
                   (string-match
                    "\\`\\([0-9]\\{4\\}\\)\\([0-9]\\{2\\}\\)\\([0-9]\\{2\\}\\)"
                    name))
          (let* ((year (string-to-number (match-string 1 name)))
                 (month (string-to-number (match-string 2 name)))
                 (day (string-to-number (match-string 3 name)))
                 (date (condition-case nil
                           (encode-time
                            (list 0 0 0 day month year nil -1 nil))
                         (error nil)))
                 (decoded (and date (decode-time date))))
            (when (and decoded
                       (= day (nth 3 decoded))
                       (= month (nth 4 decoded))
                       (= year (nth 5 decoded)))
              (delete-region beg end)
              (org-insert-time-stamp date t t))))))))

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
  ;; Invoke the ID worker explicitly with the prefix argument so a
  ;; `\[universal-argument]' regenerates an existing ID.  Doing this before
  ;; the nullary capture hooks run means a hook that calls
  ;; `org-ext-set-id-and-created' with no argument becomes a no-op
  ;; rather than racing the explicit call.
  (org-ext-set-id-and-created (when (equal arg '(4)) arg))
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

(defcustom org-ext-contact-tag-regexp "\\`[A-Z][a-z]+\\'"
  "Regexp matching tags that name a person, such as \"Nikhil\".
Matching is case-sensitive.  Tags configured in
`org-tag-persistent-alist' or `org-tag-alist' are context tags
such as \"Home\", never contact tags, even when they match this
regexp; see `org-ext--contact-tag-p'."
  :group 'org-ext
  :type 'regexp)

(defun org-ext--contact-tag-p (tag)
  "Return non-nil if TAG names a person rather than a context.
TAG qualifies when it matches `org-ext-contact-tag-regexp'
case-sensitively and is not one of the tags configured in
`org-tag-persistent-alist' or `org-tag-alist'."
  (let ((case-fold-search nil))
    (and (string-match-p org-ext-contact-tag-regexp tag)
         (not (member tag
                      (delq nil
                            (mapcar (lambda (entry)
                                      (and (stringp (car-safe entry))
                                           (car-safe entry)))
                                    (append org-tag-persistent-alist
                                            org-tag-alist))))))))

(defun org-ext--contact-tag-candidates ()
  "Return a sorted list of known contact tags for completion.
Tags are gathered from `org-global-tags-completion-table' across
the agenda files and filtered with `org-ext--contact-tag-p', so
configured context tags are excluded.  Context tags declared only
in file-local \"#+TAGS\" keywords are not excluded."
  (sort (cl-remove-if-not #'org-ext--contact-tag-p
                          (mapcar #'car (org-global-tags-completion-table)))
        #'string-lessp))

(defvar org-ext-contact-tag-history nil
  "Minibuffer history for `org-ext-switch-todo-task'.")

(defun org-ext-switch-todo-task ()
  "Switch the current entry between a TODO and a delegated TASK.
On an entry that is not already a TASK, prompt for an assignee,
set the TODO keyword to TASK, and replace all local contact tags
— those satisfying `org-ext--contact-tag-p' — with the assignee's
tag.  Empty input sets the keyword to TASK without touching tags,
since the assignee may also be implied by the entry's CATEGORY.
A typed-in assignee given entirely in lower or upper case is
capitalized; anything else must already match
`org-ext-contact-tag-regexp' or an error is signaled.

On a TASK, set the keyword back to TODO and remove every local
contact tag, without prompting.

Only the entry at point is changed, even when the region is
active.  Inherited tags are never modified, and no state change
note is logged."
  (interactive)
  (save-excursion
    (org-back-to-heading t)
    (let ((org-inhibit-logging t)
          (org-loop-over-headlines-in-active-region nil))
      (if (equal (org-get-todo-state) "TASK")
          (progn
            (org-todo "TODO")
            (org-set-tags (cl-remove-if #'org-ext--contact-tag-p
                                        (org-get-tags nil t))))
        (let ((name (string-trim
                     (completing-read "Assignee: "
                                      (org-ext--contact-tag-candidates)
                                      nil nil nil
                                      'org-ext-contact-tag-history))))
          (unless (or (string-empty-p name)
                      (org-ext--contact-tag-p name))
            (when (or (string= name (downcase name))
                      (string= name (upcase name)))
              (setq name (capitalize name)))
            (unless (org-ext--contact-tag-p name)
              (user-error "Not a valid contact tag: %s" name)))
          (org-todo "TASK")
          (unless (string-empty-p name)
            (org-set-tags
             (append (cl-remove-if #'org-ext--contact-tag-p
                                   (org-get-tags nil t))
                     (list name)))))))))

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
         (let ((inherit org-use-property-inheritance))
           ;; Normalize the four legal forms of
           ;; `org-use-property-inheritance' before adding WITH, so a
           ;; nil, t, single regexp string, or list value all yield a
           ;; proper list containing "WITH" rather than corrupting the
           ;; variable (e.g. appending to t, or to a regexp string).
           (cond
            ((null inherit) '("WITH"))
            ((eq inherit t) t)
            ((stringp inherit)
             (concat "\\(?:" inherit "\\|\\`WITH\\'\\)"))
            ((consp inherit)
             (delete-dups (append inherit '("WITH"))))
            (t '("WITH"))))))
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
Returns the priority character or nil if none is present."
  (save-excursion
    (when (org-up-heading-safe)
      (save-match-data
        (beginning-of-line)
        (when (re-search-forward org-priority-regexp (line-end-position) t)
          (string-to-char (match-string 2)))))))

(defsubst org-ext-agenda-files-except (&rest args)
  "Return expanded agenda files excluding paths equal to any of ARGS."
  (cl-set-difference (org-agenda-files) args :test #'string=))

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
                             (org-ext--first-child-todo pred))
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
        ;; Ascend through non-TODO headings (e.g. categories) to the
        ;; nearest TODO ancestor before looking for a preceding sibling.
        ;; Test the immediate parent before ascending again so direct
        ;; children are ordered too.
        (while (and (not (org-ext-task-p))
                    (org-up-heading-safe)))
        (when (org-ext-task-p)
          (let ((first-child (org-ext-first-child-todo)))
            (and first-child
                 (or (/= first-child here)
                     (org-ext-has-preceding-todo-p)))))))))

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
          (count 0))
      ;; First pass: collect heading IDs
      (while (and (< (point) end-marker)
                  (re-search-forward org-heading-regexp end-marker t))
        (save-excursion
          (org-back-to-heading t)
          (push (org-id-get-create) ids)))
      (setq ids (nreverse ids))
      ;; Second pass: set BLOCKER properties.  Carry a separate
      ;; previous-ID that is applied to the current heading before it
      ;; is advanced to the current heading's own ID, so a heading can
      ;; never block itself.
      (let ((prev-id nil))
        (goto-char beg)
        (while (and (< (point) end-marker)
                    (re-search-forward org-heading-regexp end-marker t))
          (save-excursion
            (org-back-to-heading t)
            (when prev-id
              (let* ((blocker-prop "BLOCKER")
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
            (setq prev-id (car ids))
            (setq ids (cdr ids)))))
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
  ;; Snapshot the position of every link in the subtree before opening
  ;; any of them, so the side effects of `org-open-at-point' (buffer/window
  ;; switches, narrowing, or inserted content) cannot disrupt iteration or
  ;; cause a link to be opened twice.
  (let (markers)
    (save-excursion
      (save-restriction
        (org-narrow-to-subtree)
        (goto-char (point-min))
        (let ((inhibit-message t)
              (message-log-max nil))
          (setq org-link--search-failed nil)
          (while (progn (org-next-link)
                      (not org-link--search-failed))
            (push (point-marker) markers)))))
    (dolist (m (nreverse markers))
      (when (and (markerp m) (marker-buffer m))
        (with-current-buffer (marker-buffer m)
          (save-excursion
            (save-restriction
              (widen)
              (goto-char m)
              (let ((inhibit-message t)
                    (message-log-max nil))
                (org-open-at-point)))))
        (set-marker m nil)))))

;;;###autoload
(defun org-ext-copy-subtree-as-markdown ()
  "Copy and display the current Org subtree as formatted Markdown.
Retain the subtree root as an ATX level-one heading while omitting the
TOC, workflow keywords, generated anchor targets, and state transitions."
  (interactive)
  (require 'ox-md)
  (require 'mdformat)
  (let ((mark-active nil)
        (output-buffer (get-buffer-create "*Org MD Export*"))
        markdown)
    (with-current-buffer output-buffer
      (let ((inhibit-read-only t))
        (erase-buffer))
      (text-mode))
    (let ((org-export-filter-options-functions
           (append
            org-export-filter-options-functions
            (list
             (lambda (options _backend)
               (dolist (setting
                        '((:md-headline-style atx)
                          (:md-toplevel-hlevel 1)
                          (:with-tasks t)
                          (:with-todo-keywords nil)
                          (:with-toc nil)
                          (:with-drawers (not "LOGBOOK"))))
                 (setq options
                       (plist-put options (car setting) (cadr setting))))
               options)))))
      (save-restriction
        (org-narrow-to-subtree)
        (setq markdown (org-export-as 'md))))
    (setq markdown
          (replace-regexp-in-string
           "^-[ \t]+State \"[^\"]+\"[ \t]+from \"[^\"]+\"[^\n]*\n*" ""
           (replace-regexp-in-string
            "^<a id=\"[^\"]+\"></a>[ \t]*\n*" "" markdown)))
    (with-current-buffer output-buffer
      (insert markdown)
      (mdformat-buffer)
      (goto-char (point-max))
      (while (looking-at "^")
        (backward-delete-char 1))
      (kill-new (buffer-string))
      (goto-char (point-min)))
    (pop-to-buffer output-buffer)
    (message "Formatted Markdown subtree copied and displayed")))

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
    (when (re-search-forward "\\[\\[\\([^]]+?\\)\\]\\[\\([^]]+?\\)\\]\\]" (line-end-position) t)
      (replace-match name t t nil 2))))

(defun org-ext-swap-link-name ()
  (interactive)
  (save-excursion
    (goto-char (line-beginning-position))
    (when (re-search-forward
           "\\[\\[\\([^]]+?\\)\\]\\[\\([^]]+?\\)\\]\\]: \\(\\([A-Za-z -]+ *\\)[^\n]*\n+\\)" (save-excursion (forward-line 1) (line-end-position)) t)
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
                           ;; A new one-word capitalized line is ambiguous
                           ;; content.  Accept it as an author only after that
                           ;; exact name has already been established.
                           (or (string-match-p " " first-line)
                               (gethash first-line known-authors))
                           ;; Author lines are separated from nonempty content
                           ;; by at least one blank line.
                           (save-excursion
                             (forward-line 1)
                             (and (< (point) next-timestamp-pos)
                                  (looking-at "^[[:space:]]*$")
                                  (progn
                                    (while (and (< (point) next-timestamp-pos)
                                                (looking-at "^[[:space:]]*$"))
                                      (forward-line 1))
                                    (< (point) next-timestamp-pos))))))))

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
Narrows to heading with `org-id-find', copies the subtree (without
cutting it), pastes at current location, and deletes the source only
after the paste has succeeded."
  (interactive (list (vulpea-note-id (vulpea-select "Heading"))))
  (cl-destructuring-bind (file . pos)
      (org-id-find uuid)
    (let (source-marker)
      (save-excursion
        (with-current-buffer
            (find-file-noselect file 'noward)
          (save-excursion
            (save-restriction
              (widen)
              (goto-char pos)
              ;; Copy without cutting; the source is consumed below only
              ;; after `org-paste-subtree' returns normally.
              (org-copy-subtree 1 nil)
              (setq source-marker (point-marker)))))
      (prog1
          (org-paste-subtree nil nil nil t)
        (when (and source-marker (marker-buffer source-marker))
          (with-current-buffer (marker-buffer source-marker)
            (save-excursion
              (save-restriction
                (widen)
                (goto-char source-marker)
                (org-back-to-heading t)
                (org-cut-subtree))))))))))

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
        (goto-char (point-min))
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
  (interactive
   (if (use-region-p)
       (list (region-beginning) (region-end))
     (list nil nil)))
  (save-restriction
    (narrow-to-region (or beg (point-min)) (or end (point-max)))
    (goto-char (point-min))
    (while (re-search-forward org-link-bracket-re nil t)
      ;; Replace with the description when present, otherwise the link
      ;; target (bare [[URL]]); use a literal replacement so backslashes
      ;; in the text are not interpreted as \-escapes.
      (replace-match (or (match-string 2) (match-string 1)) t t))))

(defun org-ext-follow-tag-link (tag &optional arg)
  "Display a list of TODO headlines with TAG.
With a non-nil ARG (a prefix argument), also display headlines
without a TODO keyword.  ARG is accepted explicitly rather than
read from `current-prefix-arg', so the function can be called
programmatically with a prefix equivalent (e.g. `(4)`).
Uses `org-tags-view' for filtering."
  (org-tags-view (null arg) tag))

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
                      org-link-parameters))
  ;; Refresh the compiled link regexps and the element parser syntax so
  ;; neither the link matcher nor the Org parser still recognize the
  ;; removed type once it is gone from `org-link-parameters'.
  (when (fboundp 'org-link-make-regexps)
    (org-link-make-regexps))
  (when (fboundp 'org-element-update-syntax)
    (org-element-update-syntax)))

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
  "Set the URL/URL2 property from the most recently stored link.
Require `org-stored-links' to be non-empty before mutating; signal
`user-error' otherwise so the entry is never left half-todoized.  The
link is rendered with `org-link-make-string', which builds a correctly
bracketed `[[link][desc]]' form from Org's `(link desc)' entry shape.
Description is taken from `(cadr (car org-stored-links))' rather than
`cdar', which would yield a one-element list when the entry is a
two-element list (as `org-store-link' and `org-protocol-store-link'
produce)."
  (interactive)
  (let ((entry (car org-stored-links)))
    (unless (and entry
                 (stringp (car-safe entry))
                 (not (string-empty-p (car entry))))
      (user-error "No stored link available"))
    (org-ext-todoize)
    (let ((link (car entry))
          (desc (cadr entry)))
      (org-set-property (if (org-entry-get (point-marker) "URL") "URL2" "URL")
                        (if (and (stringp desc) (not (string-empty-p desc)))
                            (org-link-make-string link desc)
                          (org-link-make-string link)))
      (org-toggle-tag "LINK" 'on))))

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
  "Return the entry timestamp as a float, or the current time when absent."
  (let ((timestamp (or (org-entry-get (point) "TIMESTAMP")
                       (org-entry-get (point) "TIMESTAMP_IA")
                       (org-entry-get (point) "CREATED"))))
    (if timestamp
        (float-time (org-time-string-to-time timestamp))
      (float-time))))

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
  (goto-char (point-min))
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
          (if (looking-at "^\\*+\\s-+")
              (setq should-skip (org-get-tags))))
        should-skip))))

(defun org-ext-ancestor-keywords ()
  "Collect todo keywords from ancestor headings in hierarchy.
Returns list of todo states from parent headings above current entry.
Uses recursive ascent with `org-up-heading-safe'."
  (save-excursion
    ;; Cons the parent's state only after a successful ascent, so a
    ;; top-level TODO yields nil and a single TODO parent yields one
    ;; keyword with no duplicate of the parent.
    (when (org-up-heading-safe)
      (delete nil
              (cons (org-get-todo-state)
                    (org-ext-ancestor-keywords))))))

(defun org-ext-insert-code-block ()
  "Replace three backticks immediately before point with an Org source block."
  (when (and (>= (- (point) (point-min)) 3)
             (equal (buffer-substring-no-properties (- (point) 3) (point))
                    "```"))
    (delete-char -3)
    (let ((language
           (or (save-excursion
                 (when (re-search-backward
                        "#\\+begin_src \\([^ \t\n]+\\)" nil t)
                   (match-string-no-properties 1)))
               "sh")))
      (insert "#+begin_src " language "\n\n#+end_src")
      (forward-line -1))))

(defsubst org-ext-setup-insert-code-block ()
  "Setup hook to auto-create code blocks after triple-backtick.
Adds `org-ext-insert-code-block' to `post-self-insert-hook'."
  (add-hook 'post-self-insert-hook #'org-ext-insert-code-block nil t))

(defun org-ext--category-values (&optional files)
  "Return the category value from each heading in FILES."
  (org-ql-select (or files (org-agenda-files))
    t
    :action (lambda () (org-get-category))))

(defun org-ext-get-all-categories (&optional files)
  "Return a sorted list of all unique categories used in org FILES."
  (interactive)
  (sort (delete-dups (delq nil (org-ext--category-values files))) #'string<))

(defun org-ext-get-all-categories-detailed (&optional files include-counts)
  "Return unique categories, optionally with counts, from org FILES."
  (interactive (list nil t))
  (let ((categories (delq nil (org-ext--category-values files))))
    (if include-counts
        (let ((counts (make-hash-table :test #'equal))
              result)
          (dolist (category categories)
            (puthash category (1+ (gethash category counts 0)) counts))
          (maphash (lambda (category count)
                     (push (cons category count) result))
                   counts)
          (sort result (lambda (a b) (string< (car a) (car b)))))
      (sort (delete-dups categories) #'string<))))

(defun org-ext-get-categories-by-file (&optional files)
  "Return an alist of (file . categories) for org FILES."
  (let (result)
    (dolist (file (or files (org-agenda-files)))
      (let ((categories
             (sort (delete-dups
                    (delq nil (org-ext--category-values (list file))))
                   #'string<)))
        (when categories
          (push (cons file categories) result))))
    (nreverse result)))

(defun org-ext-show-all-categories ()
  "Display all categories used in the current Org project.
Shows categories with their usage counts in a temporary buffer."
  (interactive)
  (let* ((categories-with-counts (org-ext-get-all-categories-detailed nil t))
         (total-categories (length categories-with-counts))
         (total-entries (apply #'+ (mapcar #'cdr categories-with-counts))))
    (with-current-buffer (get-buffer-create "*Org Categories*")
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert "Org Categories Summary\n")
        (insert "======================\n")
        (insert (format "Total categories: %d\n" total-categories))
        (insert (format "Total categorized entries: %d\n\n" total-entries))
        (insert "Category                     Count\n")
        (insert "--------                     -----\n")
        (dolist (cat-count categories-with-counts)
          (insert (format "%-28s %5d\n" (car cat-count) (cdr cat-count))))
        (goto-char (point-min))
        (read-only-mode 1))
      (display-buffer (current-buffer)))))

(defvar org-ext-category-history nil)

(defun org-ext-set-category (category)
  "Set the category of the current Org-mode element to CATEGORY."
  (interactive
   (list (completing-read "Category: " (org-ext-get-all-categories)
                          nil nil nil 'org-ext-category-history)))
  (org-set-property "CATEGORY" category))

;;; Setting heading attribution (contact) and verb
;;
;; Beyond the CATEGORY property, task headings in this configuration may
;; carry a leading attribution and/or verb directly in their title:
;;
;;     TODO (Alexey) Read: Tron documentation
;;          \______/ \__/  \_______________/
;;          contact   verb        rest
;;
;; This is the grammar recognized by `org-ql-ext-verb-regexp'.  The
;; helpers below decompose a title into those parts and reassemble it, so
;; the attribution and verb can be set with completion (analogous to
;; `org-ext-set-category').

(defun org-ext--split-heading-title (title)
  "Split heading TITLE into a list (CONTACTS VERB REST).
CONTACTS is the list of attribution names taken from any leading
`(Name)' groups.  VERB is the leading verb word, without its
trailing colon, when the remaining text begins with `Word: ' (or
`Word:' at end of title); otherwise nil.  REST is whatever title
text remains.  This is the structural inverse of
`org-ql-ext-verb-regexp'."
  (let ((s (or title ""))
        (contacts '())
        (verb nil))
    (while (string-match
            "\\`[[:space:]]*(\\([^)]+\\))\\(?:[[:space:]]+\\|\\'\\)" s)
      (push (string-trim (match-string 1 s)) contacts)
      (setq s (substring s (match-end 0))))
    (when (string-match "\\`\\([[:alpha:]]+\\):\\(?:[[:space:]]+\\|\\'\\)" s)
      (setq verb (match-string 1 s))
      (setq s (substring s (match-end 0))))
    (list (nreverse contacts) verb s)))

(defun org-ext--join-heading-title (contacts verb rest)
  "Reassemble CONTACTS, VERB and REST into a heading title string.
The inverse of `org-ext--split-heading-title': CONTACTS is a list
of attribution names rendered as `(Name)' prefixes, VERB (a string
or nil) is rendered as `Verb:', and REST is the trailing text.
Blank entries are dropped and surrounding whitespace normalized."
  (let ((parts '()))
    (dolist (name contacts)
      (when (and (stringp name) (not (string-empty-p (string-trim name))))
        (push (format "(%s)" (string-trim name)) parts)))
    (when (and (stringp verb) (not (string-empty-p (string-trim verb))))
      (push (format "%s:" (string-trim verb)) parts))
    (setq parts (nreverse parts))
    (string-trim
     (concat (mapconcat #'identity parts " ")
             (and parts " ")
             (or rest "")))))

(defun org-ext--set-heading-component (component value)
  "Set COMPONENT of the current heading's title to VALUE.
COMPONENT is the symbol `contact' or `verb'.  A nil or blank VALUE
removes that component.  Setting a contact replaces any existing
attribution; setting a verb replaces any existing verb and is
capitalized for display consistency.  The headline is rewritten
with `org-edit-headline', preserving the TODO keyword, priority and
tags."
  (org-back-to-heading t)
  (let* ((parts (org-ext--split-heading-title (org-get-heading t t t t)))
         (contacts (nth 0 parts))
         (verb (nth 1 parts))
         (rest (nth 2 parts))
         (value (and (stringp value) (string-trim value)))
         (blank (or (null value) (string-empty-p value))))
    (pcase component
      ('contact (setq contacts (unless blank (list value))))
      ('verb (setq verb (unless blank (capitalize value))))
      (_ (error "Unknown heading component: %S" component)))
    (org-edit-headline (org-ext--join-heading-title contacts verb rest))))

(defun org-ext--contacts-from-headings (&optional files)
  "Return contact names used as `(Name)' attributions in agenda FILES.
FILES defaults to `org-agenda-files'.  Names are gathered by
decomposing each heading title with `org-ext--split-heading-title'."
  (let ((names '()))
    (org-ql-select (or files (org-agenda-files))
      '(heading-regexp "([^)]+)")
      :action
      (lambda ()
        (dolist (name (car (org-ext--split-heading-title
                            (org-get-heading t t t t))))
          (cl-pushnew name names :test #'string=))))
    names))

(defun org-ext-get-all-contacts (&optional files)
  "Return a sorted list of contact names for completion.
Merges the names in the `org-contacts' database with the `(Name)'
attributions already used in headings across agenda FILES; see
`org-ext--contacts-from-headings'."
  (let ((names (and (fboundp 'org-contacts-filter)
                    (ignore-errors (mapcar #'car (org-contacts-filter))))))
    (dolist (name (org-ext--contacts-from-headings files))
      (cl-pushnew name names :test #'string=))
    (sort (delete-dups names) #'string-lessp)))

(defvar org-ext-contact-history nil
  "Minibuffer history for `org-ext-set-contact'.")

(defun org-ext-set-contact (contact)
  "Set the attribution of the current heading to CONTACT.
CONTACT appears in the heading title as a leading `(CONTACT)'
prefix, replacing any existing attribution.  An empty CONTACT
removes the attribution.  Completion draws on the `org-contacts'
database merged with attributions already in use; see
`org-ext-get-all-contacts'."
  (interactive
   (list (completing-read "Contact: " (org-ext-get-all-contacts)
                          nil nil nil 'org-ext-contact-history)))
  (org-ext--set-heading-component 'contact contact))

(defvar org-ext-verb-history nil
  "Minibuffer history for `org-ext-set-verb'.")

(defun org-ext-set-verb (verb)
  "Set the leading verb of the current heading to VERB.
The heading title is rewritten to begin with `VERB: ', replacing
any existing verb.  An empty VERB removes it.  Completion draws on
the verbs already in use across the agenda files; see
`org-ql-ext-get-all-verbs'."
  (interactive
   (list (completing-read "Verb: "
                          (and (fboundp 'org-ql-ext-get-all-verbs)
                               (org-ql-ext-get-all-verbs))
                          nil nil nil 'org-ext-verb-history)))
  (org-ext--set-heading-component 'verb verb))

(defun org-ext--collect-agenda-markers ()
  "Return a snapshot list of heading markers for the current agenda selection.

Covers three Org selection mechanisms, in priority order: bulk-marked
entries (`org-agenda-bulk-marked-entries'), an active region (when
`org-agenda-loop-over-headlines-in-active-region' is set), or just the
current agenda line.  Markers are copied so that a later
`org-agenda-redo' cannot invalidate the iteration while BODY runs."
  (let (markers)
    (cond
     ((and (boundp 'org-agenda-bulk-marked-entries)
           org-agenda-bulk-marked-entries)
      (dolist (m org-agenda-bulk-marked-entries)
        (when (and (markerp m) (marker-buffer m))
          (push (copy-marker m) markers)))
      (nreverse markers))
     ((and org-agenda-loop-over-headlines-in-active-region
           (org-region-active-p))
      (save-excursion
        (goto-char (region-beginning))
        (let ((end (move-marker (make-marker) (region-end))))
          (unwind-protect
              (progn
                (while (< (point) end)
                  (let ((m (org-get-at-bol 'org-hd-marker)))
                    (when (and m (marker-buffer m))
                      (push (copy-marker m) markers)))
                  (org-agenda-next-item 1))
                (nreverse markers))
            (set-marker end nil)))))
     (t
      (let ((m (or (org-get-at-bol 'org-hd-marker)
                  (org-agenda-error))))
        (when (and m (marker-buffer m))
          (list (copy-marker m))))))))

(defmacro org-ext--with-agenda-entry (command &rest body)
  "Evaluate BODY on the Org entry(ies) behind the current agenda line.
COMMAND is the interactive agenda command symbol; it is retained so
callers remain self-describing.  Source markers are snapshotted via
`org-ext--collect-agenda-markers' before any mutation, so an agenda
rebuild cannot disrupt iteration over region-selected or bulk-marked
entries.  BODY runs in each entry's buffer, widened and made visible,
inside `org-with-remote-undo'; the agenda is rebuilt once with
`org-agenda-redo' after every selected entry has been processed."
  (declare (indent 1) (debug (form body)))
  (ignore command)
  `(progn
     (org-agenda-check-no-diary)
     (let ((--org-ext-markers (org-ext--collect-agenda-markers)))
       (dolist (hdmarker --org-ext-markers)
         (let* ((buffer (marker-buffer hdmarker))
                (pos (marker-position hdmarker))
                (inhibit-read-only t))
           (when buffer
             (org-with-remote-undo buffer
               (with-current-buffer buffer
                 (widen)
                 (goto-char pos)
                 (org-fold-show-context 'agenda)
                 ,@body)))))
       (dolist (m --org-ext-markers)
         (when (markerp m) (set-marker m nil)))
       (org-agenda-redo))))

(defun org-ext-agenda-set-category ()
  "Set the CATEGORY property for the current agenda entry.
Calls `org-ext-set-category' on the underlying Org entry, then
refreshes the agenda since CATEGORY appears in the displayed line."
  (interactive)
  (org-ext--with-agenda-entry #'org-ext-agenda-set-category
    (call-interactively #'org-ext-set-category)))

(defun org-ext-agenda-set-contact ()
  "Set the contact attribution for the current agenda entry.
Calls `org-ext-set-contact' on the underlying Org entry, then
refreshes the agenda since the attribution appears in the heading."
  (interactive)
  (org-ext--with-agenda-entry #'org-ext-agenda-set-contact
    (call-interactively #'org-ext-set-contact)))

(defun org-ext-agenda-set-verb ()
  "Set the leading verb for the current agenda entry.
Calls `org-ext-set-verb' on the underlying Org entry, then
refreshes the agenda since the verb appears in the heading."
  (interactive)
  (org-ext--with-agenda-entry #'org-ext-agenda-set-verb
    (call-interactively #'org-ext-set-verb)))

(defun org-ext-agenda-switch-todo-task ()
  "Switch the current agenda entry between a TODO and a TASK.
Calls `org-ext-switch-todo-task' on the underlying Org entry, then
refreshes the agenda since both the keyword and the tags appear in
the displayed line."
  (interactive)
  (org-ext--with-agenda-entry #'org-ext-agenda-switch-todo-task
    (call-interactively #'org-ext-switch-todo-task)))

(defun org-ext-set-id-and-created (&optional arg)
  "Ensure the current heading has an ID and a CREATED timestamp.
Call `org-id-get-create' with ARG, which forces regeneration of an
existing ID only when ARG is non-nil (e.g. a raw `\[universal-argument]').
Then set the CREATED inactive timestamp property unless one already
exists.  `arg' defaults to nil so a nullary call from a finalize
hook never overwrites an existing ID."
  (org-id-get-create arg)
  (unless (org-entry-get (point) "CREATED")
    (org-entry-put (point) "CREATED"
                   (format-time-string (org-time-stamp-format t t)))))

(defun org-ext-quickping (host)
  (= 0 (call-process "ping" nil nil nil "-c1" "-W5" "-q" host)))

(defun org-ext-at-home-p ()
  "Return non-nil if currently attached to the home LAN.
Detection looks for a 192.168.1.* address on the bridge0 interface."
  (with-temp-buffer
    (call-process "ifconfig" nil t nil "bridge0" "inet")
    (goto-char (point-min))
    (search-forward "inet 192.168.1." nil t)))

(defcustom org-ext-location-command-timeout 2
  "Seconds to wait for CoreLocationCLI during capture finalization."
  :type 'number
  :group 'org-ext)

(defun org-ext--command-output-with-timeout (program timeout &rest args)
  "Run PROGRAM with ARGS, returning stdout or an empty string after TIMEOUT."
  (with-temp-buffer
    (let ((deadline (+ (float-time) timeout))
          process
          timed-out)
      (condition-case nil
          (progn
            (setq process
                  (make-process
                   :name "org-ext-command"
                   :buffer (current-buffer)
                   :command (cons program args)
                   :connection-type 'pipe
                   :sentinel #'ignore
                   :noquery t))
            (while (and (process-live-p process) (not timed-out))
              (let ((remaining (- deadline (float-time))))
                (if (<= remaining 0)
                    (setq timed-out t)
                  (accept-process-output process remaining))))
            (when (process-live-p process)
              (setq timed-out t)
              (delete-process process))
            (if (and (not timed-out)
                     (eq (process-status process) 'exit)
                     (= (process-exit-status process) 0))
                (buffer-string)
              ""))
        (error
         (when (and process (process-live-p process))
           (delete-process process))
         "")))))

(defun org-ext-get-location ()
  "Return current latitude and longitude, or empty strings on failure."
  (if (and nil (org-ext-at-home-p))
      '("38.569498" "-121.388618")
    (let ((strs
           (split-string
            (string-trim
             (org-ext--command-output-with-timeout
              "CoreLocationCLI" org-ext-location-command-timeout)))))
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
  "Clean NBSPs, trailing whitespace, and blank lines.
When invoked from a capture finalize hook, restrict every
operation to the capture region delimited by the buffer-local
`:begin-marker' and `:end-marker' stored by `org-capture', so an
`:unnarrowed' capture cannot mutate bytes outside the inserted
entry.  Outside capture context, the whole accessible buffer is
cleaned."
  (interactive)
  (let ((beg (when (boundp 'org-capture-plist)
               (org-capture-get :begin-marker 'local)))
        (end (when (boundp 'org-capture-plist)
               (org-capture-get :end-marker 'local))))
    (if (and (markerp beg) (markerp end)
             (marker-buffer beg) (marker-buffer end)
             (eq (marker-buffer beg) (current-buffer))
             (eq (marker-buffer end) (current-buffer))
             (< (marker-position beg) (marker-position end)))
        (save-restriction
          (narrow-to-region beg end)
          (org-ext--cleanup-whitespace-region))
      (org-ext--cleanup-whitespace-region))))

(defun org-ext--cleanup-whitespace-region ()
  "Perform the NBSP/whitespace cleanup within the current narrowing."
  (save-excursion
    (goto-char (point-min))
    (while (search-forward "\u00a0" nil t)
      (replace-match " "))
    (whitespace-cleanup)
    (goto-char (point-max))
    (skip-chars-backward " \t\n\r")
    (delete-region (point) (point-max))
    (when (looking-back (regexp-opt org-todo-keywords-1)
                        (line-beginning-position))
      (insert-before-markers " "))
    (insert-before-markers "\n"))
  (when (eobp)
    (backward-char)))

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

(declare-function org-review-ext-reviewed-today "org-review-ext")

(defun org-ext--fast-selection-keywords ()
  "Return normalized fast-selection (CHAR . KEYWORD) pairs for this buffer."
  (cl-loop for entry in org-todo-key-alist
           when (and (stringp (car-safe entry))
                     (characterp (cdr entry)))
           collect (cons (cdr entry) (car entry))))

;;;###autoload
(defun org-ext-insert-keyword-heading (char)
  "Insert a new sibling heading prefixed by an Org TODO keyword.
Prompt for CHAR using the fast-selection characters declared in
`org-todo-keywords' (e.g. ?n for NOTE, ?q for QUOTE, ?t for TODO).
The new heading is placed after the entire current subtree (matching
`org-insert-heading-respect-content' semantics, which is what M-RET does
in this configuration).  Default properties are added via
`org-ext-set-basic-properties'; for TODO-like keywords (those still
having a review state via `org-review-ext-reviewed-today'), a review
date is also recorded.  Point is left after the keyword so the title
can be typed immediately."
  (interactive
   (list (let ((alist (org-ext--fast-selection-keywords)))
           (read-char-choice
            (format "Insert heading [%s]: "
                    (mapconcat (lambda (e) (format "%c=%s" (car e) (cdr e)))
                               alist " "))
            (mapcar #'car alist)))))
  (let ((keyword (cdr (assq char (org-ext--fast-selection-keywords)))))
    (unless keyword
      (user-error "No TODO keyword has fast-selection character %c" char))
    (org-back-to-heading t)
    (org-insert-heading-respect-content)
    (insert keyword " ")
    (save-excursion
      (org-back-to-heading t)
      (org-ext-set-basic-properties)
      (when (fboundp 'org-review-ext-reviewed-today)
        (org-review-ext-reviewed-today)))))

(provide 'org-ext)

;;; org-ext.el ends here
