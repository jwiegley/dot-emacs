;;; org-roam-extra --- Extra functions for use with Org-roam

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 29 June 2024
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

(require 'org)
(require 'org-roam)
(require 'org-extra)

(defgroup org-roam-extra nil
  "Extra functions for use with Org-roam"
  :group 'org-roam)

(defvar my/org-start-date)
(defvar my/org-end-date)

(defun my/org-read-date (&optional inactive)
  (with-temp-buffer
    (org-time-stamp nil inactive)
    (buffer-string)))

(defun my/org-date (timestamp &optional offset time inactive no-brackets)
  (with-temp-buffer
    (let ((tm (org-encode-time (org-parse-time-string timestamp))))
      (if no-brackets
          (insert (format-time-string "%Y-%m-%d %a" tm))
        (org-insert-time-stamp tm nil inactive)
        (when offset
          (org-timestamp-change offset 'day))
        (when time
          (goto-char (point-max))
          (forward-char -1)
          (insert " " time))))
    (buffer-string)))

(defun my/format-date (timestring)
  (format-time-string "%Y-%m-%d %a"
                      (org-encode-time
                       (org-parse-time-string timestring))))

(defun my/format-short-date (timestring)
  (format-time-string "%Y-%m-%d"
                      (org-encode-time
                       (org-parse-time-string timestring))))

(defun my/format-within-year (timestring)
  (format-time-string "%Y-%m-%d %a"
                      (org-encode-time
                       (org-parse-time-string
                        (format "%s-%s"
                                (nth 5 (decode-time (current-time)))
                                timestring)))))

(defun my/format-in-next-year (timestring)
  (format-time-string "%Y-%m-%d %a"
                      (org-encode-time
                       (org-parse-time-string
                        (format "%s-%s"
                                (1+ (nth 5 (decode-time (current-time))))
                                timestring)))))

(defun my/org-covid-days-to-repeat ()
  (let ((start
         (time-to-days
          (org-encode-time
           (org-parse-time-string my/org-start-date))))
        (end
         (time-to-days
          (org-encode-time
           (org-parse-time-string my/org-end-date)))))
    (format "%s" (+ (- end start) 3 3))))

(defun org-roam-extra-current-entry-and-skip ()
  (let* ((title (subst-char-in-string
                 ?/ ?: (car (last (org-get-outline-path t))) t))
         (beg (point)))
    (org-next-visible-heading 1)
    (list beg (if (= beg (point))
                  (point-max)
                (point))
          title)))

(defun org-roam-extra-created-time (end)
  (save-excursion
    (re-search-forward
     (concat ":CREATED: +\\[\\([0-9]\\{4\\}\\)-\\([0-9]\\{2\\}\\)"
             "-\\([0-9]\\{2\\}\\)"
             " ... \\([0-9]\\{2\\}\\):\\([0-9]\\{2\\}\\)\\]") end)
    (list (string-to-number (match-string 1))
          (string-to-number (match-string 2))
          (string-to-number (match-string 3))
          (string-to-number (match-string 4))
          (string-to-number (match-string 5)))))

(defun org-roam-extra-headline ()
  (looking-at "\\(\\*+\\(:? NOTE\\)? +\\)\\(.+\\)\n")
  (list (match-beginning 1) (match-end 1)
        (match-string 2)))

(defun org-roam-extra-property-drawer (end)
  (save-excursion
    (re-search-forward org-property-drawer-re end)
    (list (match-beginning 0) (1+ (match-end 0)))))

(cl-defun org-roam-extra-create-new
    (&optional goto keys &key filter-fn templates info)
  (interactive "P")
  (org-roam-capture-
   :goto goto
   :info info
   :keys keys
   :templates templates
   :node (org-roam-node-create :title "Unknown")
   ;; :props '(:immediate-finish nil)
   ))

(defun org-roam-extra-title-slug (title)
  (let ((slug-trim-chars
         '(;; Combining Diacritical Marks
           ;; https://www.unicode.org/charts/PDF/U0300.pdf
           768                    ; U+0300 COMBINING GRAVE ACCENT
           769                    ; U+0301 COMBINING ACUTE ACCENT
           770                    ; U+0302 COMBINING CIRCUMFLEX ACCENT
           771                    ; U+0303 COMBINING TILDE
           772                    ; U+0304 COMBINING MACRON
           774                    ; U+0306 COMBINING BREVE
           775                    ; U+0307 COMBINING DOT ABOVE
           776                    ; U+0308 COMBINING DIAERESIS
           777                    ; U+0309 COMBINING HOOK ABOVE
           778                    ; U+030A COMBINING RING ABOVE
           779                    ; U+030B COMBINING DOUBLE ACUTE ACCENT
           780                    ; U+030C COMBINING CARON
           795                    ; U+031B COMBINING HORN
           803                    ; U+0323 COMBINING DOT BELOW
           804                    ; U+0324 COMBINING DIAERESIS BELOW
           805                    ; U+0325 COMBINING RING BELOW
           807                    ; U+0327 COMBINING CEDILLA
           813                    ; U+032D COMBINING CIRCUMFLEX ACCENT BELOW
           814                    ; U+032E COMBINING BREVE BELOW
           816                    ; U+0330 COMBINING TILDE BELOW
           817                    ; U+0331 COMBINING MACRON BELOW
           )))
    (cl-flet* ((nonspacing-mark-p (char)
                 (memq char slug-trim-chars))
               (strip-nonspacing-marks (s)
                 (string-glyph-compose
                  (apply #'string
                         (seq-remove #'nonspacing-mark-p
                                     (string-glyph-decompose s)))))
               (cl-replace (title pair)
                 (replace-regexp-in-string (car pair) (cdr pair) title)))
      (let* ((pairs `(("[^[:alnum:][:digit:]]" . "-")
                      ("--*" . "-")
                      ("^-" . "")
                      ("-$" . "")))
             (slug (-reduce-from #'cl-replace
                                 (strip-nonspacing-marks title) pairs)))
        (downcase slug)))))

(defun org-roam-extra-prepare-note ()
  (interactive)
  (save-excursion
    (cl-destructuring-bind (beg end title)
        (org-roam-extra-current-entry-and-skip)
      (let ((text (buffer-substring beg end)))
        (with-temp-buffer
          (insert text)
          (goto-char (point-min))
          (cl-destructuring-bind (beg end _title2)
              (org-roam-extra-headline)
            (goto-char beg)
            (delete-region beg end)
            (insert "#+category: Note\n#+title: ")
            (goto-char (line-end-position))
            (insert ?\n)
            (cl-destructuring-bind (beg end)
                (org-roam-extra-property-drawer (point-max))
              (let ((properties (buffer-substring beg end)))
                (delete-region beg end)
                (goto-char (point-min))
                (insert properties)))
            (goto-char (point-max))
            (delete-blank-lines)
            (whitespace-cleanup)
            (goto-char (point-min))
            (cl-destructuring-bind (year mon day hour min)
                (org-roam-extra-created-time (point-max))
              (write-region
               nil nil
               (expand-file-name
                (format "%04d%02d%02d%02d%02d-%s.org"
                        year mon day hour min
                        (org-roam-extra-title-slug title))
                org-roam-directory)
               nil nil nil t))))
        (delete-region beg end)))))

(defun org-roam-extra-node-insert-immediate (arg &rest args)
  (interactive "P")
  (let ((args (push arg args))
        (org-roam-capture-templates
         (list (append (car org-roam-capture-templates)
                       '(:immediate-finish t)))))
    (apply #'org-roam-node-insert args)))

(defun org-roam-extra-revise-title ()
  (interactive)
  (save-buffer)
  (org-roam-db-sync)
  (let* ((title (org-roam-db--file-title))
         ;; (tags (org-extra-filetags))
         (org-roam-capture--node (org-roam-node-at-point))
         (properties (org-roam-node-properties org-roam-capture--node))
         (old-name buffer-file-name)
         (old-name-nondirectory
          (and old-name (file-name-nondirectory old-name)))
         (new-name-nondirectory
          (thread-first
            org-roam-extract-new-file-path
            (org-roam-capture--fill-template)
            (string-trim))))
    (when (and old-name-nondirectory new-name-nondirectory)
      (let* (
             ;; (old-stamp (and (string-match "^\\([0-9]\\{12\\}\\)"
             ;;                               old-name-nondirectory)
             ;;                 (match-string 1 old-name-nondirectory)))
             (created (cdr (assoc "CREATED" properties)))
             (created-tm (org-encode-time (parse-time-string created)))
             (new-stamp (format-time-string "%Y%m%d%H%M" created-tm))
             (new-slug (and (string-match "^[0-9]\\{12\\}-\\(.+\\)"
                                          new-name-nondirectory)
                            (match-string 1 new-name-nondirectory)))
             (new-name
              (expand-file-name (if (and new-stamp new-slug)
                                    (concat new-stamp "-" new-slug)
                                  new-name-nondirectory)
                                (file-name-directory old-name))))
        (unless (string= new-name old-name)
          (rename-file old-name new-name 1)
          (rename-buffer new-name)
          (set-visited-file-name new-name)
          (set-buffer-modified-p nil)
          (org-roam-db-sync))))))

(defun org-roam-extra-filter-by-tag (tag-name)
  (lambda (node)
    (member tag-name (org-roam-node-tags node))))

(defun org-roam-extra-list-notes-by-tag (tag-name)
  (mapcar #'org-roam-node-file
          (seq-filter
           (org-roam-extra-filter-by-tag tag-name)
           (org-roam-node-list))))

(defun org-roam-extra-get-all-tags ()
  "Save all roam tags to a buffer visting the file ~/Test."
  (interactive)
  (with-current-buffer (get-buffer-create "*Tags*")
    (erase-buffer)
    (mapc #'(lambda (n) (insert (car n) "\n"))
          (org-roam-db-query [:select :distinct [tag] :from tags]))
    (pop-to-buffer (current-buffer))))

;; https://d12frosted.io/posts/2021-01-16-task-management-with-roam-vol5.html
(defun org-roam-extra-project-p ()
  "Return non-nil if current buffer has any todo entry.

TODO entries marked as done are ignored, meaning the this
function returns nil if current buffer contains only completed
tasks."
  (seq-find                           ; (3)
   (lambda (type)
     (eq type 'todo))
   (org-element-map                         ; (2)
       (org-element-parse-buffer 'headline) ; (1)
       'headline
     (lambda (h)
       (message "%s" (org-element-property :todo-type h))
       (message "%s" (org-element-property :todo-keyword h))
       (and (member (org-element-property :todo-keyword h)
                    org-not-done-keywords)
            (org-element-property :todo-type h))))))

;; https://magnus.therning.org/2021-03-14-keeping-todo-items-in-org-roam.html
(defun org-roam-extra-update-todo-tag ()
  "Update TODO tag in the current buffer."
  (when (and (not (active-minibuffer-window))
             (org-roam-file-p buffer-file-name))
    (save-excursion
      (goto-char (point-min))
      (if (org-roam-extra-project-p)
          (org-roam-tag-add '("todo"))
        (org-roam-tag-remove '("todo"))))))

(defun org-roam-extra-todo-files ()
  "Return a list of note files containing todo tag."
  (seq-map
   #'car
   (org-roam-db-query
    [:select [nodes:file]
             :from tags
             :left-join nodes
             :on (= tags:node-id nodes:id)
             :where (like tag (quote "%\"todo\"%"))])))

(defun org-roam-extra-sort-file-properties ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^#\\+" nil t)
      (goto-char (match-beginning 0))
      (let ((beg (point)))
        (while (looking-at "^#\\+")
          (forward-line 1))
        (save-restriction
          (narrow-to-region beg (point))
          (goto-char (point-min))
          (sort-subr nil
                     #'(lambda ()
                         (or (and (re-search-forward "^#\\+" nil t)
                                  (goto-char (match-beginning 0)))
                             (goto-char (point-max))))
                     #'(lambda ()
                         (goto-char (line-end-position)))
                     #'(lambda ()
                         (and (re-search-forward "^#\\+\\([^:]+\\):" nil t)
                              (match-string 1)))
                     nil
                     #'(lambda (x y)
                         (if (string= (downcase y) "title")
                             t
                           (string< x y)))))))))

(defun org-roam-extra-excluded-file (relative-path)
  "Return non-nil if RELATIVE-PATH should be excluded from Org-roam."
  (let (is-match)
    (dolist (exclude-re org-roam-file-exclude-regexp)
      (setq is-match
            (or is-match
                (string-match-p exclude-re relative-path))))
    is-match))

(defun org-roam-extra-update-todo-files (&rest _)
  "Update the value of `org-agenda-files'."
  (interactive)
  (setq org-agenda-files
        (append (cl-delete-duplicates
                 (cl-delete-if
                  #'(lambda (file)
                      (org-roam-extra-excluded-file
                       (file-relative-name file org-roam-directory)))
                  (org-roam-extra-todo-files))
                 :test #'string=)
                (list "~/Mobile/inbox.org")))
  (message "org-agenda-files has been updated"))

(defun org-roam-extra-sync ()
  (interactive)
  (let ((agenda-buf (get-buffer "*Org Agenda*")))
    (when agenda-buf
      (kill-buffer agenda-buf)))
  ;; (message "Synchronizing CalDAV...")
  ;; (org-caldav-sync)
  (message "Sorting Org-mode files...")
  (redisplay t)
  (dolist (file org-agenda-files)
    (message "Sorting: %s" file)
    (redisplay t)
    (with-current-buffer (find-file-noselect file)
      (goto-char (point-min))
      (org-extra-sort-all)
      (org-cycle-content 5)
      (org-align-tags t))
    (message "Sorting: %s...done" file)
    (redisplay t))
  (save-org-mode-files)
  (message "Updating Org-roam todo cookies...")
  (redisplay t)
  (org-roam-extra-update-todo-files)
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

(defun org-roam-extra-clean-transcript ()
  (interactive)
  (save-excursion
    (replace-regexp "^\\(\\(?:[0-9]+:\\)?[0-9]+:[0-9]+\\)
\\(.+\\)
\\(.+\\)" "- \\1 *\\2* \\3"))
  (let ((fill-column 78))
    (fill-region (point) (point-max))))

(defun org-roam-extra-clean-fireflies ()
  (interactive)
  (whitespace-cleanup)
  (goto-char (point-min))
  (while (re-search-forward "^#\\+.+\n" nil t)
    (delete-region (match-beginning 0) (match-end 0)))
  (goto-char (point-min))
  (while (re-search-forward "\n\n\n" nil t)
    (replace-match "\n\n"))
  (goto-char (point-min))
  (while (re-search-forward "^AI meeting summary:" nil t)
    (replace-match "** AI meeting summary")
    (forward-line 2)
    (while (looking-at "^[- ] ")
      (delete-char 2)
      (forward-line 1)))
  (goto-char (point-min))
  (while (re-search-forward "^Notes:\n\n" nil t)
    (delete-region (match-beginning 0) (match-end 0)))
  (goto-char (point-min))
  (when (re-search-forward "^Action items:\n\n" nil t)
    (replace-match "** Action items\n")
    (let ((beg (point)))
      (while (re-search-forward "^\n" nil t)
        (delete-region (match-beginning 0) (match-end 0)))
      (goto-char beg)
      (while (re-search-forward "\n  " nil t)
        (replace-match " "))
      (goto-char beg)
      (while (re-search-forward "^\\*\\(.+?\\)\\*\n" nil t)
        (let ((name (match-string 1)))
          (delete-region (match-beginning 0) (match-end 0))
          (while (looking-at "^- ")
            (replace-match "*** TASK ")
            (goto-char (line-end-position))
            (insert "  :" name ":")
            (forward-line 1))))
      (org-extra-todoize-region beg (point) t)
      (org-set-tags-command '(4))
      (save-restriction
        (narrow-to-region (point-min) beg)
        (goto-char (point-min))
        (while (re-search-forward "^\\(\n- \\)[A-Z]" nil t)
          (replace-match "  - " nil t nil 1))
        (goto-char (point-min))
        (while (re-search-forward "^\\(  \\)[^-]" nil t)
          (replace-match "    " nil t nil 1))
        (let ((fill-column 78))
          (fill-region (point-min) (point-max)))))))

(defun org-roam-extra-insert-minutes (summary)
  (interactive
   (list
    (let* ((regexp "\\.summary\\.docx\\.org\\'")
           (candidates (directory-files "~/dl/" t regexp t)))
      (if (= (length candidates) 1)
          (car candidates)
        (read-file-name "Summary file: " "~/dl/" nil t nil
                        #'(lambda (name) (string-match regexp name)))))))
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^\\* Minutes\n\n")
      (insert
       (with-current-buffer (find-file summary)
         (org-roam-extra-clean-fireflies)
         (prog1
             (buffer-string)
           (set-buffer-modified-p nil)
           (kill-buffer (current-buffer)))))))
  ;; (save-excursion
  ;;   (goto-char (point-min))
  ;;   (when (re-search-forward "\\* \\(TASK\\|TODO\\) " nil t)
  ;;     (org-roam-tag-add "todo")))
  (delete-file summary t))

(require 'parse-csv)

(defun org-roam-extra-insert-transcript (transcript)
  (interactive
   (list
    (let* ((regexp "-st\\.csv\\'")
           (candidates (directory-files "~/dl/" t regexp t)))
      (if (= (length candidates) 1)
          (car candidates)
        (read-file-name "Transcript file: " "~/dl/" nil t nil
                        #'(lambda (name) (string-match regexp name)))))))
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^\\* Transcript\n")
      (insert ?\n)
      (let ((beg (point))
            (buf (current-buffer)))
        (with-temp-buffer
          (insert-file-contents-literally transcript)
          (goto-char (point-min))
          (forward-line 1)
          (while (not (eobp))
            (let ((fields
                   (parse-csv->list
                    (buffer-substring (line-beginning-position)
                                      (line-end-position)))))
              (with-current-buffer buf
                (insert "- " (nth 1 fields)
                        " *" (nth 4 fields) "* "
                        (nth 0 fields) "\n\n")))
            (forward-line 1)))
        (whitespace-cleanup)
        (let ((fill-column 78))
          (fill-region beg (point-max)))
        (goto-char (point-max))
        (delete-blank-lines))))
  (delete-file transcript t)
  (unless (file-readable-p (org-roam-extra-current-audio-file))
    (error "Transcript audio file missing: %s"
           (org-roam-extra-current-audio-file))))

(defun org-roam-extra--replace-if-found (name)
  (let ((found (assoc name org-extra-link-names)))
    (when found
      (delete-region (match-beginning 0) (match-end 0))
      (insert (format "- [[%s][%s]]\n"
                      (nth 0 (cdr found)) (car found))))))

(defun org-roam-extra-linkify-attending ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (if (re-search-forward "^\\* Attending\n\n" nil t)
        (let ((begin (point)))
          (when (re-search-forward "^\\* " nil t)
            (save-restriction
              (narrow-to-region begin (match-beginning 0))
              (goto-char begin)
              (while (re-search-forward "^- \\([A-Za-z].+?\\)\n" nil t)
                (org-roam-extra--replace-if-found (match-string 1))))))
      (goto-char (point-min))
      (when (re-search-forward "^#\\+title: 1-on-1: \\(.+?\\)\n" nil t)
        (let ((who (match-string 1)))
          (when (re-search-forward "- \\(TeamPage\n\\)" nil t)
            (org-roam-extra--replace-if-found who))
          (when (re-search-forward "- \\(Lattice 1-on-1 page\n\\)" nil t)
            (let ((found (assoc who org-extra-link-names)))
              (when found
                (delete-region (match-beginning 0) (match-end 0))
                (insert (format "- %s\n" (nth 1 (cdr found)))))))
          (when (re-search-forward ":match \"\\(Core\\)/" nil t)
            (replace-match (save-match-data
                             (nth 0 (split-string who " ")))
                           t t nil 1)))))))

(defun org-roam-extra-import-fireflies ()
  (interactive)
  (org-roam-extra-linkify-attending)
  (call-interactively #'org-roam-extra-insert-minutes)
  (call-interactively #'org-roam-extra-insert-transcript))

(require 'listen)

(defvar org-roam-extra-listen-player nil)

(defun hms-to-seconds (hms)
  (let* ((parts (mapcar #'string-to-number (split-string hms ":")))
         (hours (if (= (length parts) 3) (nth 0 parts) 0))
         (minutes (if (= (length parts) 3) (nth 1 parts) (nth 0 parts)))
         (seconds (if (= (length parts) 3) (nth 2 parts) (nth 1 parts))))
    (+ (* hours 3600) (* minutes 60) seconds)))

(defsubst org-roam-extra-current-audio-file ()
  (expand-file-name
   (concat (file-name-base (buffer-file-name)) ".mp3")
   "~/Audio/Kadena/Meetings"))

(defun org-roam-extra-meeting-audio (&optional arg)
  (interactive "P")
  (when org-roam-extra-listen-player
    (delete-process (listen-player-process org-roam-extra-listen-player)))
  (setf org-roam-extra-listen-player (make-listen-player-vlc))
  (setq listen-player org-roam-extra-listen-player)
  (save-excursion
    (when (re-search-backward "^- \\([0-9:]+\\) \\*" nil t)
      (let* ((tm (match-string 1))
             (secs (number-to-string (* 2 (hms-to-seconds tm)))))
        (cl-callf append
            (listen-player-args org-roam-extra-listen-player)
          (list "--start-time" secs)))))
  (listen-play org-roam-extra-listen-player
               (org-roam-extra-current-audio-file)))

(provide 'org-roam-extra)

;;; org-roam-extra.el ends here
