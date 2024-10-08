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

(defun my/org-roam-current-entry-and-skip ()
  (let* ((title (subst-char-in-string
                 ?/ ?: (car (last (org-get-outline-path t))) t))
         (beg (point)))
    (org-next-visible-heading 1)
    (list beg (if (= beg (point))
                  (point-max)
                (point))
          title)))

(defun my/org-roam-created-time (end)
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

(defun my/org-roam-headline ()
  (looking-at "\\(\\*+\\(:? NOTE\\)? +\\)\\(.+\\)\n")
  (list (match-beginning 1) (match-end 1)
        (match-string 2)))

(defun my/org-roam-property-drawer (end)
  (save-excursion
    (re-search-forward org-property-drawer-re end)
    (list (match-beginning 0) (1+ (match-end 0)))))

(cl-defun my/org-roam-create-new
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

(defun my/org-roam-title-slug (title)
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

(defun my/org-roam-prepare-note ()
  (interactive)
  (save-excursion
    (cl-destructuring-bind (beg end title)
        (my/org-roam-current-entry-and-skip)
      (let ((text (buffer-substring beg end)))
        (with-temp-buffer
          (insert text)
          (goto-char (point-min))
          (cl-destructuring-bind (beg end _title2)
              (my/org-roam-headline)
            (goto-char beg)
            (delete-region beg end)
            (insert "#+category: Note\n#+title: ")
            (goto-char (line-end-position))
            (insert ?\n)
            (cl-destructuring-bind (beg end)
                (my/org-roam-property-drawer (point-max))
              (let ((properties (buffer-substring beg end)))
                (delete-region beg end)
                (goto-char (point-min))
                (insert properties)))
            (goto-char (point-max))
            (delete-blank-lines)
            (whitespace-cleanup)
            (goto-char (point-min))
            (cl-destructuring-bind (year mon day hour min)
                (my/org-roam-created-time (point-max))
              (write-region
               nil nil
               (expand-file-name
                (format "%04d%02d%02d%02d%02d-%s.org"
                        year mon day hour min
                        (my/org-roam-title-slug title))
                org-roam-directory)
               nil nil nil t))))
        (delete-region beg end)))))

(defun my/org-roam-node-insert-immediate (arg &rest args)
  (interactive "P")
  (let ((args (push arg args))
        (org-roam-capture-templates
         (list (append (car org-roam-capture-templates)
                       '(:immediate-finish t)))))
    (apply #'org-roam-node-insert args)))

(defun my/org-roam-revise-title ()
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

(defun my/org-roam-filter-by-tag (tag-name)
  (lambda (node)
    (member tag-name (org-roam-node-tags node))))

(defun my/org-roam-list-notes-by-tag (tag-name)
  (mapcar #'org-roam-node-file
          (seq-filter
           (my/org-roam-filter-by-tag tag-name)
           (org-roam-node-list))))

(defun my/org-roam-get-all-tags ()
  "Save all roam tags to a buffer visting the file ~/Test."
  (interactive)
  (with-current-buffer (get-buffer-create "*Tags*")
    (erase-buffer)
    (mapc #'(lambda (n) (insert (car n) "\n"))
          (org-roam-db-query [:select :distinct [tag] :from tags]))
    (pop-to-buffer (current-buffer))))

(defun my/org-roam-excluded-file (relative-path)
  "Return non-nil if RELATIVE-PATH should be excluded from Org-roam."
  (let (is-match)
    (dolist (exclude-re org-roam-file-exclude-regexp)
      (setq is-match
            (or is-match
                (string-match-p exclude-re relative-path))))
    is-match))

;; https://d12frosted.io/posts/2021-01-16-task-management-with-roam-vol5.html
(defun my/org-roam-project-p ()
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
(defun my/org-roam-update-todo-tag ()
  "Update TODO tag in the current buffer."
  (when (and (not (active-minibuffer-window))
             (org-roam-file-p buffer-file-name))
    (save-excursion
      (goto-char (point-min))
      (if (my/org-roam-project-p)
          (org-roam-tag-add '("todo"))
        (org-roam-tag-remove '("todo"))))))

(defun my/org-roam-todo-files ()
  "Return a list of note files containing todo tag."
  (seq-map
   #'car
   (org-roam-db-query
    [:select [nodes:file]
             :from tags
             :left-join nodes
             :on (= tags:node-id nodes:id)
             :where (like tag (quote "%\"todo\"%"))])))

(defun my/org-roam-sort-file-properties ()
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

(defun my/org-roam-update-todo-files (&rest _)
  "Update the value of `org-agenda-files'."
  (interactive)
  (setq org-agenda-files
        (append (cl-delete-duplicates
                 (cl-delete-if
                  #'(lambda (file)
                      (my/org-roam-excluded-file
                       (file-relative-name file org-roam-directory)))
                  (my/org-roam-todo-files))
                 :test #'string=)
                (list "~/Mobile/inbox.org")))
  (message "org-agenda-files has been updated"))

(defun org-roam-extra-clean-transcript ()
  (interactive)
  (replace-regexp "^\\(\\([0-9]+:\\)?[0-9]+:[0-9]+\\)
\\(.+\\)
\\(.+\\)" "- \\1 *\\2* \\3"))

(provide 'org-roam-extra)

;;; org-roam-extra.el ends here
