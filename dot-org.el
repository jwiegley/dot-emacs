;;;_ , Org-mode

(eval-and-compile
  (require 'cl-lib)
  (require 'use-package)
  (setq use-package-verbose nil)
  (setq use-package-expand-minimally t)
  (load "org-settings"))

(eval-when-compile
  (require 'cl)
  (setplist 'string-to-multibyte
            (use-package-plist-delete
             (symbol-plist 'string-to-multibyte) 'byte-obsolete-info)))

(require 'org)
(require 'org-agenda)

(unless window-system
  (setq org-agenda-files
        '("~/Documents/tasks/todo.txt"
          "~/Documents/tasks/Bahai.txt"
          "~/Documents/tasks/BAE.txt")))

(defun org-release () "8.2.11")
(defun org-git-version () "8.2.11")

(unbind-key "C-," org-mode-map)
(unbind-key "C-'" org-mode-map)

(defconst my-org-soft-red    "#fcebeb")
(defconst my-org-soft-orange "#fcf5eb")
(defconst my-org-soft-yellow "#fcfceb")
(defconst my-org-soft-green  "#e9f9e8")
(defconst my-org-soft-blue   "#e8eff9")
(defconst my-org-soft-purple "#f3e8f9")

(when nil
  (custom-set-faces
   '(variable-pitch ((t (:family "ETBembo")))))
  ;; (custom-set-faces
  ;;  '(org-document-title ((t (:foreground "#171717" :weight bold :height 1.5)))))
  (custom-set-faces
   '(org-document-title ((t (:foreground "#f7f7f7" :weight bold :height 1.5)))))
  ;; (custom-set-faces
  ;;  '(org-done ((t (:background "#E8E8E8" :foreground "#0E0E0E" :strike-through t :weight bold)))))
  ;; (custom-set-faces
  ;;  '(org-headline-done ((t (:foreground "#171717" :strike-through t)))))
  ;; (custom-set-faces
  ;;  '(org-level-1 ((t (:foreground "#090909" :weight bold :height 1.3)))))
  ;; (custom-set-faces
  ;;  '(org-level-2 ((t (:foreground "#090909" :weight normal :height 1.2)))))
  ;; (custom-set-faces
  ;;  '(org-level-3 ((t (:foreground "#090909" :weight normal :height 1.1)))))
  (custom-set-faces
   '(org-image-actual-width '(600)))
  (custom-set-faces
   '(org-block-begin-line ((t (:background "#fbf8ef")))))
  (custom-set-faces
   '(org-block-end-line ((t (:background "#fbf8ef")))))

  (setq default-major-mode 'org-mode)

  (add-hook 'org-mode-hook
            '(lambda ()
               (variable-pitch-mode 1) ;; All fonts with variable pitch.
               (mapc
                (lambda (face) ;; Other fonts with fixed-pitch.
                  (set-face-attribute face nil :inherit 'fixed-pitch))
                (list 'org-code
                      'org-link
                      'org-block
                      'org-table
                      'org-verbatim
                      'org-block-begin-line
                      'org-block-end-line
                      'org-meta-line
                      'org-document-info-keyword)))))

(defun org-fit-agenda-window ()
  "Fit the window to the buffer size."
  (and (memq org-agenda-window-setup '(reorganize-frame))
       (fboundp 'fit-window-to-buffer)
       (fit-window-to-buffer)))

(defun my-org-startup ()
  (org-agenda-list)
  (org-fit-agenda-window)
  (org-agenda-to-appt)
  (call-interactively #'org-resolve-clocks))

(defadvice org-refile-get-location (before clear-refile-history activate)
  "Fit the Org Agenda to its buffer."
  (setq org-refile-history nil))

(defun jump-to-org-agenda ()
  (interactive)
  (push-window-configuration)

  (let ((recordings-dir "~/Dropbox/Apps/Dropvox"))
    (ignore-errors
      (if (directory-files recordings-dir nil "\\`[^.]")
          (find-file recordings-dir))))

  (let ((buf (get-buffer "*Org Agenda(a)*")))
    (if buf
        (let ((wind (get-buffer-window buf)))
          (if wind
              (when (called-interactively-p 'any)
                (select-window wind)
                (org-fit-window-to-buffer))
            (if (called-interactively-p 'any)
                (progn
                  (select-window (display-buffer buf t t))
                  (org-fit-window-to-buffer))
              (with-selected-window (display-buffer buf)
                (org-fit-window-to-buffer)))))
      (call-interactively 'org-agenda-list))))

(defun org-get-global-property (name)
  (save-excursion
    (goto-char (point-min))
    (and (re-search-forward (concat "#\\+PROPERTY: " name " \\(.*\\)") nil t)
         (match-string 1))))

(defun org-agenda-add-overlays (&optional line)
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

  (add-hook 'org-finalize-agenda-hook 'org-agenda-add-overlays)"
  (let ((inhibit-read-only t) l c
        (buffer-invisibility-spec '(org-link)))
    (save-excursion
      (goto-char (if line (point-at-bol) (point-min)))
      (while (not (eobp))
        (let ((org-marker (get-text-property (point) 'org-marker)))
          (when (and org-marker
                     (null (overlays-at (point)))
                     (not (get-text-property (point) 'org-habit-p))
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

(add-hook 'org-finalize-agenda-hook 'org-agenda-add-overlays)

(autoload 'gnus-goto-article "dot-gnus")
(autoload 'gnus-string-remove-all-properties "gnus-util")

(defun gnus-summary-mark-read-and-unread-as-read (&optional new-mark)
  "Intended to be used by `gnus-mark-article-hook'."
  (let ((mark (gnus-summary-article-mark)))
    (when (or (gnus-unread-mark-p mark)
	      (gnus-read-mark-p mark))
      (ignore-errors
        (gnus-summary-mark-article gnus-current-article
                                   (or new-mark gnus-read-mark))))))

(defun org-todo-age-time (&optional pos)
  (let ((stamp (org-entry-get (or pos (point)) "CREATED" t)))
    (when stamp
      (time-subtract (current-time)
                     (org-time-string-to-time
                      (org-entry-get (or pos (point)) "CREATED" t))))))

(defun org-todo-age (&optional pos)
  (let ((days (time-to-number-of-days (org-todo-age-time pos))))
    (cond
     ((< days 1)   "today")
     ((< days 7)   (format "%dd" days))
     ((< days 30)  (format "%.1fw" (/ days 7.0)))
     ((< days 358) (format "%.1fM" (/ days 30.0)))
     (t            (format "%.1fY" (/ days 365.0))))))

(defun org-compare-todo-age (a b)
  (let ((time-a (org-todo-age-time (get-text-property 0 'org-hd-marker a)))
        (time-b (org-todo-age-time (get-text-property 0 'org-hd-marker b))))
    (if (time-less-p time-a time-b)
        -1
      (if (equal time-a time-b)
          0
        1))))

(defun org-my-message-open (message-id)
  (if (get-buffer "*Group*")
      (gnus-goto-article
       (gnus-string-remove-all-properties (substring message-id 2)))
    (error "Gnus is not running")))

(add-to-list 'org-link-protocols (list "message" 'org-my-message-open nil))

(defun save-org-mode-files ()
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq major-mode 'org-mode)
        (if (and (buffer-modified-p) (buffer-file-name))
            (save-buffer))))))

(run-with-idle-timer 25 t 'save-org-mode-files)

(defun my-org-push-mobile ()
  (interactive)
  (with-current-buffer (find-file-noselect "~/Documents/tasks/todo.txt")
    (org-mobile-push)))

(eval-when-compile
  (defvar org-clock-current-task)
  (defvar org-mobile-directory)
  (defvar org-mobile-capture-file))

(defun quickping (host)
  (= 0 (call-process "ping" nil nil nil "-c1" "-W50" "-q" host)))

(defun org-my-auto-exclude-function (tag)
  (and (cond
        ((string= tag "call")
         (let ((hour (nth 2 (decode-time))))
           (or (< hour 8) (> hour 21))))
        ((string= tag "errand")
         (let ((hour (nth 2 (decode-time))))
           (or (< hour 12) (> hour 17))))
        ((or (string= tag "home") (string= tag "nasim"))
         (with-temp-buffer
           (call-process "ifconfig" nil t nil "en0" "inet")
           (call-process "ifconfig" nil t nil "en1" "inet")
           (call-process "ifconfig" nil t nil "bond0" "inet")
           (goto-char (point-min))
           (not (re-search-forward "inet 192\\.168\\.1\\." nil t))))
        ((string= tag "net")
         (not (quickping "imap.fastmail.com")))
        ((string= tag "fun")
         org-clock-current-task))
       (concat "-" tag)))

(defun my-mobileorg-convert ()
  (interactive)
  (while (re-search-forward "^\\* " nil t)
    (goto-char (match-beginning 0))
    (insert ?*)
    (forward-char 2)
    (insert "TODO ")
    (goto-char (line-beginning-position))
    (forward-line)
    (re-search-forward "^\\[")
    (goto-char (match-beginning 0))
    (let ((uuid
           (save-excursion
             (re-search-forward "^\\*\\* Note ID: \\(.+\\)")
             (prog1
                 (match-string 1)
               (delete-region (match-beginning 0)
                              (match-end 0))))))
      ;; (insert (format "SCHEDULED: %s\n:PROPERTIES:\n"
      ;;                 (format-time-string (org-time-stamp-format))))
      (insert ":PROPERTIES:\n")
      (insert (format ":ID:       %s\n:CREATED:  " uuid)))
    (forward-line)
    (insert ":END:")))

(defun my-org-convert-incoming-items ()
  (interactive)
  (with-current-buffer
      (find-file-noselect (expand-file-name org-mobile-capture-file
                                            org-mobile-directory))
    (goto-char (point-min))
    (unless (eobp)
      (my-mobileorg-convert)
      (goto-char (point-max))
      (if (bolp)
          (delete-char -1))
      (let ((tasks (buffer-string)))
        (set-buffer-modified-p nil)
        (kill-buffer (current-buffer))
        (with-current-buffer (find-file-noselect "~/Documents/tasks/todo.txt")
          (save-excursion
            (goto-char (point-min))
            (re-search-forward "^\\* Inbox$")
            (re-search-forward "^:END:")
            (forward-line)
            (goto-char (line-beginning-position))
            (if (and tasks (> (length tasks) 0))
                (insert tasks ?\n))))))))

(defun my-org-mobile-pre-pull-function ()
  (my-org-convert-incoming-items))

(add-hook 'org-mobile-pre-pull-hook 'my-org-mobile-pre-pull-function)

(defun org-my-state-after-clock-out (state)
  (if (string= state "STARTED") "TODO" state))

(defvar org-my-archive-expiry-days 9
  "The number of days after which a completed task should be auto-archived.
This can be 0 for immediate, or a floating point value.")

(defconst org-my-ts-regexp
  "[[<]\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} [^]>\r\n]*?\\)[]>]"
  "Regular expression for fast inactive time stamp matching.")

(defun org-my-closing-time ()
  (let* ((state-regexp
          (concat "- State \"\\(?:" (regexp-opt org-done-keywords)
                  "\\)\"\\s-*\\[\\([^]\n]+\\)\\]"))
         (regexp (concat "\\(" state-regexp "\\|" org-my-ts-regexp "\\)"))
         (end (save-excursion
                (outline-next-heading)
                (point)))
         begin
         end-time)
    (goto-char (line-beginning-position))
    (while (re-search-forward regexp end t)
      (let ((moment (org-parse-time-string (match-string 1))))
        (if (or (not end-time)
                (time-less-p (apply #'encode-time end-time)
                             (apply #'encode-time moment)))
            (setq end-time moment))))
    (goto-char end)
    end-time))

(defun org-archive-expired-tasks ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((done-regexp
           (concat "^\\*\\* \\(" (regexp-opt org-done-keywords) "\\) ")))
      (while (re-search-forward done-regexp nil t)
        (if (>= (time-to-number-of-days
                 (time-subtract (current-time)
                                (apply #'encode-time (org-my-closing-time))))
                org-my-archive-expiry-days)
            (org-archive-subtree))))
    (save-buffer)))

(defalias 'archive-expired-tasks 'org-archive-expired-tasks)

(defun org-archive-done-tasks ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "\* \\(DONE\\|CANCELED\\) " nil t)
      (if (save-restriction
            (save-excursion
              (org-narrow-to-subtree)
              (search-forward ":LOGBOOK:" nil t)))
          (forward-line)
        (org-archive-subtree)
        (goto-char (line-beginning-position))))))

(defalias 'archive-done-tasks 'org-archive-done-tasks)

(defun org-get-inactive-time ()
  (float-time (org-time-string-to-time
               (or (org-entry-get (point) "TIMESTAMP")
                   (org-entry-get (point) "TIMESTAMP_IA")
                   (debug)))))

(defun org-get-completed-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (and (re-search-backward
            (concat "\\(- State \"\\(DONE\\|DEFERRED\\|CANCELED\\)\""
                    "\\s-+\\[\\(.+?\\)\\]\\|CLOSED: \\[\\(.+?\\)\\]\\)")
            begin t)
           (float-time (org-time-string-to-time (or (match-string 3)
                                                    (match-string 4))))))))

(defun org-sort-done-tasks ()
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

(defalias 'sort-done-tasks 'org-sort-done-tasks)

(defun org-sort-all ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^\* " nil t)
      (goto-char (match-beginning 0))
      (condition-case err
          (progn
            ;; (org-sort-entries t ?a)
            (org-sort-entries t ?p)
            (org-sort-entries t ?o))
        (error nil))
      (forward-line))
    (goto-char (point-min))
    (while (re-search-forward "\* PROJECT " nil t)
      (goto-char (line-beginning-position))
      (ignore-errors
        ;; (org-sort-entries t ?a)
        (org-sort-entries t ?p)
        (org-sort-entries t ?o))
      (forward-line))))

(defun org-cleanup ()
  (interactive)
  (org-archive-expired-tasks)
  (org-sort-all))

(defvar my-org-wrap-region-history nil)

(defun my-org-wrap-region (&optional arg)
  (interactive "P")
  (save-excursion
    (goto-char (region-end))
    (if arg
        (insert "#+end_src\n")
      (insert ":END:\n"))
    (goto-char (region-beginning))
    (if arg
        (insert "#+begin_src "
                (read-string "Language: " nil 'my-org-wrap-region-history)
                ?\n)
      (insert ":OUTPUT:\n"))))

(defun org-get-message-link (&optional title)
  (let (message-id subject)
    (with-current-buffer gnus-original-article-buffer
      (setq message-id (substring (message-field-value "message-id") 1 -1)
            subject (or title (message-field-value "subject"))))
    (org-make-link-string (concat "message://" message-id)
                          (rfc2047-decode-string subject))))

(defun org-insert-message-link (&optional arg)
  (interactive "P")
  (insert (org-get-message-link (if arg "writes"))))

(defun org-set-message-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Message" (org-get-message-link)))

(defun org-get-message-sender ()
  (let (message-id subject)
    (with-current-buffer gnus-original-article-buffer
      (message-field-value "from"))))

(defun org-set-message-sender ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Submitter" (org-get-message-sender)))

(defun org-get-safari-link ()
  (let ((subject (substring (do-applescript
                             (string-to-multibyte "tell application \"Safari\"
        name of document of front window
end tell")) 1 -1))
        (url (substring (do-applescript
                         (string-to-multibyte "tell application \"Safari\"
        URL of document of front window
end tell")) 1 -1)))
    (org-make-link-string url subject)))

(defun org-get-chrome-link ()
  (let ((subject (do-applescript
                  (string-to-multibyte "tell application \"Google Chrome\"
        title of active tab of front window
end tell")))
        (url (do-applescript
              (string-to-multibyte "tell application \"Google Chrome\"
        URL of active tab of front window
end tell"))))
    (org-make-link-string (substring url 1 -1) (substring subject 1 -1))))

(defun org-insert-url-link ()
  (interactive)
  (insert (org-get-safari-link)))

(defun org-set-url-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "URL" (org-get-safari-link)))

(defun org-get-file-link ()
  (let* ((subject (do-applescript "tell application \"Path Finder\"
     set theItems to the selection
     name of beginning of theItems
end tell"))
         (path (do-applescript "tell application \"Path Finder\"
     set theItems to the selection
     (POSIX path of beginning of theItems) as text
end tell"))
         (short-path
          (replace-regexp-in-string abbreviated-home-dir "~/"
                                    (substring path 1 -1))))
    (org-make-link-string (concat "file:" short-path)
                          (substring subject 1 -1))))

(defun org-insert-file-link ()
  (interactive)
  (insert (org-get-file-link)))

(defun org-set-file-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "File" (org-get-file-link)))

(defun org-set-dtp-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Document" (org-get-dtp-link)))

(defun org-dtp-message-open ()
  "Visit the message with the given MESSAGE-ID.
This will use the command `open' with the message URL."
  (interactive)
  (re-search-backward "\\[\\[message://\\(.+?\\)\\]\\[")
  (do-applescript
   (format "tell application \"DEVONthink Pro\"
        set searchResults to search \"%%3C%s%%3E\" within URLs
        open window for record (get beginning of searchResults)
end tell" (match-string 1))))

(add-hook 'org-log-buffer-setup-hook
          (lambda ()
            (setq fill-column (- fill-column 5))))

(defun org-message-reply ()
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

;;;_  . keybindings

(defvar org-mode-completion-keys
  '((?d . "DONE")
    (?g . "DELEGATED")
    (?n . "NOTE")
    (?r . "DEFERRED")
    (?s . "STARTED")
    (?t . "TODO")
    (?e . "EPIC")
    (?o . "STORY")
    (?w . "WAITING")
    (?x . "CANCELED")
    (?y . "SOMEDAY")
    ))

(eval-and-compile
  (defvar org-todo-state-map nil)
  (define-prefix-command 'org-todo-state-map))

(dolist (ckey org-mode-completion-keys)
  (let* ((key (car ckey))
         (label (cdr ckey))
         (org-sym (intern (concat "my-org-todo-" (downcase label))))
         (org-sym-no-logging
          (intern (concat "my-org-todo-" (downcase label) "-no-logging")))
         (org-agenda-sym
          (intern (concat "my-org-agenda-todo-" (downcase label))))
         (org-agenda-sym-no-logging
          (intern (concat "my-org-agenda-todo-"
                          (downcase label) "-no-logging"))))
    (eval
     `(progn
        (defun ,org-sym ()
          (interactive)
          (org-todo ,label))
        (bind-key (concat "C-c x " (char-to-string ,key)) ',org-sym
                  org-mode-map)

        (defun ,org-sym-no-logging ()
          (interactive)
          (let ((org-inhibit-logging t))
            (org-todo ,label)))
        (bind-key (concat "C-c x " (char-to-string  ,(upcase key)))
                  ',org-sym-no-logging org-mode-map)

        (defun ,org-agenda-sym ()
          (interactive)
          (let ((org-inhibit-logging
                 (let ((style (org-entry-get
                               (get-text-property (point) 'org-marker)
                               "STYLE")))
                   (and style (stringp style)
                        (string= style "habit")))))
            (org-agenda-todo ,label)))
        (define-key org-todo-state-map [,key] ',org-agenda-sym)

        (defun ,org-agenda-sym-no-logging ()
          (interactive)
          (let ((org-inhibit-logging t))
            (org-agenda-todo ,label)))
        (define-key org-todo-state-map [,(upcase key)]
          ',org-agenda-sym-no-logging)))))

(bind-keys :map org-mode-map
           ("C-c x l" . org-insert-dtp-link)
           ("C-c x L" . org-set-dtp-link)
           ("C-c x m" . org-insert-message-link)
           ("C-c x M" . org-set-message-link)
           ("C-c x u" . org-insert-url-link)
           ("C-c x U" . org-set-url-link)
           ("C-c x f" . org-insert-file-link)
           ("C-c x F" . org-set-file-link)

           ("C-c C-x @" . visible-mode)
           ("C-c M-m"   . my-org-wrap-region)

           ([return]                . org-return-indent)
           ([(control return)]      . other-window)
           ([(control meta return)] . org-insert-heading-after-current))

(remove-hook 'kill-emacs-hook 'org-babel-remove-temporary-directory)

;;;_  . org-agenda-mode

(defun my-org-publish-ical ()
  (interactive)
  (async-shell-command "make -C ~/Documents/tasks"))

(bind-keys :map org-agenda-mode-map
           ("C-c C-x C-p" . my-org-publish-ical)
           ("C-n" . next-line)
           ("C-p" . previous-line)
           ("M-n" . org-agenda-later)
           ("M-p" . org-agenda-earlier)
           (" "   . org-agenda-tree-to-indirect-buffer)
           (">"   . org-agenda-filter-by-top-headline)
           ("g"   . org-agenda-redo)
           ("f"   . org-agenda-date-later)
           ("b"   . org-agenda-date-earlier)
           ("r"   . org-agenda-refile)
           ("F"   . org-agenda-follow-mode)
           ("q"   . delete-window)
           ("x"   . org-todo-state-map)
           ("z"   . pop-window-configuration))

(unbind-key "M-m" org-agenda-keymap)

(defadvice org-agenda-redo (after fit-windows-for-agenda-redo activate)
  "Fit the Org Agenda to its buffer."
  (org-fit-agenda-window))

(defadvice org-agenda (around fit-windows-for-agenda activate)
  "Fit the Org Agenda to its buffer."
  (let ((notes
         (ignore-errors
           (directory-files
            "~/Library/Mobile Documents/iCloud~com~agiletortoise~Drafts4/Documents"
            t "[0-9].*\\.txt\\'" nil))))
    (when notes
      (with-current-buffer (find-file-noselect "~/Documents/tasks/todo.txt")
        (save-excursion
          (goto-char (point-min))
          (re-search-forward "^\\* Inbox$")
          (re-search-forward "^:END:")
          (forward-line 1)
          (dolist (note notes)
            (insert
             "** TODO "
             (with-temp-buffer
               (insert-file-contents note)
               (goto-char (point-min))
               (forward-line)
               (unless (bolp))
               (insert ?\n)
               ;; (insert (format "SCHEDULED: %s\n"
               ;;                 (format-time-string (org-time-stamp-format))))
               (goto-char (point-max))
               (unless (bolp)
                 (insert ?\n))
               (let ((uuid (substring (shell-command-to-string "uuidgen") 0 -1))
                     (file (file-name-nondirectory note)))
                 (insert (format (concat ":PROPERTIES:\n:ID:       %s\n"
                                         ":CREATED:  ") uuid))
                 (string-match
                  (concat "\\`\\([0-9]\\{4\\}\\)"
                          "-\\([0-9]\\{2\\}\\)"
                          "-\\([0-9]\\{2\\}\\)"
                          "-\\([0-9]\\{2\\}\\)"
                          "-\\([0-9]\\{2\\}\\)"
                          "-\\([0-9]\\{2\\}\\)"
                          "\\.txt\\'") file)
                 (let ((year (string-to-number (match-string 1 file)))
                       (mon (string-to-number (match-string 2 file)))
                       (day (string-to-number (match-string 3 file)))
                       (hour (string-to-number (match-string 4 file)))
                       (min (string-to-number (match-string 5 file)))
                       (sec (string-to-number (match-string 6 file))))
                   (insert (format "[%04d-%02d-%02d %s %02d:%02d]\n:END:\n"
                                   year mon day
                                   (calendar-day-name (list mon day year) t)
                                   hour min))))
               (buffer-string)))
            (delete-file note t)))
        (when (buffer-modified-p)
          (save-buffer)))))
  ad-do-it
  (org-fit-agenda-window))

(defun org-refile-heading-p ()
  (let ((heading (org-get-heading)))
    (not (string-match "Colophon" heading))))

(defun org-inline-note ()
  (interactive)
  (switch-to-buffer-other-window "notes.txt")
  (goto-char (point-min))
  (forward-line)
  (goto-char (line-beginning-position))
  (insert "* NOTE ")
  (save-excursion
    (insert (format "\n:PROPERTIES:\n:ID:       %s\n:CREATED:  %s\n:END:\n"
                    (substring (shell-command-to-string "uuidgen") 0 -1)
                    (format-time-string (org-time-stamp-format t t)))))
  (save-excursion
    (forward-line)
    (org-cycle)))

(defadvice org-archive-subtree (before set-billcode-before-archiving activate)
  "Before archiving a task, set its BILLCODE and TASKCODE."
  (let ((billcode (org-entry-get (point) "BILLCODE" t))
        (taskcode (org-entry-get (point) "TASKCODE" t))
        (project  (org-entry-get (point) "PROJECT" t)))
    (if billcode (org-entry-put (point) "BILLCODE" billcode))
    (if taskcode (org-entry-put (point) "TASKCODE" taskcode))
    (if project (org-entry-put (point) "PROJECT" project))))

(font-lock-add-keywords
 'org-mode
 '(("^ *\\(-\\) "
    (0 (ignore (compose-region (match-beginning 1) (match-end 1) "•"))))))

(defconst first-year-in-list 172)

(defconst naw-ruz
  '((3 21 2015)
    (3 20 2016)
    (3 20 2017)
    (3 21 2018)
    (3 21 2019)
    (3 20 2020)
    (3 20 2021)
    (3 21 2022)
    (3 21 2023)
    (3 20 2024)
    (3 20 2025)
    (3 21 2026)
    (3 21 2027)
    (3 20 2028)
    (3 20 2029)
    (3 20 2030)
    (3 21 2031)
    (3 20 2032)
    (3 20 2033)
    (3 20 2034)
    (3 21 2035)
    (3 20 2036)
    (3 20 2037)
    (3 20 2038)
    (3 21 2039)
    (3 20 2040)
    (3 20 2041)
    (3 20 2042)
    (3 21 2043)
    (3 20 2044)
    (3 20 2045)
    (3 20 2046)
    (3 21 2047)
    (3 20 2048)
    (3 20 2049)
    (3 20 2050)
    (3 21 2051)
    (3 20 2052)
    (3 20 2053)
    (3 20 2054)
    (3 21 2055)
    (3 20 2056)
    (3 20 2057)
    (3 20 2058)
    (3 20 2059)
    (3 20 2060)
    (3 20 2061)
    (3 20 2062)
    (3 20 2063)
    (3 20 2064))
  "The days when Naw-Rúz begins, for the next fifty years.")

(defconst days-of-há
  '(4 4 5 4 4 4 5 4 4 4 5 4 4 4 4 5 4 4 4 5 4 4 4 5 4
      4 4 5 4 4 4 5 4 4 4 5 4 4 4 5 4 4 4 4 5 4 4 4 5 4)
  "The days when Naw-Rúz begins, for the next fifty years.")

(defconst bahai-months
  '("Bahá"      ; 1
    "Jalál"     ; 2
    "Jamál"     ; 3
    "‘Aẓamat"   ; 4
    "Núr"       ; 5
    "Raḥmat"    ; 6
    "Kalimát"   ; 7
    "Kamál"     ; 8
    "Asmá’"     ; 9
    "‘Izzat"    ; 10
    "Mashíyyat" ; 11
    "‘Ilm"      ; 12
    "Qudrat"    ; 13
    "Qawl"      ; 14
    "Masá’il"   ; 15
    "Sharaf"    ; 16
    "Sulṭán"    ; 17
    "Mulk"      ; 18
    "‘Alá’"     ; 19
    ))

(eval-and-compile
  (require 'cal-julian)
  (require 'diary-lib))

(defun bahai-date (month day &optional bahai-year)
  (let* ((greg-year (if bahai-year
                        (+ 1844 (1- bahai-year))
                      (nth 2 (calendar-current-date))))
         (year (1+ (- greg-year 1844)))
         (first-day (cl-find-if #'(lambda (x) (= greg-year (nth 2 x)))
                                naw-ruz))
         (greg-base (calendar-julian-to-absolute first-day))
         (hdays (nth (- year first-year-in-list) days-of-há))
         (offset (+ (1- day) (* 19 (1- month))
                    (if (= month 19)
                        hdays
                      0)))
         (greg-date (calendar-julian-from-absolute (+ greg-base offset))))
    (apply #'diary-date greg-date)))

(defun org-current-is-todo ()
  (member (org-get-todo-state) '("TODO" "EPIC" "STORY" "STARTED")))

(defun my-org-agenda-should-skip-p ()
  "Skip all but the first non-done entry."
  (let (should-skip-entry)
    (unless (org-current-is-todo)
      (setq should-skip-entry t))
    (when (or (org-get-scheduled-time (point))
              (org-get-deadline-time (point)))
      (setq should-skip-entry t))
    (when (/= (point)
              (save-excursion
                (org-goto-first-child)
                (point)))
      (setq should-skip-entry t))
    (save-excursion
      (while (and (not should-skip-entry) (org-goto-sibling t))
        (when (and (org-current-is-todo)
                   (not (org-get-scheduled-time (point)))
                   (not (org-get-deadline-time (point))))
          (setq should-skip-entry t))))
    should-skip-entry))

(defun my-org-agenda-skip-all-siblings-but-first ()
  "Skip all but the first non-done entry."
  (when (my-org-agenda-should-skip-p)
    (or (outline-next-heading)
        (goto-char (point-max)))))

(defun my-org-current-tags ()
  (save-excursion
    (ignore-errors
      (let (should-skip)
        (while (and (not should-skip)
                    (not (org-up-element)))
          (if (looking-at "^\*+\\s-+")
              (setq should-skip (org-get-local-tags))))
        should-skip))))

(defun my-org-agenda-skip-all-siblings-but-first-hot ()
  "Skip all but the first non-done entry."
  (when (or (my-org-agenda-should-skip-p)
            (not (member "HOT" (my-org-current-tags))))
    (or (outline-next-heading)
        (goto-char (point-max)))))

(use-package anki-editor
  :commands anki-editor-submit)

(use-package calfw
  :bind (("C-c A" . my-calendar)
         :map cfw:calendar-mode-map
         ("M-n" . cfw:navi-next-month-command)
         ("M-p" . cfw:navi-previous-month-command)
         ("j"   . cfw:navi-goto-date-command)
         ("g"   . cfw:refresh-calendar-buffer))
  :commands cfw:open-calendar-buffer
  :functions (cfw:open-calendar-buffer
              cfw:refresh-calendar-buffer
              cfw:org-create-source
              cfw:cal-create-source)
  :preface
  (defun my-calendar ()
    (interactive)
    (let ((buf (get-buffer "*cfw-calendar*"))
          (org-agenda-files
           (cons "~/Documents/tasks/Nasim.org"
                 (cons "~/Documents/tasks/Sacramento.org"
                       org-agenda-files))))
      (if buf
          (pop-to-buffer buf nil)
        (cfw:open-calendar-buffer
         :contents-sources
         (list (cfw:org-create-source "Dark Blue")
               (cfw:cal-create-source "Dark Orange"))
         :view 'two-weeks)
        (setq-local org-agenda-files org-agenda-files))))

  :config
  (require 'calfw-cal)
  (use-package calfw-org
    :config
    (setq cfw:org-agenda-schedule-args '(:deadline :timestamp :sexp)))

  (setq cfw:fchar-junction ?╋
        cfw:fchar-vertical-line ?┃
        cfw:fchar-horizontal-line ?━
        cfw:fchar-left-junction ?┣
        cfw:fchar-right-junction ?┫
        cfw:fchar-top-junction ?┯
        cfw:fchar-top-left-corner ?┏
        cfw:fchar-top-right-corner ?┓))

(use-package helm-org-rifle
  :bind ("A-M-r" . helm-org-rifle))

(use-package jobhours
  :demand t
  :bind ("M-o j" . jobhours-update-string)
  :config
  (defun my-org-insert-jobhours-string ()
    (interactive)
    (save-excursion
      (goto-char (point-min))
      (goto-char (line-end-position))
      (let* ((width (- (window-width) (current-column)))
             (jobhours (jobhours-get-string t))
             (spacer (- width (length jobhours)))
             (inhibit-read-only t))
        (when (> spacer 0)
          (insert (make-string spacer ? ) jobhours)))))

  (defun my-org-delayed-update ()
    (run-with-idle-timer
     1 nil
     `(lambda ()
        (with-current-buffer ,(current-buffer)
          (org-save-all-org-buffers)
          (my-org-insert-jobhours-string)))))

  (add-hook 'org-agenda-finalize-hook #'my-org-delayed-update t))

(use-package ob-diagrams)

(use-package ob-restclient)

(use-package org-babel
  :no-require
  :after ob-restclient
  :config
  (org-babel-do-load-languages
   'org-babel-load-languages
   '((python     . t)
     (emacs-lisp . t)
     (coq        . t)
     (haskell    . t)
     (calc       . t)
     (ledger     . t)
     (ditaa      . t)
     (plantuml   . t)
     (sh         . t)
     (sql        . t)
     (dot        . t)
     (restclient . t))))

(use-package org-bookmark-heading)

(use-package org-crypt
  :bind (:map org-mode-map
              ("C-c C-x C-/" . org-decrypt-entry)))

(use-package org-devonthink)

(use-package org-gcal
  :disabled t
  :commands org-gcal-sync
  :config
  (setq org-gcal-client-id
        (lookup-password "org-caldav-user.google.com" "jwiegley" 80)
        org-gcal-client-secret
        (lookup-password "org-caldav.google.com" org-gcal-client-id 80)
        org-gcal-file-alist
        '(("jwiegley@gmail.com" .
           "~/Documents/tasks/Google.org")
          ("ajhrtkkubthrda9l40bf95hceo@group.calendar.google.com" .
           "~/Documents/tasks/Bahá'í.org")
          ("57jh2om1vl9sv16sor1mudl030@group.calendar.google.com" .
           "~/Documents/tasks/Family.org")
          ("789ust6872bajeo87oqd2jqfog@group.calendar.google.com" .
           "~/Documents/tasks/Nasim.org")
          ("sacramento.lsa1914@gmail.com" .
           "~/Documents/tasks/Sacramento.org"))))

(use-package org-mime
  :config
  (add-hook 'message-mode-hook
            (lambda ()
              (local-set-key "\C-c\M-o" 'org-mime-htmlize)))

  (add-hook 'org-mode-hook
            (lambda ()
              (local-set-key "\C-c\M-o" 'org-mime-org-buffer-htmlize)))

  (add-hook 'org-mime-html-hook
            (lambda ()
              (org-mime-change-element-style
               "blockquote" "border-left: 2px solid gray; padding-left: 4px;")
              (org-mime-change-element-style
               "pre" (format "color: %s; background-color: %s; padding: 0.5em;"
                             "#E6E1DC" "#232323")))))

(use-package org-opml
  :disabled t)

(use-package org-pdfview
  :config
  (delete '("\\.pdf\\'" . default) org-file-apps)
  (add-to-list 'org-file-apps '("\\.pdf\\'" . org-pdfview-open))
  (add-to-list 'org-file-apps
               '("\\.pdf::\\([[:digit:]]+\\)\\'" . org-pdfview-open)))

(use-package org-protocol)

(use-package org-ref
  ;; jww (2017-12-10): Need to configure.
  :disabled t)

(use-package org-rich-yank
  :defer 5
  :bind (:map org-mode-map
              ("C-M-y" . org-rich-yank)))

(use-package org-smart-capture)

(use-package org-super-agenda
  :disabled t
  :preface
  (defun super-jump-to-org-agenda ()
    (interactive)
    (let ((org-super-agenda-groups
           '((:name "Today"
                    :time-grid t
                    :todo "TODAY")
             (:name "Important"
                    :tag "bills"
                    :priority "A")
             (:order-multi
              (2 (:name "Shopping in town"
                        :and (:tag "shopping" :tag "@town"))
                 (:name "Food-related"
                        :tag ("food" "dinner"))
                 (:name "Personal"
                        :habit t
                        :tag "personal")
                 (:name "Space-related (non-moon-or-planet-related)"
                        :and (:regexp ("space" "NASA")
                                      :not (:regexp "moon" :tag "planet")))))
             (:todo "WAITING" :order 8)
             (:todo ("SOMEDAY" "TO-READ" "CHECK" "TO-WATCH" "WATCHING")
                    :order 9)
             (:priority<= "B" :order 1))))
      (org-agenda nil "a")))
  :config
  (org-super-agenda-mode))

(use-package org-velocity
  :bind ("C-, C-." . org-velocity))

(use-package org-web-tools
  :bind (("C-, C-y" . my-org-insert-url)
         ("C-, C-M-y" . org-web-tools-insert-web-page-as-entry))
  :functions (org-web-tools--org-link-for-url
              org-web-tools--get-first-url)
  :preface
  (declare-function org-web-tools--org-link-for-url "org-web-tools")
  (declare-function org-web-tools--get-first-url "org-web-tools")
  (defun my-org-insert-url (&optional arg)
    (interactive "P")
    (require' org-web-tools)
    (let ((link (org-web-tools--org-link-for-url
                 (org-web-tools--get-first-url))))
      (if arg
          (progn
            (org-set-property "URL" link)
            (message "Added pasteboard link to URL property"))
        (insert link)))))

(use-package orgit
  :disabled t)

(use-package orgnav)

(use-package orgtbl-aggregate
  :config
  (load "org-insert-dblock"))

(use-package ox-confluence
  :commands org-confluence-export-as-confluence)

(use-package ox-gfm
  ;; :demand t
  ;; :commands ox-gfm-export-to-markdown
  )

(use-package ox-jira
  :commands ox-jira-export-as-jira)

(use-package ox-slack
  :commands org-slack-export-to-clipboard-as-slack)

(use-package ox-md)

(use-package ox-pandoc
  :disabled t)

(use-package ox-texinfo-plus
  :defer t)

(use-package yankpad
  :defer 10
  :init
  (setq yankpad-file "~/Documents/tasks/yankpad.org")
  :config
  ;; (bind-key "<f7>" 'yankpad-map)
  ;; (bind-key "<f12>" 'yankpad-expand)
  ;; If you want to complete snippets using company-mode
  ;; (add-to-list 'company-backends #'company-yankpad)
  ;; If you want to expand snippets with hippie-expand
  ;; (add-to-list 'hippie-expand-try-functions-list #'yankpad-expand)
  )

(use-package worf
  :bind (:map org-mode-map
              ("C-c C-j" . worf-goto)))

;; Local Variables:
;;   mode: emacs-lisp
;;   outline-regexp: "^;;;_\\([,. ]+\\)"
;; End:

;;; dot-org.el ends here
