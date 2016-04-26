;;;_ , Org-mode

(require 'cl)
(require 'use-package)

(load "org-settings")

(require 'org)
(require 'org-agenda)
(require 'org-smart-capture)
(require 'org-crypt)
(require 'org-bbdb)
(require 'org-devonthink)
(require 'org-mac-link)
;; (require 'org-magit)
(require 'org-velocity)
(require 'ob-python)
(require 'ob-ruby)
(require 'ob-emacs-lisp)
(require 'ob-haskell)
(require 'ob-sh)
(require 'ox-md)
;; (require 'ox-opml)

(declare-function cfw:open-calendar-buffer "calfw")
(declare-function cfw:refresh-calendar-buffer "calfw")
(declare-function cfw:org-create-source "calfw-org")
(declare-function cfw:cal-create-source "calfw-cal")

(defun org-fit-agenda-window ()
  "Fit the window to the buffer size."
  (and (memq org-agenda-window-setup '(reorganize-frame))
       (fboundp 'fit-window-to-buffer)
       (fit-window-to-buffer)))

(defun my-org-startup ()
  (org-agenda-list)
  (org-fit-agenda-window)
  (org-agenda-to-appt)
  ;; (other-window 1)
  ;; (my-calendar)
  ;; (run-with-idle-timer
  ;;  0.1 nil
  ;;  (lambda ()
  ;;    (let ((wind (get-buffer-window "*Org Agenda*")))
  ;;      (when wind
  ;;        (set-frame-selected-window nil wind)
  ;;        (call-interactively #'org-agenda-redo)))
  ;;    (let ((wind (get-buffer-window "*cfw-calendar*")))
  ;;      (when wind
  ;;        (set-frame-selected-window nil wind)
  ;;        (call-interactively #'cfw:refresh-calendar-buffer)))
  ;;    (let ((wind (get-buffer-window "*Org Agenda*")))
  ;;      (when wind
  ;;        (set-frame-selected-window nil wind)
  ;;        (call-interactively #'org-resolve-clocks)))))
  )

(defun my-calendar ()
  (interactive)
  (let ((buf (get-buffer "*cfw-calendar*")))
    (if buf
        (pop-to-buffer buf nil)
      (cfw:open-calendar-buffer
       :contents-sources
       (list (cfw:org-create-source "Dark Blue")
             (cfw:cal-create-source "Dark Orange"))
       :view 'two-weeks))))

(use-package org-autolist
  :load-path "site-lisp/org-autolist"
  :commands org-autolist-mode)

(use-package calfw
  :load-path "site-lisp/emacs-calfw"
  :bind ("C-c A" . my-calendar)
  :init
  (progn
    (use-package calfw-cal)
    (use-package calfw-org)

    (bind-key "M-n" 'cfw:navi-next-month-command cfw:calendar-mode-map)
    (bind-key "M-p" 'cfw:navi-previous-month-command cfw:calendar-mode-map))

  :config
  (progn
    ;; Unicode characters
    (setq cfw:fchar-junction ?╋
          cfw:fchar-vertical-line ?┃
          cfw:fchar-horizontal-line ?━
          cfw:fchar-left-junction ?┣
          cfw:fchar-right-junction ?┫
          cfw:fchar-top-junction ?┯
          cfw:fchar-top-left-corner ?┏
          cfw:fchar-top-right-corner ?┓)

    (bind-key "j" 'cfw:navi-goto-date-command cfw:calendar-mode-map)
    (bind-key "g" 'cfw:refresh-calendar-buffer cfw:calendar-mode-map)))

(defadvice org-refile-get-location (before clear-refile-history activate)
  "Fit the Org Agenda to its buffer."
  (setq org-refile-history nil))

(defun jump-to-org-agenda ()
  (interactive)
  (let ((recordings-dir "~/Dropbox/Apps/Dropvox"))
    (ignore-errors
      (if (directory-files recordings-dir nil "\\`[^.]")
          (find-file recordings-dir))))
  (let ((buf (get-buffer "*Org Agenda*"))
        wind)
    (if buf
        (if (setq wind (get-buffer-window buf))
            (when (called-interactively-p 'any)
              (select-window wind)
              (org-fit-window-to-buffer))
          (if (called-interactively-p 'any)
              (progn
                (select-window (display-buffer buf t t))
                (org-fit-window-to-buffer))
            (with-selected-window (display-buffer buf)
              (org-fit-window-to-buffer))))
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

(defun org-my-message-open (message-id)
  (if (get-buffer "*Group*")
      (gnus-goto-article
       (gnus-string-remove-all-properties (substring message-id 2)))
    (org-mac-message-open message-id)))

;; (defun org-my-message-open (message-id)
;;   (condition-case err
;;       (if (get-buffer "*Group*")
;;           (gnus-goto-article
;;            (gnus-string-remove-all-properties (substring message-id 2)))
;;         (org-mac-message-open message-id))
;;     (error
;;      (org-mac-message-open message-id))))

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
  (with-current-buffer (find-file-noselect "~/doc/tasks/todo.txt")
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
           (not (re-search-forward "inet 192\\.168\\.9\\." nil t))))
        ((string= tag "net")
         (not (quickping "imap.gmail.com")))
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
      (insert (format "SCHEDULED: %s\n:PROPERTIES:\n"
                      (format-time-string (org-time-stamp-format))))
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
        (with-current-buffer (find-file-noselect "~/doc/tasks/todo.txt")
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

;;;_  . make-bug-link

(defun make-ledger-bugzilla-bug (product component version priority severity)
  (interactive
   (let ((omk (get-text-property (point) 'org-marker)))
     (with-current-buffer (marker-buffer omk)
       (save-excursion
         (goto-char omk)
         (let ((components
                (list "data" "doc" "expr" "lisp" "math" "python" "report"
                      "test" "util" "website" "build" "misc"))
               (priorities (list "P1" "P2" "P3" "P4" "P5"))
               (severities (list "blocker" "critical" "major"
                                 "normal" "minor" "trivial" "enhancement"))
               (product "Ledger")
               (version "3.0.0-20120217"))
           (list product
                 (ido-completing-read "Component: " components
                                      nil t nil nil (car (last components)))
                 version
                 (let ((orgpri (nth 3 (org-heading-components))))
                   (cond
                    ((and orgpri (= ?A orgpri))
                     "P1")
                    ((and orgpri (= ?C orgpri))
                     "P3")
                    (t
                     (ido-completing-read "Priority: " priorities
                                          nil t nil nil "P2"))))
                 (ido-completing-read "Severity: " severities nil t nil nil
                                      "normal") ))))))
  (let ((omk (get-text-property (point) 'org-marker)))
    (with-current-buffer (marker-buffer omk)
      (save-excursion
        (goto-char omk)
        (let ((heading (nth 4 (org-heading-components)))
              (contents (buffer-substring-no-properties
                         (org-entry-beginning-position)
                         (org-entry-end-position)))
              bug)
          (with-temp-buffer
            (insert contents)
            (goto-char (point-min))
            (delete-region (point) (1+ (line-end-position)))
            (search-forward ":PROP")
            (delete-region (match-beginning 0) (point-max))
            (goto-char (point-min))
            (while (re-search-forward "^   " nil t)
              (delete-region (match-beginning 0) (match-end 0)))
            (goto-char (point-min))
            (while (re-search-forward "^SCHE" nil t)
              (delete-region (match-beginning 0) (1+ (line-end-position))))
            (goto-char (point-min))
            (when (eobp)
              (insert "No description.")
              (goto-char (point-min)))
            (insert (format "Product: %s
Component: %s
Version: %s
Priority: %s
Severity: %s
Hardware: Other
OS: Other
Summary: %s" product component version priority severity heading) ?\n ?\n)
            (let ((buf (current-buffer)))
              (with-temp-buffer
                (let ((tmpbuf (current-buffer)))
                  (if nil
                      (insert "Bug 999 posted.")
                    (with-current-buffer buf
                      (shell-command-on-region
                       (point-min) (point-max)
                       "~/bin/bugzilla-submit http://bugs.ledger-cli.org/"
                       tmpbuf)))
                  (goto-char (point-min))
                  (or (re-search-forward "Bug \\([0-9]+\\) posted." nil t)
                      (debug))
                  (setq bug (match-string 1))))))
          (save-excursion
            (org-back-to-heading t)
            (re-search-forward
             (concat "\\(TODO\\|DEFERRED\\|STARTED\\|WAITING\\|DELEGATED\\)"
                     " \\(\\[#[ABC]\\] \\)?"))
            (insert (format "[[bug:%s][#%s]] " bug bug)))))))
  (org-agenda-redo))

(defun make-bug-link ()
  (interactive)
  (let* ((omk (get-text-property (point) 'org-marker))
         (path (with-current-buffer (marker-buffer omk)
                 (save-excursion
                   (goto-char omk)
                   (org-get-outline-path)))))
    (cond
     ((string-match "/ledger/" (buffer-file-name (marker-buffer omk)))
      (call-interactively #'make-ledger-bugzilla-bug))
     (t
      (error "Cannot make bug, unknown category")))))

;;;_  . keybindings

(defvar org-mode-completion-keys
  '((?d . "DONE")
    (?g . "DELEGATED")
    (?n . "NOTE")
    (?r . "DEFERRED")
    (?s . "STARTED")
    (?t . "TODO")
    (?w . "WAITING")
    (?x . "CANCELED")
    (?y . "SOMEDAY")
    ))

(defvar org-todo-state-map nil)
(define-prefix-command 'org-todo-state-map)

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
        (bind-key (concat "C-c x " (char-to-string ,key)) ',org-sym)

        (defun ,org-sym-no-logging ()
          (interactive)
          (let ((org-inhibit-logging t))
            (org-todo ,label)))
        (bind-key (concat "C-c x " (char-to-string  ,(upcase key)))
                  ',org-sym-no-logging)

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

(bind-key "C-c x b"
          (lambda (bug) (error "Define bug syntax!")
            ;; (interactive "sBug: ")
            ;; (insert (format "[[project:%s][#%s]]" bug bug))
            ))
(bind-key "C-c x l" 'org-insert-dtp-link)
(bind-key "C-c x L" 'org-set-dtp-link)
(bind-key "C-c x m" 'org-insert-message-link)
(bind-key "C-c x M" 'org-set-message-link)
(bind-key "C-c x u" 'org-insert-url-link)
(bind-key "C-c x U" 'org-set-url-link)
(bind-key "C-c x f" 'org-insert-file-link)
(bind-key "C-c x F" 'org-set-file-link)

(org-defkey org-mode-map [(control meta return)]
            'org-insert-heading-after-current)
(org-defkey org-mode-map [(control return)] 'other-window)
(org-defkey org-mode-map [return] 'org-return-indent)
(org-defkey org-mode-map [(control ?c) (control ?x) ?@] 'visible-mode)
(org-defkey org-mode-map [(control ?c) (meta ?m)] 'my-org-wrap-region)

(remove-hook 'kill-emacs-hook 'org-babel-remove-temporary-directory)

;;;_  . org-agenda-mode

(let ((map org-agenda-mode-map))
  (define-key map "\C-n" 'next-line)
  (define-key map "\C-p" 'previous-line)

  (define-key map "g" 'org-agenda-redo)
  (define-key map "f" 'org-agenda-date-later)
  (define-key map "b" 'org-agenda-date-earlier)
  (define-key map "r" 'org-agenda-refile)
  (define-key map " " 'org-agenda-tree-to-indirect-buffer)
  (define-key map "F" 'org-agenda-follow-mode)
  (define-key map "q" 'delete-window)
  (define-key map [(meta ?p)] 'org-agenda-earlier)
  (define-key map [(meta ?n)] 'org-agenda-later)
  (define-key map "x" 'org-todo-state-map)

  (define-key map ">" 'org-agenda-filter-by-top-headline)

  (define-key org-todo-state-map "z" 'make-bug-link))

(unbind-key "M-m" org-agenda-keymap)

(defadvice org-agenda-redo (after fit-windows-for-agenda-redo activate)
  "Fit the Org Agenda to its buffer."
  (org-fit-agenda-window))

(defadvice org-agenda (around fit-windows-for-agenda activate)
  "Fit the Org Agenda to its buffer."
  (let ((notes (ignore-errors
                 (directory-files
                  "~/Dropbox/Apps/Drafts/" t "[0-9].*\\.txt\\'" nil))))
    (when notes
      (with-current-buffer (find-file-noselect "~/doc/tasks/todo.txt")
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
               (insert (format "SCHEDULED: %s\n"
                               (format-time-string (org-time-stamp-format))))
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

(defadvice org-archive-subtree (before set-billcode-before-archiving activate)
  "Before archiving a task, set its BILLCODE and TASKCODE."
  (let ((billcode (org-entry-get (point) "BILLCODE" t))
        (taskcode (org-entry-get (point) "TASKCODE" t))
        (project  (org-entry-get (point) "PROJECT" t)))
    (if billcode (org-entry-put (point) "BILLCODE" billcode))
    (if taskcode (org-entry-put (point) "TASKCODE" taskcode))
    (if project (org-entry-put (point) "PROJECT" project))))

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

(defun bahai-date (month day &optional bahai-year)
  (let* ((greg-year (if bahai-year
                        (+ 1844 (1- bahai-year))
                      (nth 2 (calendar-current-date))))
         (year (1+ (- greg-year 1844)))
         (first-day (find-if #'(lambda (x) (= greg-year (nth 2 x)))
                             naw-ruz))
         (greg-base (calendar-julian-to-absolute first-day))
         (hdays (nth (- year first-year-in-list) days-of-há))
         (offset (+ (1- day) (* 19 (1- month))
                    (if (= month 19)
                        hdays
                      0)))
         (greg-date (calendar-julian-from-absolute (+ greg-base offset))))
    (apply #'diary-date greg-date)))

(provide 'dot-org)

;; Local Variables:
;;   mode: emacs-lisp
;;   outline-regexp: "^;;;_\\([,. ]+\\)"
;; End:

;;; dot-org.el ends here
