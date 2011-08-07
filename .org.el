;;; -*- mode: emacs-lisp -*-

;;;_* customizations

;;;_ + variables

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(calendar-latitude 40.845112)
 '(calendar-longitude -74.287672)
 '(calendar-mark-holidays-flag t)
 '(diary-file "~/Documents/Tasks/diary")
 '(org-M-RET-may-split-line
   (quote
    ((headline)
     (default . t))))
 '(org-agenda-auto-exclude-function
   (quote org-my-auto-exclude-function))
 '(org-agenda-custom-commands
   (quote
    (("E" "Errands (next 3 days)" tags "Errand&TODO<>\"DONE\"&TODO<>\"CANCELED\"&STYLE<>\"habit\"&SCHEDULED<\"<+3d>\""
      ((org-agenda-overriding-header "Errands (next 3 days)")))
     ("A" "Priority #A tasks" agenda ""
      ((org-agenda-ndays 1)
       (org-agenda-overriding-header "Today's priority #A tasks: ")
       (org-agenda-skip-function
        (quote
         (org-agenda-skip-entry-if
          (quote notregexp)
          "\\=.*\\[#A\\]")))))
     ("b" "Priority #A and #B tasks" agenda ""
      ((org-agenda-ndays 1)
       (org-agenda-overriding-header "Today's priority #A and #B tasks: ")
       (org-agenda-skip-function
        (quote
         (org-agenda-skip-entry-if
          (quote regexp)
          "\\=.*\\[#C\\]")))))
     ("w" "Waiting/delegated tasks" tags "TODO=\"WAITING\"|TODO=\"DELEGATED\""
      ((org-agenda-overriding-header "Waiting/delegated tasks:")
       (org-agenda-sorting-strategy
        (quote
         (todo-state-up priority-down category-up)))))
     ("u" "Unscheduled tasks" tags "AREA<>\"Work\"&TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}"
      ((org-agenda-files
        (quote
         ("~/Documents/Tasks/todo.txt" "~/Documents/Accounts/finances.txt")))
       (org-agenda-overriding-header "Unscheduled tasks: ")
       (org-agenda-skip-function
        (quote
         (org-agenda-skip-entry-if
          (quote scheduled)
          (quote deadline)
          (quote timestamp)
          (quote regexp)
          "\\* \\(DEFERRED\\|SOMEDAY\\)")))
       (org-agenda-sorting-strategy
        (quote
         (priority-down)))))
     ("U" "Deferred tasks" tags "TODO=\"DEFERRED\""
      ((org-agenda-files
        (quote
         ("~/Documents/Tasks/todo.txt" "~/Documents/Accounts/finances.txt")))
       (org-agenda-overriding-header "Deferred tasks:")))
     ("S" "Someday tasks" tags "TODO=\"SOMEDAY\""
      ((org-agenda-overriding-header "Someday tasks:")))
     ("G" "Ledger tasks (all)" alltodo ""
      ((org-agenda-files
        (quote
         ("~/src/ledger/plan/TODO")))
       (org-agenda-overriding-header "Ledger tasks:")
       (org-agenda-sorting-strategy
        (quote
         (todo-state-up priority-down category-up)))))
     ("N" "Ledger tasks (all, alphabetical)" alltodo ""
      ((org-agenda-files
        (quote
         ("~/src/ledger/plan/TODO")))
       (org-agenda-overriding-header "Ledger tasks, alphabetical:")
       (org-agenda-sorting-strategy
        (quote
         (alpha-up)))))
     ("l" "Ledger tasks" tags-todo "TODO<>{SOMEDAY\\|DEFERRED}"
      ((org-agenda-files
        (quote
         ("~/src/ledger/plan/TODO")))
       (org-agenda-overriding-header "Ledger tasks:")
       (org-agenda-sorting-strategy
        (quote
         (todo-state-up priority-down category-up)))
       (org-agenda-skip-function
        (quote
         (org-agenda-skip-entry-if
          (quote regexp)
          "\\=.*\\[#C\\]")))))
     ("L" "Ledger tasks not in Bugzilla" tags "TODO<>{DONE\\|TESTED\\|CLOSED\\|NOTE}&LEVEL=2"
      ((org-agenda-files
        (quote
         ("~/src/ledger/plan/TODO")))
       (org-agenda-overriding-header "Ledger tasks:")
       (org-agenda-sorting-strategy
        (quote
         (todo-state-up priority-down category-up)))
       (org-agenda-skip-function
        (quote
         (org-agenda-skip-entry-if
          (quote regexp)
          "#")))))
     ("r" "Uncategorized items" tags "CATEGORY=\"Inbox\"&LEVEL=2"
      ((org-agenda-overriding-header "Uncategorized items")))
     ("V" "Unscheduled work-related tasks" tags "AREA=\"Work\"&TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}"
      ((org-agenda-overriding-header "Unscheduled work-related tasks")
       (org-agenda-files
        (quote
         ("~/Documents/Tasks/todo.txt")))
       (org-agenda-sorting-strategy
        (quote
         (category-up)))
       (org-agenda-skip-function
        (quote
         (org-agenda-skip-entry-if
          (quote scheduled)
          (quote deadline)
          (quote timestamp)
          (quote regexp)
          "\\* \\(DEFERRED\\|SOMEDAY\\)")))))
     ("W" "Work-related tasks" tags "AREA=\"Work\"&TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}"
      ((org-agenda-overriding-header "Work-related tasks")
       (org-agenda-files
        (quote
         ("~/Documents/Tasks/todo.txt")))
       (org-agenda-sorting-strategy
        (quote
         (category-up priority-down todo-state-up alpha-up)))
       (org-agenda-skip-function
        (quote
         (org-agenda-skip-entry-if
          (quote regexp)
          "\\* \\(DEFERRED\\|SOMEDAY\\)"))))))))
 '(org-agenda-deadline-leaders
   (quote
    ("D: " "D%d: ")))
 '(org-agenda-deadline-relative-text "D%d: ")
 '(org-agenda-deadline-text "D: ")
 '(org-agenda-default-appointment-duration 60)
 '(org-agenda-files
   (quote
    ("~/Documents/Tasks/todo.txt" "~/Documents/Accounts/finances.txt" "~/src/ledger/plan/TODO")))
 '(org-agenda-fontify-priorities t)
 '(org-agenda-include-diary t)
 '(org-agenda-ndays 1)
 '(org-agenda-persistent-filter t)
 '(org-agenda-prefix-format
   (quote
    ((agenda . "  %-11:c%?-12t% s")
     (timeline . "  % s")
     (todo . "  %-11:c")
     (tags . "  %-11:c"))))
 '(org-agenda-scheduled-leaders
   (quote
    ("" "S%d: ")))
 '(org-agenda-scheduled-relative-text "S%d: ")
 '(org-agenda-scheduled-text "")
 '(org-agenda-show-all-dates t)
 '(org-agenda-skip-deadline-if-done t)
 '(org-agenda-skip-scheduled-if-deadline-is-shown t)
 '(org-agenda-skip-scheduled-if-done t)
 '(org-agenda-skip-unavailable-files t)
 '(org-agenda-sorting-strategy
   (quote
    ((agenda habit-down time-up todo-state-up priority-down category-keep)
     (todo priority-down category-keep)
     (tags priority-down category-keep)
     (search category-keep))))
 '(org-agenda-start-on-weekday nil)
 '(org-agenda-tags-column -100)
 '(org-agenda-text-search-extra-files
   (quote
    (agenda-archives)))
 '(org-archive-location "TODO-archive::")
 '(org-archive-save-context-info
   (quote
    (time category itags)))
 '(org-attach-method
   (quote mv))
 '(org-capture-templates
   (quote
    (("t" "Task" entry
      (file+headline "~/Documents/Tasks/todo.txt" "Inbox")
      "* TODO %?
  SCHEDULED: %t
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :CREATED:  %U
  :END:" :prepend t))))
 '(org-clock-idle-time 10)
 '(org-clock-in-resume t)
 '(org-clock-in-switch-to-state "STARTED")
 '(org-clock-into-drawer "LOGBOOK")
 '(org-clock-modeline-total
   (quote current))
 '(org-clock-out-remove-zero-time-clocks t)
 '(org-clock-out-switch-to-state nil)
 '(org-clock-persist
   (quote history))
 '(org-completion-use-ido t)
 '(org-confirm-elisp-link-function nil)
 '(org-confirm-shell-link-function nil)
 '(org-cycle-global-at-bob t)
 '(org-deadline-warning-days 14)
 '(org-default-notes-file "~/Documents/Tasks/todo.txt")
 '(org-directory "~/Documents/Tasks/")
 '(org-drawers
   (quote
    ("PROPERTIES" "CLOCK" "LOGBOOK" "OUT")))
 '(org-enforce-todo-dependencies t)
 '(org-export-babel-evaluate nil)
 '(org-extend-today-until 8)
 '(org-fast-tag-selection-single-key
   (quote expert))
 '(org-footnote-section nil)
 '(org-habit-preceding-days 42)
 '(org-hide-leading-stars t)
 '(org-irc-link-to-logs t t)
 '(org-mobile-directory "~/Dropbox/MobileOrg")
 '(org-mobile-files nil)
 '(org-mobile-inbox-for-pull "~/Documents/Tasks/from-mobile.org")
 '(org-modules
   (quote
    (org-crypt org-gnus org-id org-info org-habit org-irc org-mac-message org-w3m org-annotate-file org-bookmark org-checklist org-depend org-eshell org-eval org-expiry org-git-link org-man)))
 '(org-refile-targets
   (quote
    (("~/Documents/Tasks/todo.txt" :level . 1)
     ("~/Documents/Tasks/todo.txt" :todo . "PROJECT")
     ("~/Documents/Accounts/finances.txt" :level . 1)
     ("~/src/ledger/plan/TODO" :level . 1))))
 '(org-return-follows-link t)
 '(org-reverse-note-order t)
 '(org-tags-column -97)
 '(org-time-clocksum-use-fractional t)
 '(org-todo-keyword-faces
   (quote
    (("TODO" :foreground "medium blue" :weight bold)
     ("APPT" :foreground "medium blue" :weight bold)
     ("NOTE" :foreground "brown" :weight bold)
     ("STARTED" :foreground "dark orange" :weight bold)
     ("WAITING" :foreground "red" :weight bold)
     ("DELEGATED" :foreground "dark violet" :weight bold)
     ("DEFERRED" :foreground "dark blue" :weight bold)
     ("SOMEDAY" :foreground "dark blue" :weight bold)
     ("PROJECT" :foreground "#088e8e" :weight bold))))
 '(org-todo-repeat-to-state "TODO")
 '(org-use-property-inheritance
   (quote
    ("AREA")))
 '(org-use-speed-commands t))

;;;_ + faces

(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(org-habit-alert-face
   ((((background light))
     (:background "#f5f946"))))
 '(org-habit-alert-future-face
   ((((background light))
     (:background "#fafca9"))))
 '(org-habit-clear-face
   ((((background light))
     (:background "#8270f9"))))
 '(org-habit-clear-future-face
   ((((background light))
     (:background "#d6e4fc"))))
 '(org-habit-overdue-face
   ((((background light))
     (:background "#f9372d"))))
 '(org-habit-overdue-future-face
   ((((background light))
     (:background "#fc9590"))))
 '(org-habit-ready-face
   ((((background light))
     (:background "#4df946"))))
 '(org-habit-ready-future-face
   ((((background light))
     (:background "#acfca9"))))
 '(org-scheduled
   ((((class color)
      (min-colors 88)
      (background light))
     nil)))
 '(org-upcoming-deadline
   ((((class color)
      (min-colors 88)
      (background light))
     (:foreground "Brown")))))

;;;_ + org-mode

(require 'org)
(require 'org-agenda)

;;(require 'org-crypt)
(require 'org-devonthink)
(require 'org-x)
(require 'ob-R)
(require 'ob-python)
(require 'ob-emacs-lisp)
;;(require 'ob-haskell)
(require 'ob-sh)

;;(load "org-log" t)

(defun org-info (&optional node)
  "Read documentation for Org-mode in the info system.
With optional NODE, go directly to that node."
  (interactive)
  (info "/Users/johnw/Library/Emacs/site-lisp/org-mode/doc/org"))

(defun org-export-tasks ()
  (interactive)
  (let ((index 1))
    (org-map-entries
     #'(lambda ()
         (outline-mark-subtree)
         (org-export-as-html 3)
         (write-file (format "%d.html" index))
         (kill-buffer (current-buffer))
         (setq index (1+ index)))
     "LEVEL=2")))

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
            (let ((overlays (org-entry-get org-marker "OVERLAY" t)))
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

(defun org-my-message-open (message-id)
  (gnus-goto-article
   (gnus-string-remove-all-properties (substring message-id 2))))

;;(defun org-my-message-open (message-id)
;;  (condition-case err
;;      (if (get-buffer "*Group*")
;;          (gnus-goto-article
;;           (gnus-string-remove-all-properties (substring message-id 2)))
;;        (org-mac-message-open message-id))
;;    (error
;;     (org-mac-message-open message-id))))

(eval-after-load "org-mac-message"
  '(progn
     (let ((protocol (assoc "message" org-link-protocols)))
       (assert protocol)
       (setcar (cdr protocol) 'org-my-message-open))))

(defun org-my-filter-tasks ()
  (and (string-match "opportunities" buffer-file-name)
       (not (member "John" (org-get-tags-at)))
       (progn (outline-next-heading) (point))))

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
	       (version "3.0.0-20100623"))
	   (list product
		 (ido-completing-read "Component: " components
				      nil t nil nil (car (last components)))
		 version
		 (let ((orgpri (nth 3 (org-heading-components))))
		   (if (and orgpri (= ?A orgpri))
		       "P1"
		     (ido-completing-read "Priority: " priorities
					  nil t nil nil "P3")))
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
		       "~/bin/bugzilla-submit http://newartisans.com/bugzilla/"
		       tmpbuf)))
		  (goto-char (point-min))
		  (re-search-forward "Bug \\([0-9]+\\) posted.")
		  (setq bug (match-string 1))))))
	  (save-excursion
	    (org-back-to-heading t)
	    (re-search-forward "\\(TODO\\|DEFERRED\\|STARTED\\|WAITING\\|DELEGATED\\) \\(\\[#[ABC]\\] \\)?")
	    (insert (format "[[bug:%s][#%s]] " bug bug)))))))
  (org-agenda-redo))

(defun save-org-mode-files ()
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq major-mode 'org-mode)
	(if (and (buffer-modified-p) (buffer-file-name))
	    (save-buffer))))))

(run-with-idle-timer 25 t 'save-org-mode-files)

(defun my-org-push-mobile ()
  (interactive)
  (with-current-buffer (find-file-noselect "~/Documents/Tasks/todo.txt")
    (org-mobile-push)))

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
	   (call-process "/sbin/ifconfig" nil t nil "en0" "inet")
	   (call-process "/sbin/ifconfig" nil t nil "en1" "inet")
	   (call-process "/sbin/ifconfig" nil t nil "bond0" "inet")
	   (goto-char (point-min))
	   (not (re-search-forward "inet 192\\.168\\.9\\." nil t))))
	((string= tag "net")
	 (/= 0 (call-process "/sbin/ping" nil nil nil
			     "-c1" "-q" "-t1" "mail.gnu.org")))
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
      (insert (format "   SCHEDULED: %s\n   :PROPERTIES:\n"
                      (format-time-string (org-time-stamp-format))))
      (insert (format "   :ID:       %s\n   :CREATED:  " uuid)))
    (forward-line)
    (insert (format "   :END:"
                    (format-time-string (org-time-stamp-format t t))))))

(defun my-org-convert-incoming-items ()
  (interactive)
  (with-current-buffer
      (find-file-noselect (expand-file-name org-mobile-capture-file
                                            org-mobile-directory))
    (goto-char (point-min))
    (my-mobileorg-convert)
    (let ((tasks (buffer-string)))
      (set-buffer-modified-p nil)
      (kill-buffer (current-buffer))
      (with-current-buffer (find-file-noselect "~/Documents/Tasks/todo.txt")
	(save-excursion
	  (goto-char (point-min))
          (re-search-forward "^\\* Inbox$")
          (re-search-forward "^  :END:")
          (forward-line)
          (goto-char (line-beginning-position))
          (insert tasks ?\n))))))

;;; Don't sync agendas.org to MobileOrg.  I do this because I only use
;;; MobileOrg for recording new tasks on the phone, and never for viewing
;;; tasks.  This allows MobileOrg to start up and sync extremely quickly.

(add-hook 'org-mobile-post-push-hook
          (function
           (lambda ()
             (shell-command "/bin/rm -f ~/Dropbox/MobileOrg/agendas.org")
             (shell-command
              (concat "perl -i -ne 'print unless /agendas\\.org/;'"
                      "~/Dropbox/MobileOrg/checksums.dat"))
             (shell-command
              (concat "perl -i -ne 'print unless /agendas\\.org/;'"
                      "~/Dropbox/MobileOrg/index.org")))))

(add-hook 'org-mobile-pre-pull-hook 'my-org-convert-incoming-items)

(defun org-insert-bug (project bug)
  (interactive
   (list (ido-completing-read "Project: " '("redmine" "bug"))
         (read-number "Bug: ")))
  (insert (format "[[%s:%s][#%s]]" project bug bug)))

(defun org-my-state-after-clock-out (state)
  (if (string= state "STARTED")
      "TODO"
    state))

(defvar org-my-archive-expiry-days 1
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

(defun org-my-archive-done-tasks ()
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

(defalias 'archive-done-tasks 'org-my-archive-done-tasks)

(defun org-get-inactive-time ()
  (float-time (org-time-string-to-time
               (or (org-entry-get (point) "TIMESTAMP")
                   (org-entry-get (point) "TIMESTAMP_IA")
                   (debug)))))

(defun org-get-completed-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (and (re-search-backward "\\(- State \"\\(DONE\\|DEFERRED\\|CANCELED\\)\"\\s-+\\[\\(.+?\\)\\]\\|CLOSED: \\[\\(.+?\\)\\]\\)" begin t)
	   (time-to-seconds (org-time-string-to-time (or (match-string 3)
							 (match-string 4))))))))

(defun org-my-sort-done-tasks ()
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

(defalias 'sort-done-tasks 'org-my-sort-done-tasks)

(defun org-sort-all ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^\* " nil t)
      (goto-char (match-beginning 0))
      (ignore-errors
        (org-sort-entries t ?a)
        (org-sort-entries t ?p)
        (org-sort-entries t ?o))
      (forward-line))
    (goto-char (point-min))
    (while (re-search-forward "\* PROJECT " nil t)
      (goto-char (line-beginning-position))
      (ignore-errors
        (org-sort-entries t ?a)
        (org-sort-entries t ?p)
        (org-sort-entries t ?o))
      (forward-line))))

(defun org-maybe-remember (&optional done)
  (interactive "P")
  (if (string= (buffer-name) "*Remember*")
      (call-interactively 'org-ctrl-c-ctrl-c)
    (if (null done)
	(call-interactively 'org-remember)
      (let ((org-capture-templates
	     '((110 "* STARTED %?
  - State \"STARTED\"    %U
  SCHEDULED: %t
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :CREATED:  %U
  :END:" "~/Documents/Tasks/todo.txt" "Inbox"))))
	(org-remember))))
  (set-fill-column 72))

(defun org-inline-note ()
  (interactive)
  (switch-to-buffer-other-window "todo.txt")
  (goto-char (point-min))
  (re-search-forward "^\\* Inbox$")
  (re-search-forward "^  :END:")
  (forward-line)
  (goto-char (line-beginning-position))
  (insert "** NOTE ")
  (save-excursion
    (insert (format "
   :PROPERTIES:
   :ID:       %s   :VISIBILITY: folded
   :CREATED:  %s
   :END:" (shell-command-to-string "uuidgen")
   (format-time-string (org-time-stamp-format t t))))
    (insert ?\n))
  (save-excursion
    (forward-line)
    (org-cycle)))

(defun org-remember-note ()
  (interactive)
  (if (string= (buffer-name) "*Remember*")
      (call-interactively 'org-ctrl-c-ctrl-c)
    (let ((org-capture-templates
	   '((110 "* NOTE %?
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :VISIBILITY: folded
  :CREATED:  %U
  :END:" "~/Documents/Tasks/todo.txt" "Inbox"))))
      (call-interactively 'org-remember))))

(defun org-get-apple-message-link ()
  (let ((subject (do-applescript "tell application \"Mail\"
        set theMessages to selection
        subject of beginning of theMessages
end tell"))
        (message-id (do-applescript "tell application \"Mail\"
        set theMessages to selection
        message id of beginning of theMessages
end tell")))
    (org-make-link-string (concat "message://" message-id) subject)))

(defun org-get-message-sender ()
  (do-applescript "tell application \"Mail\"
        set theMessages to selection
        sender of beginning of theMessages
end tell"))

(defun org-insert-apple-message-link ()
  (interactive)
  (insert (org-get-apple-message-link)))

(defun org-get-message-link ()
  (if (get-buffer "*Group*")
      (let (message-id subject)
        (with-current-buffer gnus-original-article-buffer
          (nnheader-narrow-to-headers)
          (setq message-id (substring (message-fetch-field "message-id") 1 -1)
                subject (message-fetch-field "subject")))
        (org-make-link-string (concat "message://" message-id) subject))
    (org-get-apple-message-link)))

(defun org-insert-message-link ()
  (interactive)
  (insert (org-get-message-link)))

(defun org-set-message-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Message" (org-get-message-link)))

(defun org-set-message-sender ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Submitter" (org-get-message-sender)))

(defun org-get-safari-link ()
  (let ((subject (do-applescript "tell application \"Safari\"
        name of document of front window
end tell"))
        (url (do-applescript "tell application \"Safari\"
        URL of document of front window
end tell")))
    (org-make-link-string url subject)))

(defun org-get-chrome-link ()
  (let ((subject (do-applescript "tell application \"Google Chrome\"
        title of active tab of front window
end tell"))
        (url (do-applescript "tell application \"Google Chrome\"
        URL of active tab of front window
end tell")))
    (org-make-link-string url subject)))

(defun org-insert-url-link ()
  (interactive)
  (insert (org-get-chrome-link)))

(defun org-set-url-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "URL" (org-get-chrome-link)))

(defun org-get-file-link ()
  (let ((subject (do-applescript "tell application \"Finder\"
	set theItems to the selection
	name of beginning of theItems
end tell"))
        (path (do-applescript "tell application \"Finder\"
	set theItems to the selection
	POSIX path of (beginning of theItems as text)
end tell")))
    (org-make-link-string (concat "file:" path) subject)))

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

(fset 'orgify-line
   [?\C-k ?\C-o ?t ?o ?d ?o tab ?\C-y backspace ?\C-a ?l ?\C-u ?\C-n ?\C-n ?\C-n])

(add-hook 'org-log-buffer-setup-hook
          (lambda ()
            (setq fill-column (- fill-column 5))))

;;;_ + howm-mode

(setq howm-view-title-header "*") ;; *BEFORE* loading howm!

(add-hook 'org-agenda-mode-hook (lambda () (local-unset-key (kbd "\C-c,"))))
(add-hook 'org-mode-hook (lambda () (local-unset-key (kbd "\C-c,"))))

(when (load "howm" t)
  (add-to-list 'auto-mode-alist '("\\.howm$" . org-mode))

  (defun org-howm-template (&rest ignore-args)
    (format
     "* %%title%%cursor
  :PROPERTIES:
  :ID:       %s  :CREATED:  %s
  :END:
   "
     (shell-command-to-string "uuidgen")
     (format-time-string (org-time-stamp-format t t))))

  (defun move-org-note-to-howm ()
    (interactive)
    (let* ((created
            (save-excursion
              (re-search-forward
               ":CREATED:\\s-*\\[\\(.+?\\)\\]")
              (match-string 1)))
           (path
            (expand-file-name
             (format-time-string "%Y/%m/%Y-%m-%d-%H%M%S.howm"
                                 (apply 'encode-time
                                        (org-parse-time-string created)))
             howm-directory))
           (entry (org-x-parse-entry)))
      (org-x-delete-entry)
      (org-x-clear-state entry)
      (org-x-set-depth entry 1)
      (org-x-set-property entry "VISIBILITY" "all")
      (let ((dir (file-name-directory path)))
        (unless (file-directory-p dir)
          (make-directory dir t))
        (with-current-buffer (find-file-noselect path)
          (erase-buffer)
          (org-x-insert-entry entry)
          (save-buffer)
          (kill-buffer (current-buffer))))))

  (setq howm-template 'org-howm-template)

  (define-key org-mode-map [(control ?c) tab] 'action-lock-magic-return))

;;;_* keybindings

;;;_ + global

(defun org-smart-capture ()
  (interactive)
  (if (string-match "\\`\\*Summary " (buffer-name))
      (let (message-id subject)
        (with-current-buffer gnus-original-article-buffer
          (nnheader-narrow-to-headers)
          (setq message-id (message-fetch-field "message-id")
                subject (message-fetch-field "subject")
                from (message-fetch-field "from")
                date-sent (message-fetch-field "date")))
        (org-capture nil "t")
        (save-excursion
          (insert (replace-regexp-in-string
                   "\\[.*? - [A-Za-z]+ #\\([0-9]+\\)\\] (New)"
                   "[[redmine:\\1][#\\1]]"
                   (replace-regexp-in-string "^\\(Re\\|Fwd\\): " ""
                                             subject))))
        (org-set-property "Date" date-sent)
        (org-set-property "Message"
                          (format "[[message://%s][%s]]"
                                  (substring message-id 1 -1)
                                  (subst-char-in-string
                                   ?\[ ?\{ (subst-char-in-string
                                            ?\] ?\} subject))))
        (org-set-property "Submitter" from))
    (org-capture nil "t")))

(define-key mode-specific-map [?x ?d]
  #'(lambda nil (interactive) (org-todo "DONE")))
(define-key mode-specific-map [?x ?r]
  #'(lambda nil (interactive) (org-todo "DEFERRED")))
(define-key mode-specific-map [?x ?y]
  #'(lambda nil (interactive) (org-todo "SOMEDAY")))
(define-key mode-specific-map [?x ?g]
  #'(lambda nil (interactive) (org-todo "DELEGATED")))
(define-key mode-specific-map [?x ?n]
  #'(lambda nil (interactive) (org-todo "NOTE")))
(define-key mode-specific-map [?x ?s]
  #'(lambda nil (interactive) (org-todo "STARTED")))
(define-key mode-specific-map [?x ?t]
  #'(lambda nil (interactive) (org-todo "TODO")))
(define-key mode-specific-map [?x ?w]
  #'(lambda nil (interactive) (org-todo "WAITING")))
(define-key mode-specific-map [?x ?x]
  #'(lambda nil (interactive) (org-todo "CANCELED")))

(define-key mode-specific-map [?x ?l] 'org-insert-dtp-link)
(define-key mode-specific-map [?x ?L] 'org-set-dtp-link)

(define-key mode-specific-map [?x ?m] 'org-insert-message-link)
(define-key mode-specific-map [?x ?M] 'org-set-message-link)
(define-key mode-specific-map [?x ?a] 'org-insert-apple-message-link)
(define-key mode-specific-map [?x ?Y] 'org-set-message-sender)

(define-key mode-specific-map [?x ?u] 'org-insert-url-link)
(define-key mode-specific-map [?x ?U] 'org-set-url-link)

(define-key mode-specific-map [?x ?f] 'org-insert-file-link)
(define-key mode-specific-map [?x ?F] 'org-set-file-link)

(define-key mode-specific-map [?x ?b] 'org-insert-bug)

;;;_ + org-mode

(eval-after-load "org"
  '(progn
     (org-defkey org-mode-map [(control meta return)]
                 'org-insert-heading-after-current)
     (org-defkey org-mode-map [(control return)] 'other-window)
     (org-defkey org-mode-map [return] 'org-return-indent)))

(defun org-fit-agenda-window ()
  "Fit the window to the buffer size."
  (and (memq org-agenda-window-setup '(reorganize-frame))
       (fboundp 'fit-window-to-buffer)
       (fit-window-to-buffer)))

(defun yas/org-very-safe-expand ()
  (let ((yas/fallback-behavior 'return-nil)) (yas/expand)))

(add-hook 'org-mode-hook
          (lambda ()
            ;; yasnippet (using the new org-cycle hooks)
            (make-variable-buffer-local 'yas/trigger-key)
            (setq yas/trigger-key [tab])
            (add-to-list 'org-tab-first-hook 'yas/org-very-safe-expand)
            (define-key yas/keymap [tab] 'yas/next-field)))

(remove-hook 'kill-emacs-hook
             'org-babel-remove-temporary-directory)

;;;_ + org-agenda-mode

(dolist (map (list org-agenda-keymap org-agenda-mode-map))
  (define-key map "\C-n" 'next-line)
  (define-key map "\C-p" 'previous-line)

  (define-key map "g" 'org-agenda-redo)
  (define-key map "r"
    #'(lambda nil
        (interactive)
        (error "The 'r' command is deprecated here; use 'g'")))
  (define-key map "f" 'org-agenda-date-later)
  (define-key map "b" 'org-agenda-date-earlier)
  (define-key map "r" 'org-agenda-refile)
  (define-key map " " 'org-agenda-tree-to-indirect-buffer)
  (define-key map "F" 'org-agenda-follow-mode)
  (define-key map "q" 'delete-window)
  (define-key map [(meta ?p)] 'org-agenda-earlier)
  (define-key map [(meta ?n)] 'org-agenda-later)

  (define-prefix-command 'org-todo-state-map)

  (define-key map "x" 'org-todo-state-map)

  (defun org-todo-mark-done ()
    (interactive) (org-agenda-todo "DONE"))
  (defun org-todo-mark-deferred ()
    (interactive) (org-agenda-todo "DEFERRED"))
  (defun org-todo-mark-someday ()
    (interactive) (org-agenda-todo "SOMEDAY"))
  (defun org-todo-mark-delegated ()
    (interactive) (org-agenda-todo "DELEGATED"))
  (defun org-todo-mark-note ()
    (interactive) (org-agenda-todo "NOTE"))
  (defun org-todo-mark-started ()
    (interactive) (org-agenda-todo "STARTED"))
  (defun org-todo-mark-todo ()
    (interactive) (org-agenda-todo "TODO"))
  (defun org-todo-mark-waiting ()
    (interactive) (org-agenda-todo "WAITING"))
  (defun org-todo-mark-canceled ()
    (interactive) (org-agenda-todo "CANCELED"))

  (define-key org-todo-state-map "d" #'org-todo-mark-done)
  (define-key org-todo-state-map "r" #'org-todo-mark-deferred)
  (define-key org-todo-state-map "y" #'org-todo-mark-someday)
  (define-key org-todo-state-map "g" #'org-todo-mark-delegated)
  (define-key org-todo-state-map "n" #'org-todo-mark-note)
  (define-key org-todo-state-map "s" #'org-todo-mark-started)
  (define-key org-todo-state-map "t" #'org-todo-mark-todo)
  (define-key org-todo-state-map "w" #'org-todo-mark-waiting)
  (define-key org-todo-state-map "x" #'org-todo-mark-canceled)

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
       ((string= "BoostPro" (car path))
        (call-interactively #'org-x-redmine-post-issue))
       (t
        (error "Cannot make bug, unknown category")))))

  (define-key org-todo-state-map "z" #'make-bug-link))

(defadvice org-agenda-redo (after fit-windows-for-agenda activate)
  "Fit the Org Agenda to its buffer."
  (org-fit-agenda-window))

(provide 'dot-org-el)

;; .org.el ends here
