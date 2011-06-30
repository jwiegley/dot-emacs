;;; -*- mode: emacs-lisp -*-

(require 'org)
(require 'org-agenda)
(require 'org-crypt)
(require 'org-install)
(require 'org-attach)
(require 'org-devonthink)
(require 'ob-R)
(require 'ob-python)
(require 'ob-emacs-lisp)
(require 'ob-haskell)
(require 'ob-sh)

;;(load "org-log" t)

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
 '(org-M-RET-may-split-line (quote ((headline) (default . t))))
 '(org-agenda-auto-exclude-function (quote org-my-auto-exclude-function))
 '(org-agenda-custom-commands (quote (("E" "Errands (next 3 days)" tags "Errand&TODO<>\"DONE\"&TODO<>\"CANCELED\"&STYLE<>\"habit\"&SCHEDULED<\"<+3d>\"" ((org-agenda-overriding-header "Errands (next 3 days)"))) ("A" "Priority #A tasks" agenda "" ((org-agenda-ndays 1) (org-agenda-overriding-header "Today's priority #A tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote notregexp) "\\=.*\\[#A\\]"))))) ("B" "Priority #A and #B tasks" agenda "" ((org-agenda-ndays 1) (org-agenda-overriding-header "Today's priority #A and #B tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\=.*\\[#C\\]"))))) ("w" "Waiting/delegated tasks" tags "TODO=\"WAITING\"|TODO=\"DELEGATED\"" ((org-agenda-overriding-header "Waiting/delegated tasks:") (org-agenda-sorting-strategy (quote (todo-state-up priority-down category-up))))) ("u" "Unscheduled tasks" tags "TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}" ((org-agenda-files (quote ("~/Documents/Tasks/todo.txt" "~/Documents/Accounts/finances.txt"))) (org-agenda-overriding-header "Unscheduled tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote scheduled) (quote deadline) (quote timestamp) (quote regexp) "\\* \\(DEFERRED\\|SOMEDAY\\)"))) (org-agenda-sorting-strategy (quote (priority-down))))) ("U" "Deferred tasks" tags "TODO=\"DEFERRED\"" ((org-agenda-files (quote ("~/Documents/Tasks/todo.txt" "~/Documents/Accounts/finances.txt"))) (org-agenda-overriding-header "Deferred tasks:"))) ("S" "Someday tasks" tags "TODO=\"SOMEDAY\"" ((org-agenda-overriding-header "Someday tasks:"))) ("G" "Ledger tasks (all)" alltodo "" ((org-agenda-files (quote ("~/src/ledger/plan/TODO"))) (org-agenda-overriding-header "Ledger tasks:") (org-agenda-sorting-strategy (quote (todo-state-up priority-down category-up))))) ("N" "Ledger tasks (all, alphabetical)" alltodo "" ((org-agenda-files (quote ("~/src/ledger/plan/TODO"))) (org-agenda-overriding-header "Ledger tasks, alphabetical:") (org-agenda-sorting-strategy (quote (alpha-up))))) ("l" "Ledger tasks" tags-todo "TODO<>{SOMEDAY\\|DEFERRED}" ((org-agenda-files (quote ("~/src/ledger/plan/TODO"))) (org-agenda-overriding-header "Ledger tasks:") (org-agenda-sorting-strategy (quote (todo-state-up priority-down category-up))) (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\=.*\\[#C\\]"))))) ("L" "Ledger tasks not in Bugzilla" tags "TODO<>{DONE\\|TESTED\\|CLOSED\\|NOTE}&LEVEL=2" ((org-agenda-files (quote ("~/src/ledger/plan/TODO"))) (org-agenda-overriding-header "Ledger tasks:") (org-agenda-sorting-strategy (quote (todo-state-up priority-down category-up))) (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "#"))))) ("r" "Uncategorized items" tags "CATEGORY=\"Inbox\"&LEVEL=2" ((org-agenda-overriding-header "Uncategorized items"))) ("V" "Unscheduled work-related tasks" tags "AREA=\"Work\"TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}" ((org-agenda-overriding-header "Unscheduled work-related tasks") (org-agenda-files (quote ("~/Documents/Tasks/todo.txt"))) (org-agenda-sorting-strategy (quote (category-up))) (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote scheduled) (quote deadline) (quote timestamp) (quote regexp) "\\* \\(DEFERRED\\|SOMEDAY\\)"))))) ("W" "Work-related tasks" tags "AREA=\"Work\"TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}" ((org-agenda-overriding-header "Work-related tasks") (org-agenda-files (quote ("~/Documents/Tasks/todo.txt"))) (org-agenda-sorting-strategy (quote (category-up))) (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\* \\(DEFERRED\\|SOMEDAY\\)"))))))))
 '(org-agenda-deadline-leaders (quote ("D: " "D%d: ")))
 '(org-agenda-deadline-relative-text "D%d: ")
 '(org-agenda-deadline-text "D: ")
 '(org-agenda-default-appointment-duration 60)
 '(org-agenda-files (quote ("~/Documents/Tasks/todo.txt" "~/Documents/Accounts/finances.txt" "~/src/ledger/plan/TODO")))
 '(org-agenda-fontify-priorities t)
 '(org-agenda-include-diary t)
 '(org-agenda-ndays 1)
 '(org-agenda-persistent-filter t)
 '(org-agenda-prefix-format (quote ((agenda . "  %-11:c%?-12t% s") (timeline . "  % s") (todo . "  %-11:c") (tags . "  %-11:c"))))
 '(org-agenda-scheduled-leaders (quote ("" "S%d: ")))
 '(org-agenda-scheduled-relative-text "S%d: ")
 '(org-agenda-scheduled-text "")
 '(org-agenda-show-all-dates t)
 '(org-agenda-skip-deadline-if-done t)
 '(org-agenda-skip-scheduled-if-deadline-is-shown t)
 '(org-agenda-skip-scheduled-if-done t)
 '(org-agenda-skip-unavailable-files t)
 '(org-agenda-sorting-strategy (quote ((agenda habit-down time-up todo-state-up priority-down category-keep) (todo priority-down category-keep) (tags priority-down category-keep) (search category-keep))))
 '(org-agenda-start-on-weekday nil)
 '(org-agenda-tags-column -100)
 '(org-agenda-text-search-extra-files (quote (agenda-archives)))
 '(org-archive-location "TODO-archive::")
 '(org-archive-save-context-info (quote (time category itags)))
 '(org-attach-method (quote mv))
 '(org-capture-templates (quote (("t" "Task" entry (file+headline "~/Documents/Tasks/todo.txt" "Inbox") "* TODO %?
  SCHEDULED: %t
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :CREATED:  %U
  :END:" :prepend t))))
 '(org-clock-idle-time 10)
 '(org-clock-in-resume t)
 '(org-clock-in-switch-to-state "STARTED")
 '(org-clock-into-drawer "LOGBOOK")
 '(org-clock-modeline-total (quote current))
 '(org-clock-out-remove-zero-time-clocks t)
 '(org-clock-out-switch-to-state nil)
 '(org-clock-persist (quote history))
 '(org-completion-use-ido t)
 '(org-confirm-elisp-link-function nil)
 '(org-confirm-shell-link-function nil)
 '(org-cycle-global-at-bob t)
 '(org-deadline-warning-days 14)
 '(org-default-notes-file "~/Documents/Tasks/todo.txt")
 '(org-directory "~/Documents/Tasks/")
 '(org-enforce-todo-dependencies t)
 '(org-extend-today-until 8)
 '(org-fast-tag-selection-single-key (quote expert))
 '(org-footnote-section nil)
 '(org-habit-preceding-days 42)
 '(org-hide-leading-stars t)
 '(org-mobile-directory "~/Dropbox/MobileOrg")
 '(org-mobile-files (quote (org-agenda-files org-agenda-text-search-extra-files)))
 '(org-mobile-inbox-for-pull "~/Documents/Tasks/from-mobile.org")
 '(org-modules (quote (org-crypt org-gnus org-id org-habit org-mac-message org-bookmark org-checklist org-depend org-eval)))
 '(org-refile-targets (quote (("~/Documents/Tasks/todo.txt" :level . 1) ("~/Documents/Tasks/todo.txt" :todo . "PROJECT") ("~/Documents/Accounts/finances.txt" :level . 1) ("~/src/ledger/plan/TODO" :level . 1))))
 '(org-return-follows-link t)
 '(org-reverse-note-order t)
 '(org-tags-column -97)
 '(org-time-clocksum-use-fractional t)
 '(org-todo-keyword-faces (quote (("TODO" :foreground "medium blue" :weight bold) ("APPT" :foreground "medium blue" :weight bold) ("NOTE" :foreground "brown" :weight bold) ("STARTED" :foreground "dark orange" :weight bold) ("WAITING" :foreground "red" :weight bold) ("DELEGATED" :foreground "dark violet" :weight bold) ("DEFERRED" :foreground "dark blue" :weight bold) ("SOMEDAY" :foreground "dark blue" :weight bold) ("PROJECT" :foreground "#088e8e" :weight bold))))
 '(org-todo-repeat-to-state "TODO")
 '(org-use-property-inheritance (quote ("AREA")))
 '(org-use-speed-commands t)
 '(org2blog/wp-track-posts nil))
;;;_ + faces
(custom-set-faces
  ;; custom-set-faces was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 '(org-habit-alert-face ((((background light)) (:background "#f5f946"))))
 '(org-habit-alert-future-face ((((background light)) (:background "#fafca9"))))
 '(org-habit-clear-face ((((background light)) (:background "#8270f9"))))
 '(org-habit-clear-future-face ((((background light)) (:background "#d6e4fc"))))
 '(org-habit-overdue-face ((((background light)) (:background "#f9372d"))))
 '(org-habit-overdue-future-face ((((background light)) (:background "#fc9590"))))
 '(org-habit-ready-face ((((background light)) (:background "#4df946"))))
 '(org-habit-ready-future-face ((((background light)) (:background "#acfca9"))))
 '(org-scheduled ((((class color) (min-colors 88) (background light)) nil)))
 '(org-upcoming-deadline ((((class color) (min-colors 88) (background light)) (:foreground "Brown")))))
;;;_ + org-mode

(add-to-list 'auto-mode-alist '("\\.org$" . org-mode))

(load "org2blog-autoloads" t)

(setq org2blog/wp-blog-alist
      '(("thoughts"
         :url "http://johnwiegley.com/xmlrpc.php"
         :username "johnw"   
         :default-categories ("journal")
         :tags-as-categories nil)))

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

(defun plist-to-alist (sym)
  (let ((l (symbol-plist sym))
        props)
    (while l
      (unless (or (null (cadr l))
                  (and (stringp (cadr l))
                       (= 0 (length (cadr l)))))
        (push (cons (car l) (cadr l)) props))
      (setq l (cddr l)))
    props))

(defsubst trim-string (str)
  (replace-regexp-in-string "\\(\\`[[:space:]\n]*\\|[[:space:]\n]*\\'\\)" ""
                            str))

(defmacro resolve-log-entry ()
  `(when log-entry
     (put 'log-entry 'body
          (trim-string (get 'log-entry 'body)))
     (put 'item 'log
          (cons (plist-to-alist 'log-entry)
                (get 'item 'log)))
     (setq log-entry nil)
     (setplist 'log-entry '())))

(defun org-parse-entry ()
  (save-restriction
    (save-excursion
      (outline-back-to-heading)
      (narrow-to-region (point) (progn (outline-next-heading) (point)))
      (goto-char (point-min))

      (let (item log-entry)
        (setplist 'item '())
        (put 'item 'body "")
        (put 'item 'tags '())
        (put 'item 'log '())
        (put 'item 'properties '())
        (while (not (eobp))
          (cond
           ((looking-at "^\\(\\*+\\)\\( \\([A-Z][A-Z]+\\)\\)?\\( \\[#\\([A-C]\\)\\]\\)? \\(.+?\\)\\( +:\\(.+?\\):\\)?$")
            (put 'item 'depth (length (match-string-no-properties 1)))
            (if (match-string-no-properties 2)
                (put 'item 'state (match-string-no-properties 3)))
            (put 'item 'priority (or (match-string-no-properties 5) "B"))
            (put 'item 'title (match-string-no-properties 6))
            (if (match-string-no-properties 8)
                (put 'item 'tags
                     (split-string (match-string-no-properties 8) ":" t))))

           ((looking-at "^\\(\\s-*\\)- State \"\\([A-Z]+\\)\"\\s-*\\(from \"\\([A-Z]*\\)\"\\s-*\\)?\\[\\([^]]+\\)\\]\\(\\s-*\\\\\\\\\\)?\\s-*$")
            (resolve-log-entry)

            (put 'log-entry 'depth
                 (+ 1 (length (match-string-no-properties 1))))
            (put 'log-entry 'to (match-string-no-properties 2))
            (if (and (match-string-no-properties 3)
                     (match-string-no-properties 4))
                (put 'log-entry 'from (match-string-no-properties 4)))
            (put 'log-entry 'date (match-string-no-properties 5))
            (if (match-string-no-properties 6)
                (progn
                  (put 'log-entry 'body "")
                  (setq log-entry t))
              (put 'item 'log
                   (cons (plist-to-alist 'log-entry)
                         (get 'item 'log)))
              (setplist 'log-entry '())))

           ((looking-at "^\\(\\s-*\\)- Note taken on\\s-*\\[\\([^]]+\\)\\]\\(\\s-*\\\\\\\\\\)?\\s-*$")
            (resolve-log-entry)

            (put 'log-entry 'depth
                 (+ 1 (length (match-string-no-properties 1))))
            (put 'log-entry 'date (match-string-no-properties 2))
            (put 'log-entry 'note t)
            (if (match-string-no-properties 3)
                (progn
                  (put 'log-entry 'body "")
                  (setq log-entry t))
              (put 'item 'log
                   (cons (plist-to-alist 'log-entry)
                         (get 'item 'log)))
              (setplist 'log-entry '())))

           ((re-search-forward ":PROPERTIES:" (line-end-position) t)
            (while (not (re-search-forward ":END:" (line-end-position) t))
              (assert (not (eobp)))
              (if (looking-at "^\\s-*:\\([^:]+\\):\\s-*\\(.*\\)")
                  (let ((name (match-string-no-properties 1))
                        (data (match-string-no-properties 2)))
                    ;;(if (and (string= name "CREATED")
                    ;;         (string-match "\\[\\([^]\n]+\\)\\]" data))
                    ;;    (setq data (match-string 1 data)))
                    (unless (assoc name (get 'item 'properties))
                      (put 'item 'properties
                           (cons (cons name data)
                                 (get 'item 'properties))))))
              (forward-line)))

           ;; My old way of timestamping entries
           ((looking-at "^\\s-*\\[\\([^]]+\\)\\]\\s-*$")
            (unless (assoc "CREATED" (get 'item 'properties))
              (put 'item 'properties
                   (cons (cons "CREATED"
                               (concat "[" (match-string-no-properties 1) "]"))
                         (get 'item 'properties)))))

           (t
            (let (skip-line)
              (goto-char (line-beginning-position))
              (when (re-search-forward "SCHEDULED:\\s-*<\\([^>\n]+\\)>"
                                       (line-end-position) t)
                (put 'item 'scheduled (match-string-no-properties 1))
                (setq skip-line t))
              (goto-char (line-beginning-position))
              (when (re-search-forward "DEADLINE:\\s-*<\\([^>\n]+\\)>"
                                       (line-end-position) t)
                (put 'item 'deadline (match-string-no-properties 1))
                (setq skip-line t))
              (goto-char (line-beginning-position))
              (when (re-search-forward "CLOSED:\\s-*\\[\\([^]\n]+\\)\\]"
                                       (line-end-position) t)
                (put 'log-entry 'to (get 'item 'state))
                (put 'log-entry 'date (match-string-no-properties 1))
                (put 'item 'log
                     (cons (plist-to-alist 'log-entry)
                           (get 'item 'log)))
                (setplist 'log-entry '())
                (setq skip-line t))
              (goto-char (line-beginning-position))
              (when (re-search-forward "ARCHIVED:\\s-*<\\([^>\n]+\\)>"
                                       (line-end-position) t)
                (unless (assoc "ARCHIVE_TIME" (get 'item 'properties))
                  (put 'item 'properties
                       (cons (cons "ARCHIVE_TIME"
                                   (match-string-no-properties 1))
                             (get 'item 'properties))))
                (setq skip-line t))
              (if skip-line
                  (goto-char (line-end-position))))

            (assert (get (if log-entry 'log-entry 'item) 'depth))
            (dotimes (i (1+ (get (if log-entry 'log-entry 'item) 'depth)))
              (if (eq (char-after) ? )
                  (forward-char)
                (unless (looking-at "^\\s-*$")
                  (resolve-log-entry))))

            (put (if log-entry 'log-entry 'item) 'body
                 (concat (get (if log-entry 'log-entry 'item) 'body) "\n"
                         (buffer-substring-no-properties
                          (point) (line-end-position))))))
          (forward-line))

        (resolve-log-entry)

        (put 'item 'body (trim-string (get 'item 'body)))
        (plist-to-alist 'item)))))

(defun org-normalize-entry ()
  (interactive)
  (let ((entry (org-parse-entry)))
    (save-restriction
      (save-excursion
        (outline-back-to-heading)
        (narrow-to-region (point) (progn (outline-next-heading) (point)))
        (delete-region (point-min) (point-max))

        (insert (make-string (cdr (assq 'depth entry)) ?*) ? )
        (if (assq 'state entry)
            (insert (cdr (assq 'state entry)) ? ))
        (if (and (assq 'priority entry)
                 (not (string= "B" (cdr (assq 'priority entry)))))
            (insert "[#" (cdr (assq 'priority entry)) "] "))
        (insert (cdr (assq 'title entry)))
        (when (assq 'tags entry)
          (insert "  :" (mapconcat 'identity (cdr (assq 'tags entry)) ":") ":")
          (org-align-all-tags))
        (insert ?\n)

        (when (or (assq 'scheduled entry) (assq 'deadline entry))
          (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? ))
          (if (assq 'scheduled entry)
              (insert "SCHEDULED: <" (cdr (assq 'scheduled entry)) ">"))
          (when (assq 'deadline entry)
            (if (assq 'scheduled entry)
                (insert ? ))
            (insert "DEADLINE: <" (cdr (assq 'deadline entry)) ">"))
          (insert ?\n))
        
        (when (assq 'log entry)
          (dolist (log (reverse (cdr (assq 'log entry))))
            (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? ))
            (cond
             ((assq 'note log)
              (insert "- Note taken on [" (cdr (assq 'date log)) "]"))
             ((assq 'from log)
              (insert (format "- State %-12s from %-12s [%s]"
                              (concat "\"" (cdr (assq 'to log)) "\"")
                              (concat "\"" (cdr (assq 'from log)) "\"")
                              (cdr (assq 'date log)))))
             (t
              (insert (format "- State %-12s [%s]"
                              (concat "\"" (cdr (assq 'to log)) "\"")
                              (cdr (assq 'date log))))))
            (if (assq 'body log)
                (progn
                  (insert " \\\\\n")
                  (dolist (line (split-string (cdr (assq 'body log)) "\n"))
                    (insert (make-string (+ 3 (cdr (assq 'depth entry))) ? )
                            line ?\n)))
              (insert ?\n))))

        (when (assq 'body entry)
          (dolist (line (split-string (cdr (assq 'body entry)) "\n"))
            (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? )
                    line ?\n)))

        (when (assq 'properties entry)
          (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? )
                  ":PROPERTIES:\n")
          (dolist (prop (if nil
                            (sort (cdr (assq 'properties entry))
                                  (lambda (a b) (or (string= (car a) "ID")
                                               (string< (car a) (car b)))))
                          (reverse (cdr (assq 'properties entry)))))
            (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? )
                    (format "%-10s %s\n"
                            (concat ":" (car prop) ":") (cdr prop))))
          (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? )
                  ":END:\n"))))))

(defun org-normalize-all ()
  (interactive)
  (goto-char (point-min))
  (show-all)
  (untabify (point-min) (point-max))
  (while (re-search-forward "^\\*" nil t)
    (org-normalize-entry)
    (forward-line))
  (goto-char (point-min))
  (delete-trailing-whitespace)
  (save-buffer))

(defun org-my-message-open (message-id)
  (condition-case err
      (if (and nil (get-buffer "*Group*"))
          (gnus-goto-article
           (gnus-string-remove-all-properties (substring message-id 2)))
        (org-mac-message-open message-id))
    (error
     (org-mac-message-open message-id))))

(eval-after-load "org-mac-message"
  '(progn
     (let ((protocol (assoc "message" org-link-protocols)))
       (assert protocol)
       (setcar (cdr protocol) 'org-my-message-open))))

(defun org-my-filter-tasks ()
  (and (string-match "opportunities" buffer-file-name)
       (not (member "John" (org-get-tags-at)))
       (progn (outline-next-heading) (point))))


(defun make-ceg-bugzilla-bug (product component version priority severity)
  (interactive
   (let ((omk (get-text-property (point) 'org-marker)))
     (with-current-buffer (marker-buffer omk)
       (save-excursion
	 (goto-char omk)
	 (let ((products
		(list (list "ABC" (list "Admin" "User" "Other" "CSR")
			    (list "3.0"))
		      (list "Bizcard" (list "Catalog" "Content Section"
					    "Uploader" "Visual Aesthetics"
					    "webui" "Linux Port")
			    (list "unspecified"))
		      (list "Adagio" (list "DTSX" "PTS" "Satellite" "Zips"
					   "Core")
			    (list "unspecified"))
		      (list "IT" (list "install" "network" "repair" "misc")
			    (list "unspecified"))
		      (list "EVAprint" (list "misc")
			    (list "1.0"))))
	       (priorities (list "P1" "P2" "P3" "P4" "P5"))
	       (severities (list "blocker" "critical" "major"
				 "normal" "minor" "trivial" "enhancement"))
	       (product (org-get-category)))
	   (list product
		 (let ((components (nth 1 (assoc product products))))
		   (if (= 1 (length components))
		       (car components)
		     (ido-completing-read "Component: " components
					  nil t nil nil (car (last components)))))
		 (let ((versions (nth 2 (assoc product products))))
		   (if (= 1 (length versions))
		       (car versions)
		     (ido-completing-read "Version: " versions
					  nil t nil nil (car (last versions)))))
		 (let ((orgpri (nth 3 (org-heading-components))))
		   (if (and orgpri (= ?A orgpri))
		       "P1"
		     (ido-completing-read "Priority: " priorities
					  nil t nil nil "P3")))
		 (ido-completing-read "Severity: " severities nil t nil nil
				      "normal") ))))))
  (if (string= product "Bizcard")
      (setq product "BizCard"))
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
		       "~/bin/bugzilla-submit https://portal/bugzilla/"
		       tmpbuf)))
		  (goto-char (point-min))
		  (re-search-forward "Bug \\([0-9]+\\) posted.")
		  (setq bug (match-string 1))))))
	  (save-excursion
	    (org-back-to-heading t)
	    (re-search-forward "\\(TODO\\|DEFERRED\\|STARTED\\|WAITING\\|DELEGATED\\) \\(\\[#[ABC]\\] \\)?")
	    (insert (format "[[cegbug:%s][#%s]] " bug bug)))))))
  (org-agenda-redo))

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

(defun make-boostpro-jira-bug (product component version priority)
  (interactive
   (let ((omk (get-text-property (point) 'org-marker)))
     (with-current-buffer (marker-buffer omk)
       (save-excursion
	 (goto-char omk)
	 (let ((products
		(list
                 (list "Admin" (list "none") (list "none"))
                 (list "IT" (list "VCS" "none") (list "none"))
                 (list "Embarcadero" (list "admin") (list "none"))))
	       (priorities (list "Blocker" "Critical"
				 "Major" "Minor" "Trivial"))
               (product (or (org-get-category) "BoostPro")))
	   (list product
		 (let ((components (nth 1 (assoc product products))))
		   (if (= 1 (length components))
		       (car components)
		     (ido-completing-read "Component: " components
					  nil t nil nil (car (last components)))))
		 (let ((versions (nth 2 (assoc product products))))
		   (if (= 1 (length versions))
		       (car versions)
		     (ido-completing-read "Version: " versions
					  nil t nil nil (car (last versions)))))
		 (let ((orgpri (nth 3 (org-heading-components))))
		   (if (and orgpri (= ?A orgpri))
		       "Blocker"
		     (ido-completing-read "Priority: " priorities
					  nil t nil nil "Minor")))))))))
  (let ((omk (get-text-property (point) 'org-marker)))
    (with-current-buffer (marker-buffer omk)
      (save-excursion
	(goto-char omk)
	(let ((heading (nth 4 (org-heading-components)))
	      (contents (buffer-substring-no-properties
			 (org-entry-beginning-position)
			 (org-entry-end-position)))
	      description bug proj)
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
	    (setq description (if (eobp) "No description." (buffer-string))))
          (let ((buf (current-buffer)))
            (with-temp-buffer
              (let ((tmpbuf (current-buffer)))
                (if nil
                    (insert "Issue BP-999 created.")
                  (with-current-buffer buf
                    (shell-command-on-region
                     (point-min) (point-max)
                     (format
                      (concat "~/.jcli/jira.sh -a createIssue "
                              "--project %s "
                              (if (not (string= component "none"))
                                  (concat "--components " component) "")
                              (if (not (string= version "none"))
                                  (concat "--version " version) "")
                              " --type %s "
                              "--summary '%s' "
                              "--reporter %s "
                              "--assignee %s "
                              (if priority (concat "--priority " priority) "")
                              " --description '%s'")
                      product (ido-completing-read
                               "Type: "
                               '("Bug" "New Feature" "Task" "Improvement")
                               nil t nil nil "Task") heading "johnw" "johnw"
                      description)
                     tmpbuf)))
                (goto-char (point-min))
                (re-search-forward "Issue \\([A-Za-z0-9]+\\)-\\([0-9]+\\) created.")
                (setq proj (match-string 1)
                      bug (match-string 2)))))
	  (save-excursion
	    (org-back-to-heading t)
	    (re-search-forward "\\(TODO\\|DEFERRED\\|STARTED\\|WAITING\\|DELEGATED\\) \\(\\[#[ABC]\\] \\)?")
	    (insert (format "[[j%s:%s][#%s]] " (downcase proj) bug bug)))))))
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
     ((string= "BoostPro" (car path))
      (call-interactively #'make-boostpro-jira-bug))
     ((string= "CEG" (car path))
      (call-interactively #'make-ceg-bugzilla-bug))
     (t
      (error "Cannot make bug, unknown category")))))

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
	((string= tag "home")
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

;;(defun org-indent-empty-items (arg)
;;  (when (eq arg 'empty)
;;    (goto-char (line-end-position))
;;    (cond
;;     ((org-at-item-p) (org-indent-item 1))
;;     ((org-on-heading-p)
;;      (if (equal this-command last-command)
;;	  (condition-case nil
;;	      (org-promote-subtree)
;;	    (error
;;	     (save-excursion
;;	       (goto-char (point-at-bol))
;;	       (and (looking-at "\\*+") (replace-match ""))
;;	       (org-insert-heading)
;;	       (org-demote-subtree))))
;;	(org-demote-subtree))))))
;;
;;(add-hook 'org-pre-cycle-hook 'org-indent-empty-items)

(defun my-org-convert-incoming-items ()
  (interactive)
  (with-current-buffer (find-file-noselect org-mobile-inbox-for-pull)
    (goto-char (point-min))
    (while (re-search-forward "^\\* " nil t)
      (goto-char (match-beginning 0))
      (insert ?*)
      (forward-char 2)
      (insert "TODO ")
      (goto-char (line-beginning-position))
      (forward-line)
      (insert
       (format
	"   SCHEDULED: %s
   :PROPERTIES:
   :ID:       %s   :CREATED:  %s
   :END:
   "
        (format-time-string (org-time-stamp-format))
        (shell-command-to-string "uuidgen")
        (format-time-string (org-time-stamp-format t t)))))
    (let ((tasks (buffer-string)))
      (erase-buffer)
      (save-buffer)
      (kill-buffer (current-buffer))
      (with-current-buffer (find-file-noselect "~/Documents/Tasks/todo.txt")
	(save-excursion
	  (goto-char (point-min))
          (re-search-forward "^\\* Inbox$")
          (re-search-forward "^  :END:")
          (forward-line)
          (goto-char (line-beginning-position))
          (insert tasks))))))

(add-hook 'org-mobile-post-pull-hook 'my-org-convert-incoming-items)

(defun org-insert-bug (project bug)
  (interactive
   (list (ido-completing-read "Project: " '("redmine" "bug" "cegbug"))
         (read-number "Bug: ")))
  (insert (format "[[%s:%s][#%s]]" project bug bug)))

(defun org-cmp-bugs (a b)
  (let* ((bug-a (and (string-match "#\\([0-9]+\\)" a)
		     (match-string 1 a)))
	 (bug-b (and (string-match "#\\([0-9]+\\)" b)
		     (match-string 1 b)))
	 (cmp (and bug-a bug-b
		   (- (string-to-number bug-b)
		      (string-to-number bug-a)))))
    (cond ((null cmp) nil)
	  ((< cmp 0) -1)
	  ((> cmp 0) 1)
	  ((= cmp 0) nil))))

(defun org-my-state-after-clock-out (state)
  (if (string= state "STARTED")
      "TODO"
    state))

(defun replace-named-dates ()
  (interactive)
  (while (re-search-forward
	  "-\\(Jan\\|Feb\\|Mar\\|Apr\\|May\\|Jun\\|Jul\\|Aug\\|Sep\\|Oct\\|Nov\\|Dec\\)-"
	  nil t)
    (let ((mon (match-string 1)))
      (replace-match
       (format "/%s/"
	       (cond ((equal mon "Jan") "01")
		     ((equal mon "Feb") "02")
		     ((equal mon "Mar") "03")
		     ((equal mon "Apr") "04")
		     ((equal mon "May") "05")
		     ((equal mon "Jun") "06")
		     ((equal mon "Jul") "07")
		     ((equal mon "Aug") "08")
		     ((equal mon "Sep") "09")
		     ((equal mon "Oct") "10")
		     ((equal mon "Nov") "11")
		     ((equal mon "Dec") "12")))))))

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

(defun jump-to-ledger-journal ()
  (interactive)
  (find-file-other-window "~/Documents/Accounts/ledger.dat")
  (goto-char (point-max))
  (insert (format-time-string "%Y/%m/%d ")))

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

(defun org-get-message-link ()
  (if (get-buffer "*Group*")
      (let (message-id subject)
        (with-current-buffer gnus-original-article-buffer
          (nnheader-narrow-to-headers)
          (setq message-id (substring (message-fetch-field "message-id") 1 -1)
                subject (message-fetch-field "subject")))
        (org-make-link-string (concat "message://" message-id) subject))
    (org-get-apple-message-link)))

(defun org-get-message-sender ()
  (do-applescript "tell application \"Mail\"
        set theMessages to selection
        sender of beginning of theMessages
end tell"))

(defun org-get-url-link ()
  (let ((subject (do-applescript "tell application \"Safari\"
        name of document of front window
end tell"))
        (url (do-applescript "tell application \"Safari\"
        URL of document of front window
end tell")))
    (org-make-link-string url subject)))

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

(defun org-insert-message-link ()
  (interactive)
  (insert (org-get-message-link)))

(defun org-insert-apple-message-link ()
  (interactive)
  (insert (org-get-apple-message-link)))

(defun org-insert-url-link ()
  (interactive)
  (insert (org-get-url-link)))

(defun org-insert-file-link ()
  (interactive)
  (insert (org-get-file-link)))

(defun org-set-dtp-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Document" (org-get-dtp-link)))

(defun org-set-message-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Message" (org-get-message-link)))

(defun org-set-message-sender ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Submitter" (org-get-message-sender)))

(defun org-set-url-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "URL" (org-get-url-link)))

(defun org-set-file-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "File" (org-get-file-link)))

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

(defun org-make-regress-test ()
  (interactive)
  (save-excursion
    (outline-previous-visible-heading 1)
    (let ((begin (point))
	  (end (save-excursion
		 (outline-next-heading)
		 (point)))
	  (input "\n") (data "") (output ""))
      (goto-char begin)
      (when (re-search-forward ":SCRIPT:\n" end t)
	(goto-char (match-end 0))
	(let ((input-beg (point)))
	  (re-search-forward "[ 	]+:END:")
	  (setq input (buffer-substring input-beg (match-beginning 0)))))
      (goto-char begin)
      (when (search-forward ":\\(DATA\\|SOURCE\\):\n" end t)
	(goto-char (match-end 0))
	(let ((data-beg (point)))
	  (re-search-forward "[ 	]+:END:")
	  (setq data (buffer-substring data-beg (match-beginning 0)))))
      (goto-char begin)
      (when (search-forward ":OUTPUT:\n" end t)
	(goto-char (match-end 0))
	(let ((output-beg (point)))
	  (re-search-forward "[ 	]+:END:")
	  (setq output (buffer-substring output-beg (match-beginning 0)))))
      (goto-char begin)
      (when (re-search-forward ":ID:\\s-+\\([^-]+\\)" end t)
	(find-file (expand-file-name (concat (match-string 1) ".test")
				     "~/src/ledger/test/regress/"))
	(insert input "<<<\n" data ">>>1\n" output ">>>2\n=== 0\n")
	(pop-to-buffer (current-buffer))
	(goto-char (point-min))))))

(fset 'sort-todo-categories
   [?\C-u ?\C-s ?^ ?\\ ?* ?\S-  ?\C-a ?^ ?a ?^ ?p ?^ ?o ?\C-e])

(fset 'sort-subcategories
   [?\C-u ?\C-s ?\\ ?* ?\\ ?* ?\S-  ?P ?R ?O ?J ?E ?C ?T ?\C-a ?^ ?a ?^ ?p ?^ ?o ?\C-e])

(fset 'match-bug-list
   [?\C-s ?= ?\C-b ?\C-f ?\C-  ?\C-e ?\M-w ?\C-a ?\C-n C-return ?\M-< ?\C-s ?\M-y C-return])

(fset 'match-up-bugs
   [?\C-s ?= ?\C-  ?\C-e ?\M-w ?\C-a ?\C-n C-return ?\M-< ?\C-s ?# ?\M-y C-return])

(fset 'move-created-dates
   [?\C-u ?\C-s ?^ ?  ?+ ?\\ ?\[ ?2 ?\C-b ?\C-x ?n ?s ?\C-b ?\C-\M-k ?\C-x ?\C-o ?\C-r ?: ?P ?R ?O ?P ?\C-b ?\C-c ?\C-x ?p ?C ?R ?E ?A ?T ?E ?D return ?\C-y return ?\C-x ?n ?w ?\C-x ?\C-o ?\C-a ?\C-n ?\C-x ?\C-o])

(defun jump-to-org-agenda ()
  (interactive)
  (let ((buf (get-buffer "*Org Agenda*"))
	wind)
    (if buf
	(if (setq wind (get-buffer-window buf))
	    (select-window wind)
	  (if (called-interactively-p)
	      (progn
		(select-window (display-buffer buf t t))
		(org-fit-window-to-buffer)
		;; (org-agenda-redo)
		)
	    (with-selected-window (display-buffer buf)
	      (org-fit-window-to-buffer)
	      ;; (org-agenda-redo)
	      )))
      (call-interactively 'org-agenda-list)))
  ;;(let ((buf (get-buffer "*Calendar*")))
  ;;  (unless (get-buffer-window buf)
  ;;    (org-agenda-goto-calendar)))
  )

(run-with-idle-timer 300 t 'jump-to-org-agenda)

(defadvice org-add-log-note (after narrow-fill-column activate)
  "Subtract 5 from the fill-column."
  (setq fill-column (- fill-column 5)))

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
                   "\\[.*? - Bug #\\([0-9]+\\)\\] (New)" "[[redmine:\\1][#\\1]]"
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

(define-key global-map [(meta ?m)] 'org-smart-capture)
(define-key global-map [(meta ?z)] 'org-inline-note)
(define-key global-map [(meta ?C)] 'jump-to-org-agenda)

(define-key mode-specific-map [?a] 'org-agenda)
(define-key mode-specific-map [(meta ?w)] 'org-store-link)
(define-key mode-specific-map [(shift ?w)] 'org-kill-entry)

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

(define-key mode-specific-map [?x ?L] 'org-set-dtp-link)
(define-key mode-specific-map [?x ?M] 'org-set-message-link)
(define-key mode-specific-map [?x ?Y] 'org-set-message-sender)
(define-key mode-specific-map [?x ?U] 'org-set-url-link)
(define-key mode-specific-map [?x ?F] 'org-set-file-link)
(define-key mode-specific-map [?x ?C] 'cvs-examine)
(define-key mode-specific-map [?x ?S] 'svn-status)
(define-key mode-specific-map [?x ?b] 'org-insert-bug)
(define-key mode-specific-map [?x ?l] 'org-insert-dtp-link)
(define-key mode-specific-map [?x ?m] 'org-insert-message-link)
(define-key mode-specific-map [?x ?a] 'org-insert-apple-message-link)
(define-key mode-specific-map [?x ?u] 'org-insert-url-link)
(define-key mode-specific-map [?x ?f] 'org-insert-file-link)

(defun org-trac-ticket-open ()
  (interactive)
  (browse-url (concat "http://trac.newartisans.com/ledger/ticket/"
		      (org-entry-get (point) "Ticket"))))

(define-key mode-specific-map [?x ?T] 'org-trac-ticket-open)

(define-key mode-specific-map [(shift ?y)] 'org-yank-entry)

;;;_ + org-mode

(eval-after-load "org"
  '(progn
     (org-defkey org-mode-map [(control meta return)]
                 'org-insert-heading-after-current)
     (org-defkey org-mode-map [(control return)] 'other-window)
     (define-key org-mode-map [return] 'org-return-indent)

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
		 (define-key yas/keymap [tab] 'yas/next-field)))))

(eval-after-load "org-agenda"
  '(progn
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

       (define-key org-todo-state-map "z" #'make-bug-link))))

;;;_* startup

(add-hook 'after-init-hook
	  (function
	   (lambda ()
	     (org-agenda-list)
	     (org-resolve-clocks)
             (remove-hook 'kill-emacs-hook
                          'org-babel-remove-temporary-directory))))

;; .org.el ends here
