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
 '(org-use-tag-inheritance nil)
 '(org-use-speed-commands t)
 '(org-todo-repeat-to-state "TODO")
 '(org-todo-keywords (quote ((sequence "TODO" "APPT" "|" "DONE" "NOTE"))))
 '(org-todo-keyword-faces (quote (("TODO" :foreground "medium blue" :weight bold) ("APPT" :foreground "medium blue" :weight bold) ("NOTE" :foreground "brown" :weight bold) ("STARTED" :foreground "dark orange" :weight bold) ("WAITING" :foreground "red" :weight bold) ("DELEGATED" :foreground "dark violet" :weight bold) ("DEFERRED" :foreground "dark blue" :weight bold) ("SOMEDAY" :foreground "dark blue" :weight bold))))
 '(org-time-clocksum-use-fractional t)
 '(org-tags-column -97)
 '(org-tag-alist (quote ((#("NASIM" 0 5 (face nil)) . 110) (#("WORK" 0 4 (face nil)) . 119))))
 '(org-stuck-projects (quote ("+LEVEL=1/-DONE" ("TODO" "STARTED" "NEXT" "NEXTACTION") nil "\\(Appointments\\|Notes\\|Anniversaries\\)")))
 '(org-speed-commands-user nil)
 '(org-reverse-note-order t)
 '(org-return-follows-link t)
 '(org-remember-templates (quote (("Task" 116 "* TODO %?
  SCHEDULED: %t
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :END:
  %U" nil "Inbox" nil))))
 '(org-remember-store-without-prompt t)
 '(org-refile-targets (quote (("~/Dropbox/todo.txt" :level . 1) ("~/Dropbox/todo.txt" :todo . "Project") ("~/Dropbox/Accounts/finances.txt" :level . 1) ("~/src/ledger/plan/TODO" :level . 1))))
 '(org-modules (quote (org-crypt org-gnus org-id org-habit org-mac-message org-bookmark org-checklist org-depend org-eval)))
 '(org-mobile-inbox-for-pull "~/Dropbox/from-mobile.org")
 '(org-mobile-files (quote (org-agenda-files org-agenda-text-search-extra-files)))
 '(org-mobile-directory "~/Dropbox/MobileOrg")
 '(org-hide-leading-stars t)
 '(org-habit-preceding-days 42)
 '(org-footnote-section nil)
 '(org-fast-tag-selection-single-key (quote expert))
 '(org-extend-today-until 8)
 '(org-enforce-todo-dependencies t)
 '(org-directory "~/Dropbox/")
 '(org-default-notes-file "~/Dropbox/todo.txt")
 '(org-deadline-warning-days 14)
 '(org-cycle-global-at-bob t)
 '(org-confirm-shell-link-function nil)
 '(org-confirm-elisp-link-function nil)
 '(org-completion-use-ido t)
 '(org-clock-persist (quote history))
 '(org-clock-out-switch-to-state nil)
 '(org-clock-out-remove-zero-time-clocks t)
 '(org-clock-modeline-total (quote current))
 '(org-clock-into-drawer "LOGBOOK")
 '(org-clock-in-switch-to-state "STARTED")
 '(org-clock-in-resume t)
 '(org-clock-idle-time 10)
 '(org-capture-templates (quote (("t" "Task" entry (file+headline "~/Dropbox/todo.txt" "Inbox") "* TODO %?
  SCHEDULED: %t
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :END:
  %U" :prepend t))))
 '(org-attach-method (quote mv))
 '(org-archive-save-context-info (quote (time category itags)))
 '(org-archive-location "TODO-archive::")
 '(org-agenda-text-search-extra-files (quote (agenda-archives)))
 '(org-agenda-tags-column -100)
 '(org-agenda-start-on-weekday nil)
 '(org-agenda-sorting-strategy (quote ((agenda habit-down time-up todo-state-up priority-down category-keep) (todo priority-down category-keep) (tags priority-down category-keep) (search category-keep))))
 '(org-agenda-skip-unavailable-files t)
 '(org-agenda-skip-scheduled-if-done t)
 '(org-agenda-skip-scheduled-if-deadline-is-shown t)
 '(org-agenda-skip-deadline-if-done t)
 '(org-agenda-show-all-dates t)
 '(org-agenda-scheduled-text "")
 '(org-agenda-scheduled-relative-text "S%d: ")
 '(org-agenda-scheduled-leaders (quote ("" "S%d: ")))
 '(org-agenda-prefix-format (quote ((agenda . "  %-11:c%?-12t% s") (timeline . "  % s") (todo . "  %-11:c") (tags . "  %-11:c"))))
 '(org-agenda-persistent-filter t)
 '(org-agenda-ndays 1)
 '(org-agenda-include-diary t)
 '(org-agenda-fontify-priorities t)
 '(org-agenda-files (quote ("~/Dropbox/todo.txt" "~/Dropbox/Accounts/finances.txt" "~/Dropbox/BoostPro/Documents/SEO.org" "~/src/ledger/plan/TODO")))
 '(org-agenda-default-appointment-duration 60)
 '(org-agenda-deadline-text "D: ")
 '(org-agenda-deadline-relative-text "D%d: ")
 '(org-agenda-deadline-leaders (quote ("D: " "D%d: ")))
 '(org-agenda-custom-commands (quote (("E" "Errands (next 3 days)" tags "Errand&TODO<>\"DONE\"&TODO<>\"CANCELED\"&STYLE<>\"habit\"&SCHEDULED<\"<+3d>\"" ((org-agenda-overriding-header "Errands (next 3 days)"))) ("A" "Priority #A tasks" agenda "" ((org-agenda-ndays 1) (org-agenda-overriding-header "Today's priority #A tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote notregexp) "\\=.*\\[#A\\]"))))) ("B" "Priority #A and #B tasks" agenda "" ((org-agenda-ndays 1) (org-agenda-overriding-header "Today's priority #A and #B tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\=.*\\[#C\\]"))))) ("w" "Waiting/delegated tasks" tags "TODO=\"WAITING\"|TODO=\"DELEGATED\"" ((org-agenda-overriding-header "Waiting/delegated tasks:") (org-agenda-sorting-strategy (quote (todo-state-up priority-down category-up))))) ("u" "Unscheduled tasks" tags "TODO<>\"\"&TODO<>\"DONE\"&TODO<>\"CANCELED\"&TODO<>\"NOTE\"" ((org-agenda-files (quote ("~/Dropbox/todo.txt" "~/Dropbox/Accounts/finances.txt"))) (org-agenda-overriding-header "Unscheduled tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote scheduled) (quote deadline) (quote timestamp) (quote regexp) "\\* \\(DEFERRED\\|SOMEDAY\\)"))) (org-agenda-sorting-strategy (quote (priority-down))))) ("U" "Deferred tasks" tags "TODO=\"DEFERRED\"&CATEGORY<>{CEG\\|ABC\\|Bizcard\\|Adagio\\|EVAprint\\|\\<IT\\>}" ((org-agenda-overriding-header "Deferred tasks:"))) ("S" "Someday tasks" tags "TODO=\"SOMEDAY\"&CATEGORY<>{CEG\\|ABC\\|Bizcard\\|Adagio\\|EVAprint\\|\\<IT\\>}" ((org-agenda-overriding-header "Someday tasks:"))) ("G" "Ledger tasks (all)" tags-todo "TODO<>{SOMEDAY}" ((org-agenda-files (quote ("~/src/ledger/plan/TODO"))) (org-agenda-overriding-header "Ledger tasks:") (org-agenda-sorting-strategy (quote (todo-state-up priority-down category-up))))) ("l" "Ledger tasks" tags-todo "TODO<>{SOMEDAY\\|DEFERRED}" ((org-agenda-files (quote ("~/src/ledger/plan/TODO"))) (org-agenda-overriding-header "Ledger tasks:") (org-agenda-sorting-strategy (quote (todo-state-up priority-down category-up))) (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\=.*\\[#C\\]"))))) ("L" "Ledger tasks not in Bugzilla" alltodo "" ((org-agenda-files (quote ("~/src/ledger/plan/TODO"))) (org-agenda-overriding-header "Ledger tasks:") (org-agenda-sorting-strategy (quote (todo-state-up priority-down category-up))) (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\(bug:\\)"))))) ("r" "Uncategorized items" tags "CATEGORY=\"Inbox\"&LEVEL=2" ((org-agenda-overriding-header "Uncategorized items"))) ("W" "Unscheduled work tasks" tags "CATEGORY={CEG\\|ABC\\|Bizcard\\|Adagio\\|IT\\|EVAprint}&CATEGORY<>\"Website\"&TODO<>\"DONE\"&TODO<>\"CANCELED\"&TODO<>\"NOTE\"&TODO<>\"\"&LEVEL>1" ((org-agenda-overriding-header "Unscheduled work tasks") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote scheduled) (quote deadline)))) (org-agenda-sorting-strategy (quote (todo-state-up priority-down))))) ("z" "CEG tasks not in Bugzilla" tags "CATEGORY={CEG\\|ABC\\|Bizcard\\|Adagio\\|IT\\|EVAprint}&CATEGORY<>{Website\\|Admin}&TODO<>\"DONE\"&TODO<>\"CANCELED\"&TODO<>\"NOTE\"&TODO<>\"\"&LEVEL>1&SCOPE<>\"local\"" ((org-agenda-overriding-header "CEG tasks not in Bugzilla") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\(cegbug:\\)"))))) ("Z" "CEG tasks in Bugzilla" tags "CATEGORY={CEG\\|ABC\\|Bizcard\\|Adagio\\|IT\\|EVAprint}&TODO<>\"DONE\"&TODO<>\"CANCELED\"&TODO<>\"DELEGATED\"&TODO<>\"NOTE\"&LEVEL>1" ((org-agenda-overriding-header "CEG tasks in Bugzilla") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote notregexp) "cegbug:"))) (org-agenda-sorting-strategy (quote (todo-state-up category-down priority-down user-defined-up))))) ("y" "CEG tasks not in Bugzilla" tags "CATEGORY={CEG\\|ABC\\|Bizcard\\|Adagio\\|CEG IT\\|EVAprint}&CATEGORY<>{Website\\|Admin}&TODO<>\"DONE\"&TODO<>\"CANCELED\"&TODO<>\"NOTE\"&TODO<>\"\"&LEVEL>1&SCOPE<>\"local\"" ((org-agenda-overriding-header "CEG tasks not in Bugzilla") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\(cegbug:\\)"))))) ("Y" "CEG tasks in Bugzilla" tags "CATEGORY={CEG\\|ABC\\|Bizcard\\|Adagio\\|CEG IT\\|EVAprint}&TODO<>\"DONE\"&TODO<>\"CANCELED\"&TODO<>\"DELEGATED\"&TODO<>\"NOTE\"&LEVEL>1" ((org-agenda-overriding-header "CEG tasks in Bugzilla") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote notregexp) "cegbug:"))) (org-agenda-sorting-strategy (quote (todo-state-up category-down priority-down user-defined-up))))))))
 '(org-agenda-cmp-user-defined (quote org-cmp-ceg-bugs))
 '(org-agenda-auto-exclude-function (quote org-my-auto-exclude-function))
 '(org-M-RET-may-split-line (quote ((headline) (default . t))))
 '(calendar-mark-holidays-flag t)
 '(calendar-longitude -74.287672)
 '(calendar-latitude 40.845112))
(custom-set-faces
 '(org-upcoming-deadline ((((class color) (min-colors 88) (background light)) (:foreground "Brown"))))
 '(org-scheduled ((((class color) (min-colors 88) (background light)) nil)))
 '(org-habit-ready-future-face ((((background light)) (:background "#acfca9"))))
 '(org-habit-ready-face ((((background light)) (:background "#4df946"))))
 '(org-habit-overdue-future-face ((((background light)) (:background "#fc9590"))))
 '(org-habit-overdue-face ((((background light)) (:background "#f9372d"))))
 '(org-habit-clear-future-face ((((background light)) (:background "#d6e4fc"))))
 '(org-habit-clear-face ((((background light)) (:background "#8270f9"))))
 '(org-habit-alert-future-face ((((background light)) (:background "#fafca9"))))
 '(org-habit-alert-face ((((background light)) (:background "#f5f946")))))

;;;_ + faces

(custom-set-faces
 '(org-upcoming-deadline ((((class color) (min-colors 88) (background light)) (:foreground "Brown"))))
 '(org-scheduled ((((class color) (min-colors 88) (background light)) nil)))
 '(org-habit-ready-future-face ((((background light)) (:background "#acfca9"))))
 '(org-habit-ready-face ((((background light)) (:background "#4df946"))))
 '(org-habit-overdue-future-face ((((background light)) (:background "#fc9590"))))
 '(org-habit-overdue-face ((((background light)) (:background "#f9372d"))))
 '(org-habit-clear-future-face ((((background light)) (:background "#d6e4fc"))))
 '(org-habit-clear-face ((((background light)) (:background "#8270f9"))))
 '(org-habit-alert-future-face ((((background light)) (:background "#fafca9"))))
 '(org-habit-alert-face ((((background light)) (:background "#f5f946")))))

;;;_ + org-mode

(add-to-list 'auto-mode-alist '("\\.org$" . org-mode))

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
	       (version "3.0.0-20100615"))
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
  (with-current-buffer (find-file-noselect "~/Dropbox/todo.txt")
    (org-mobile-push)))

;; (run-with-idle-timer 600 t 'my-org-push-mobile)

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

(defun my-org-mobile-post-push-hook ()
  (shell-command "ssh root@192.168.9.144 chown admin:admin '/c/docs/'")
  (message "Fixed permissions on https://johnw.homeunix.net/docs"))

(add-hook 'org-mobile-post-push-hook 'my-org-mobile-post-push-hook)

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
   :ID:       %s   :END:
   "
	(with-temp-buffer (org-insert-time-stamp (current-time)))
	(shell-command-to-string "uuidgen"))))
    (let ((tasks (buffer-string)))
      (erase-buffer)
      (save-buffer)
      (kill-buffer (current-buffer))
      (with-current-buffer (find-file-noselect "~/Dropbox/todo.txt")
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
   (list (ido-completing-read "Project: "
                              '("redmine" "bug" "cegbug"))
         (read-number "Bug: ")))
  (insert (format "[[%s:%s][#%s]]" project bug bug)))

(defun org-cmp-ceg-bugs (a b)
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

(defconst org-my-ts-regexp "[[<]\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} [^]>\r\n]*?\\)[]>]"
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
  :ID:       %(shell-command-to-string \"uuidgen\")  :END:
  %U" "~/Dropbox/todo.txt" "Inbox"))))
	(org-remember))))
  (set-fill-column 72))

(defun jump-to-ledger-journal ()
  (interactive)
  (find-file-other-window "~/Dropbox/Accounts/ledger.dat")
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
   :END:
   " (shell-command-to-string "uuidgen")))
    (org-insert-time-stamp nil t 'inactive)
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
  :END:
  %U" "~/Dropbox/todo.txt" "Inbox"))))
      (call-interactively 'org-remember))))

(defun org-get-message-link ()
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

(defun org-insert-url-link ()
  (interactive)
  (insert (org-get-url-link)))

(defun org-insert-file-link ()
  (interactive)
  (insert (org-get-file-link)))

(defun org-set-dtp-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Document" (org-get-dtp-link)D))

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
   [?\C-u ?\C-s ?^ ?\\ ?* ?\\ ?* ?\S-  ?P ?r ?o ?j ?e ?c ?t ?\C-a ?^ ?a ?^ ?p ?^ ?o ?\C-e])

(fset 'match-bug-list
   [?\C-s ?= ?\C-b ?\C-f ?\C-  ?\C-e ?\M-w ?\C-a ?\C-n C-return ?\M-< ?\C-s ?\M-y C-return])

(fset 'match-up-bugs
   [?\C-s ?= ?\C-  ?\C-e ?\M-w ?\C-a ?\C-n C-return ?\M-< ?\C-s ?# ?\M-y C-return])

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

(define-key global-map [(meta ?m)]
  (lambda () (interactive) (org-capture nil "t")))
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
