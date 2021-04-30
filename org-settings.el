(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(cfw:read-date-command
   (lambda nil
     (interactive)
     (let
         ((xs
           (decode-time
            (org-time-string-to-time
             (org-read-date)))))
       (list
        (nth 4 xs)
        (nth 3 xs)
        (nth 5 xs)))))
 '(deft-directory "~/doc/notes")
 '(deft-text-mode 'org-mode)
 '(deft-use-filename-as-title t)
 '(jobhours-files
   '("~/dfinity/docs/dfinity.org" "~/dfinity/docs/archive/dfinity.org"))
 '(org-M-RET-may-split-line '((headline) (default . t)))
 '(org-adapt-indentation nil)
 '(org-agenda-auto-exclude-function 'org-my-auto-exclude-function)
 '(org-agenda-cmp-user-defined 'org-compare-todo-age)
 '(org-agenda-custom-commands
   '(("h" "Current Hotlist" alltodo ""
      ((org-agenda-overriding-header "Current Hotlist")
       (org-agenda-skip-function #'my-org-agenda-skip-all-siblings-but-first-hot)))
     ("H" "Hot Projects" tags "HOT&TODO=\"PROJECT\""
      ((org-agenda-overriding-header "Hot Projects")))
     ("T" "Non-Hot Projects" tags "-HOT&TODO=\"PROJECT\""
      ((org-agenda-overriding-header "Non-Hot Projects")))
     ("n" "Project Next Actions" alltodo ""
      ((org-agenda-overriding-header "Project Next Actions")
       (org-agenda-skip-function #'my-org-agenda-skip-all-siblings-but-first)))
     ("P" "All Projects" tags "TODO=\"PROJECT\""
      ((org-agenda-overriding-header "All Projects")))
     ("A" "Priority #A tasks" agenda ""
      ((org-agenda-ndays 1)
       (org-agenda-overriding-header "Today's priority #A tasks: ")
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'notregexp "\\=.*\\[#A\\]"))))
     ("b" "Priority #A and #B tasks" agenda ""
      ((org-agenda-ndays 1)
       (org-agenda-overriding-header "Today's priority #A and #B tasks: ")
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'regexp "\\=.*\\[#C\\]"))))
     ("r" "Uncategorized items" tags "CATEGORY=\"Inbox\"&LEVEL=2"
      ((org-agenda-overriding-header "Uncategorized items")))
     ("W" "Waiting/delegated tasks" tags "W-TODO=\"DONE\"|TODO={WAITING\\|DELEGATED}"
      ((org-agenda-overriding-header "Waiting/delegated tasks:")
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'scheduled))
       (org-agenda-sorting-strategy
        '(todo-state-up priority-down category-up))))
     ("D" "Deadlined tasks" tags "TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}"
      ((org-agenda-overriding-header "Deadlined tasks: ")
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'notdeadline))
       (org-agenda-sorting-strategy
        '(category-up))))
     ("S" "Scheduled tasks" tags "TODO<>\"\"&TODO<>{APPT\\|DONE\\|CANCELED\\|NOTE\\|PROJECT}&STYLE<>\"habit\""
      ((org-agenda-overriding-header "Scheduled tasks: ")
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'notscheduled))
       (org-agenda-sorting-strategy
        '(category-up))))
     ("d" "Unscheduled open source tasks (by date)" tags "TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}"
      ((org-agenda-overriding-header "Unscheduled Open Source tasks (by date): ")
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp 'regexp "\\* \\(DEFERRED\\|SOMEDAY\\)"))
       (org-agenda-sorting-strategy
        '(user-defined-up))
       (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
       (org-agenda-files
        '("~/doc/tasks/OSS.org"))))
     ("o" "Unscheduled open source tasks (by project)" tags "TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT}"
      ((org-agenda-overriding-header "Unscheduled Open Source tasks (by project): ")
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp 'regexp "\\* \\(DEFERRED\\|SOMEDAY\\)"))
       (org-agenda-sorting-strategy
        '(category-up))
       (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
       (org-agenda-files
        '("~/doc/tasks/OSS.org"))))
     ("u" "Unscheduled tasks" tags "TODO<>\"\"&TODO<>{DONE\\|CANCELED\\|NOTE\\|PROJECT\\|DEFERRED\\|SOMEDAY}"
      ((org-agenda-overriding-header "Unscheduled tasks: ")
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp))
       (org-agenda-sorting-strategy
        '(user-defined-up))
       (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
       (org-agenda-files
        '("~/doc/tasks/todo.org" "~/doc/tasks/Bahai.org"))))
     ("U" "Deferred tasks" tags "TODO=\"DEFERRED\""
      ((org-agenda-overriding-header "Deferred tasks:")
       (org-agenda-sorting-strategy
        '(user-defined-up))
       (org-agenda-prefix-format "%-11c%5(org-todo-age) ")))
     ("Y" "Someday tasks" tags "TODO=\"SOMEDAY\""
      ((org-agenda-overriding-header "Someday tasks:")
       (org-agenda-sorting-strategy
        '(user-defined-up))
       (org-agenda-prefix-format "%-11c%5(org-todo-age) ")))
     ("w" "Unscheduled work-related tasks" tags "TODO<>\"\"&TODO<>{DONE\\|DEFERRED\\|CANCELED\\|NOTE\\|PROJECT}"
      ((org-agenda-overriding-header "Unscheduled work-related tasks")
       (org-agenda-files
        '("~/dfinity/docs/dfinity.org"))
       (org-agenda-sorting-strategy
        '(category-up user-defined-up))
       (org-agenda-skip-function
        '(org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp))
       (org-agenda-prefix-format "%-11c%5(org-todo-age) ")))
     ("c" "Appointment Calendar" agenda ""
      ((org-agenda-overriding-header "Appointment Calendar")
       (org-agenda-sorting-strategy
        '(time-up))
       (org-agenda-span 14)
       (org-agenda-ndays 14)
       (org-agenda-regexp-filter-preset
        '("+APPT"))))))
 '(org-agenda-deadline-leaders '("!D!: " "D%02d: "))
 '(org-agenda-default-appointment-duration 60)
 '(org-agenda-files
   '("~/doc/tasks/todo.org" "~/doc/tasks/habits.org" "~/dfinity/docs/dfinity.org" "~/doc/tasks/Bahai.org" "~/doc/tasks/OSS.org"))
 '(org-agenda-fontify-priorities t)
 '(org-agenda-include-diary t)
 '(org-agenda-inhibit-startup t)
 '(org-agenda-log-mode-items '(closed clock state))
 '(org-agenda-ndays 1)
 '(org-agenda-persistent-filter t)
 '(org-agenda-prefix-format
   '((agenda . "  %-11c%?-12t% s")
     (timeline . "  % s")
     (todo . "  %-11c%5(org-todo-age) ")
     (tags . "  %-11c")))
 '(org-agenda-scheduled-leaders '("" "S%d: "))
 '(org-agenda-scheduled-relative-text "S%d: ")
 '(org-agenda-scheduled-text "")
 '(org-agenda-show-all-dates t)
 '(org-agenda-skip-deadline-if-done t)
 '(org-agenda-skip-scheduled-if-deadline-is-shown t)
 '(org-agenda-skip-scheduled-if-done t)
 '(org-agenda-skip-unavailable-files t)
 '(org-agenda-sorting-strategy
   '((agenda habit-down time-up todo-state-up priority-down)
     (todo priority-down category-keep)
     (tags priority-down category-keep)
     (search category-keep)))
 '(org-agenda-start-on-weekday nil)
 '(org-agenda-tags-column -100)
 '(org-agenda-tags-todo-honor-ignore-options t)
 '(org-agenda-text-search-extra-files '(agenda-archives "~/doc/tasks/notes.org"))
 '(org-agenda-todo-ignore-scheduled 'past)
 '(org-agenda-use-time-grid nil)
 '(org-agenda-window-frame-fractions '(0.5 . 0.75))
 '(org-archive-location "TODO-archive::")
 '(org-archive-save-context-info '(time category itags))
 '(org-attach-file-list-property nil)
 '(org-attach-method 'mv)
 '(org-attach-store-link-p 'attached)
 '(org-author-transforms '(("^Howard Reubenstein$" . "Howard")))
 '(org-beamer-frame-default-options "fragile")
 '(org-capture-templates
   '(("a" "Add Task" entry
      (file+headline "~/doc/tasks/todo.org" "Inbox")
      "* TODO %?
:PROPERTIES:
:ID:       %(shell-command-to-string \"uuidgen\"):CREATED:  %U
:END:" :prepend t)
     ("n" "Note" entry
      (file "~/doc/tasks/notes.org")
      "* NOTE %?
:PROPERTIES:
:ID:       %(shell-command-to-string \"uuidgen\"):CREATED:  %U
:END:" :prepend t)
     ("c" "Calendar" entry
      (file+headline "~/doc/tasks/todo.org" "Inbox")
      "* APPT %?
:PROPERTIES:
:ID:       %(shell-command-to-string \"uuidgen\"):CREATED:  %U
:END:" :prepend t)
     ("t" "Add Task" entry
      (file+headline "~/doc/tasks/todo.org" "Inbox")
      "* TODO %?
:PROPERTIES:
:ID:       %(shell-command-to-string \"uuidgen\"):CREATED:  %U
:END:" :prepend t)
     ("p" "Protocol" entry
      (file+headline "~/doc/tasks/todo.org" "Inbox")
      "* NOTE %?
#+BEGIN_QUOTE
%i
#+END_QUOTE
:PROPERTIES:
:ID:       %(shell-command-to-string \"uuidgen\"):CREATED:  %U
:URL:      %c
:END:")
     ("L" "Protocol Link" entry
      (file+headline "~/doc/tasks/todo.org" "Inbox")
      "* NOTE %?
[[%:link][%:description]]
#+BEGIN_QUOTE
%i
#+END_QUOTE
:PROPERTIES:
:ID:       %(shell-command-to-string \"uuidgen\"):CREATED:  %U
:URL:      %c
:END:")
     ("j" "Journal entry" entry
      (file+datetree "~/dfinity/docs/dfinity.org")
      "* %?")))
 '(org-clock-clocked-in-display nil)
 '(org-clock-idle-time 10)
 '(org-clock-in-resume t)
 '(org-clock-in-switch-to-state "STARTED")
 '(org-clock-into-drawer "LOGBOOK")
 '(org-clock-mode-line-total 'current)
 '(org-clock-out-remove-zero-time-clocks t)
 '(org-clock-out-switch-to-state nil)
 '(org-clock-persist t)
 '(org-clock-persist-file "~/.emacs.d/data/org-clock-save.el")
 '(org-clock-resolve-expert t)
 '(org-completion-use-ido t)
 '(org-confirm-babel-evaluate nil)
 '(org-confirm-elisp-link-function nil)
 '(org-confirm-shell-link-function nil)
 '(org-crypt-disable-auto-save t)
 '(org-crypt-key "0xAB37611BDDE48EBD")
 '(org-cycle-global-at-bob t)
 '(org-deadline-warning-days 14)
 '(org-default-notes-file "~/doc/tasks/todo.org")
 '(org-depend-tag-blocked nil)
 '(org-directory "~/doc/tasks/")
 '(org-ditaa-jar-path "~/.nix-profile/lib/ditaa.jar")
 '(org-drawers '("PROPERTIES" "CLOCK" "LOGBOOK" "OUT"))
 '(org-edit-src-content-indentation 0)
 '(org-enforce-todo-dependencies t)
 '(org-export-babel-evaluate nil)
 '(org-export-latex-classes
   '(("article" "\\documentclass[11pt]{article}"
      ("\\section{%s}" . "\\section*{%s}")
      ("\\subsection{%s}" . "\\subsection*{%s}")
      ("\\subsubsection{%s}" . "\\subsubsection*{%s}")
      ("\\paragraph{%s}" . "\\paragraph*{%s}")
      ("\\subparagraph{%s}" . "\\subparagraph*{%s}"))
     ("linalg" "\\documentclass{article}
\\usepackage{linalgjh}
[DEFAULT-PACKAGES]
[EXTRA]
[PACKAGES]"
      ("\\section{%s}" . "\\section*{%s}")
      ("\\subsection{%s}" . "\\subsection*{%s}")
      ("\\subsubsection{%s}" . "\\subsubsection*{%s}")
      ("\\paragraph{%s}" . "\\paragraph*{%s}")
      ("\\subparagraph{%s}" . "\\subparagraph*{%s}"))
     ("report" "\\documentclass[11pt]{report}"
      ("\\part{%s}" . "\\part*{%s}")
      ("\\chapter{%s}" . "\\chapter*{%s}")
      ("\\section{%s}" . "\\section*{%s}")
      ("\\subsection{%s}" . "\\subsection*{%s}")
      ("\\subsubsection{%s}" . "\\subsubsection*{%s}"))
     ("book" "\\documentclass[11pt]{book}"
      ("\\part{%s}" . "\\part*{%s}")
      ("\\chapter{%s}" . "\\chapter*{%s}")
      ("\\section{%s}" . "\\section*{%s}")
      ("\\subsection{%s}" . "\\subsection*{%s}")
      ("\\subsubsection{%s}" . "\\subsubsection*{%s}"))
     ("beamer" "\\documentclass{beamer}" org-beamer-sectioning)))
 '(org-extend-today-until 4)
 '(org-fast-tag-selection-single-key 'expert)
 '(org-fontify-done-headline t)
 '(org-fontify-quote-and-verse-blocks t)
 '(org-fontify-whole-heading-line t)
 '(org-footnote-section nil)
 '(org-gcal-dir "~/.emacs.d/data/org-gcal/")
 '(org-habit-preceding-days 42)
 '(org-habit-today-glyph 45)
 '(org-hide-emphasis-markers t)
 '(org-hide-leading-stars t)
 '(org-icalendar-combined-agenda-file "~/doc/tasks/org.ics")
 '(org-icalendar-timezone "America/Los_Angeles")
 '(org-id-locations-file "~/.emacs.d/data/org-id-locations")
 '(org-image-actual-width nil)
 '(org-imenu-depth 4)
 '(org-insert-heading-respect-content t)
 '(org-irc-link-to-logs t t)
 '(org-latex-default-packages-alist
   '(("T1" "fontenc" t)
     ("" "fixltx2e" nil)
     ("" "graphicx" t)
     ("" "longtable" nil)
     ("" "float" nil)
     ("" "wrapfig" nil)
     ("" "rotating" nil)
     ("normalem" "ulem" t)
     ("" "amsmath" t)
     ("" "textcomp" t)
     ("" "marvosym" t)
     ("" "wasysym" t)
     ("" "amssymb" t)
     ("" "hyperref" nil)
     "\\tolerance=1000"))
 '(org-latex-listings 'minted)
 '(org-latex-minted-options
   '(("fontsize" "\\footnotesize")
     ("linenos" "true")
     ("xleftmargin" "0em")))
 '(org-latex-pdf-process
   '("pdflatex -shell-escape -interaction nonstopmode -output-directory %o %f" "pdflatex -shell-escape -interaction nonstopmode -output-directory %o %f" "pdflatex -shell-escape -interaction nonstopmode -output-directory %o %f"))
 '(org-mime-preserve-breaks nil)
 '(org-mobile-agendas '("Z"))
 '(org-mobile-directory "~/Dropbox/Apps/MobileOrg")
 '(org-mobile-files '("~/doc/tasks/todo.org"))
 '(org-mobile-files-exclude-regexp "\\(TODO\\(-.*\\)?\\)\\'")
 '(org-mobile-inbox-for-pull "~/doc/tasks/from-mobile.org")
 '(org-mode-hook
   '(org-babel-result-hide-spec org-babel-hide-all-hashes abbrev-mode))
 '(org-modules '(org-gnus org-habit org-info org-depend))
 '(org-plantuml-jar-path "~/.nix-profile/lib/plantuml.jar")
 '(org-pretty-entities t)
 '(org-priority-faces
   '((65 :foreground "White" :weight bold)
     (66 . "White")
     (67 :foreground "dark gray" :slant italic)))
 '(org-refile-target-verify-function 'org-refile-heading-p)
 '(org-refile-targets '((org-agenda-files :todo . "PROJECT")))
 '(org-return-follows-link t)
 '(org-reverse-note-order t)
 '(org-smart-capture-use-lastname t)
 '(org-src-fontify-natively t)
 '(org-src-tab-acts-natively t)
 '(org-stuck-projects '("TODO=\"PROJECT\"" ("TODO" "DEFERRED") nil ""))
 '(org-subject-transforms
   '(("\\`\\(Re\\|Fwd\\): " . "")
     ("\\`{ledger} " . "")
     ("([Ww]as: .+)\\'" . "")
     ("\\`\\[[a-z-]+\\] " . "")
     ("\\`bug#\\([0-9]+\\):" . "[[x-debbugs-gnu:\\1][#\\1]]")))
 '(org-tags-column -97)
 '(org-time-clocksum-use-fractional t)
 '(org-todo-keyword-faces
   '(("TODO" :foreground "medium blue" :weight bold)
     ("EPIC" :foreground "deep sky blue" :weight bold)
     ("STORY" :foreground "royal blue" :weight bold)
     ("RECUR" :foreground "cornflowerblue" :weight bold)
     ("APPT" :foreground "medium blue" :weight bold)
     ("NOTE" :foreground "brown" :weight bold)
     ("STARTED" :foreground "dark orange" :weight bold)
     ("WAITING" :foreground "red" :weight bold)
     ("DELEGATED" :foreground "dark violet" :weight bold)
     ("DEFERRED" :foreground "dark blue" :weight bold)
     ("SOMEDAY" :foreground "dark blue" :weight bold)
     ("PROJECT" :foreground "#088e8e" :weight bold)))
 '(org-todo-repeat-to-state "TODO")
 '(org-use-property-inheritance '("AREA"))
 '(org-use-speed-commands t)
 '(org-use-tag-inheritance nil)
 '(org-velocity-always-use-bucket t)
 '(org-velocity-bucket "~/doc/tasks/notes.org")
 '(org-velocity-capture-templates
   '(("v" "Velocity" entry
      (file "~/doc/tasks/notes.org")
      "* NOTE %:search
%i%?
:PROPERTIES:
:ID:       %(shell-command-to-string \"uuidgen\"):CREATED:  %U
:END:" :prepend t)))
 '(org-velocity-exit-on-match nil)
 '(org-velocity-force-new t)
 '(org-velocity-search-method 'regexp)
 '(org-velocity-use-completion t)
 '(org-x-backends '(ox-org ox-redmine))
 '(org-x-redmine-title-prefix-function 'org-x-redmine-title-prefix)
 '(org-x-redmine-title-prefix-match-function 'org-x-redmine-title-prefix-match))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(org-agenda-clocking ((t (:background "red2"))) t)
 '(org-agenda-done ((t (:foreground "ForestGreen"))))
 '(org-done ((t (:foreground "ForestGreen" :weight bold))))
 '(org-habit-alert-face ((((background light)) (:background "#f5f946"))))
 '(org-habit-alert-future-face ((((background light)) (:background "#fafca9"))))
 '(org-habit-clear-face ((((background light)) (:background "#8270f9"))))
 '(org-habit-clear-future-face ((((background light)) (:background "#d6e4fc"))))
 '(org-habit-overdue-face ((((background light)) (:background "#f9372d"))))
 '(org-habit-overdue-future-face ((((background light)) (:background "#fc9590"))))
 '(org-habit-ready-face ((((background light)) (:background "#4df946"))))
 '(org-habit-ready-future-face ((((background light)) (:background "#acfca9"))))
 '(org-headline-done ((t (:foreground "grey75" :strike-through t :slant italic))))
 '(org-level-4 ((t (:foreground "green"))))
 '(org-scheduled ((((class color) (min-colors 88) (background light)) nil)))
 '(org-upcoming-deadline ((((class color) (min-colors 88) (background light)) (:foreground "Brown")))))
