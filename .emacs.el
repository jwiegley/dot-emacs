;;; -*- mode: emacs-lisp -*-

;;;_* initial packages

;; Add other site-lisp directories, in case they were not setup by the
;; environment.

(dolist
    (path
     (reverse
      (list
       (expand-file-name "~/Projects/ledger/lisp")
       (expand-file-name "/opt/local/share/doc/git-core/contrib/emacs")
       (expand-file-name "~/Library/Emacs")
       (expand-file-name "~/Library/Emacs/site-lisp/apel")
       (expand-file-name "~/Library/Emacs/site-lisp/delim-kill")
       (expand-file-name "~/Library/Emacs/site-lisp/eshell")
       (expand-file-name "~/Library/Emacs/site-lisp/ess/lisp")
       (expand-file-name "~/Library/Emacs/site-lisp/gist")
       (expand-file-name "~/Library/Emacs/site-lisp/haskell-mode")
       (expand-file-name "~/Library/Emacs/site-lisp/magit")
       (expand-file-name "~/Library/Emacs/site-lisp/org-mode/contrib/lisp")
       (expand-file-name "~/Library/Emacs/site-lisp/org-mode/lisp")
       (expand-file-name "~/Library/Emacs/site-lisp/regex-tool")
       (expand-file-name "~/Library/Emacs/site-lisp/remember")
       (expand-file-name "~/Library/Emacs/site-lisp/scala-mode")
       (expand-file-name "~/Library/Emacs/site-lisp/yasnippet")
       (expand-file-name "~/Library/Emacs/site-lisp/zencoding")
       )))

  (setq path (expand-file-name path))
  (setq load-path (delete path load-path))

  (when (file-directory-p path)
    (let ((default-directory path))
      (normal-top-level-add-subdirs-to-load-path)
      (add-to-list 'load-path path))))

(load "autoloads" t)

;; Read in the Mac's global environment settings.

(let ((plist (expand-file-name "~/.MacOSX/environment.plist")))
  (when (file-readable-p plist)
    (let ((dict (cdr (assq 'dict (cdar (xml-parse-file plist))))))
      (while dict
	(when (and (listp (car dict)) (eq 'key (caar dict)))
	  (setenv (car (cddr (car dict)))
		  (car (cddr (car (cddr dict))))))
	(setq dict (cdr dict))))
    (setq exec-path nil)
    (dolist (path (nreverse (split-string (getenv "PATH") ":")))
      (add-to-list 'exec-path path))))

;; Set the *Message* log to something higher

(setq message-log-max 2048)

;;;_* customizations

;;;_ * variables

(custom-set-variables
  ;; custom-set-variables was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 '(after-save-hook (quote (executable-make-buffer-file-executable-if-script-p)))
 '(align-c++-modes (quote (csharp-mode c++-mode c-mode java-mode groovy-mode)))
 '(align-to-tab-stop nil)
 '(auto-compression-mode t nil (jka-compr))
 '(auto-image-file-mode t)
 '(auto-save-interval 1024)
 '(backup-directory-alist (quote (("/Volumes/Files/" . "/Volumes/Files/.backups") (".*recentf.*" . "/tmp") (".*" . "~/.emacs.d/backups"))))
 '(backward-delete-char-untabify-method (quote untabify))
 '(bookmark-save-flag 1)
 '(browse-url-browser-function (quote (("\\.\\(gz\\|tgz\\|bz2\\|tbz\\|dmg\\|iso\\|pdf\\|mp3\\)\\'" . browse-url-download-file) (".*" . browse-url-default-macosx-browser))))
 '(c-default-style (quote ((java-mode . "gnu") (awk-mode . "awk") (other . "gnu"))))
 '(calendar-latitude 40.845112)
 '(calendar-longitude -74.287672)
 '(calendar-mark-holidays-flag t)
 '(circe-ignore-list (quote ("jordanb_?")))
 '(clean-buffer-list-kill-regexps (quote (".*")))
 '(column-number-mode t)
 '(compilation-scroll-output t)
 '(completion-ignored-extensions (quote (".svn/" "CVS/" ".o" "~" ".bin" ".lbin" ".so" ".a" ".ln" ".blg" ".bbl" ".elc" ".lof" ".glo" ".idx" ".lot" ".dvi" ".fmt" ".tfm" ".pdf" ".class" ".fas" ".lib" ".mem" ".x86f" ".sparcf" ".xfasl" ".fasl" ".ufsl" ".fsl" ".dxl" ".pfsl" ".dfsl" ".lo" ".la" ".gmo" ".mo" ".toc" ".aux" ".cp" ".fn" ".ky" ".pg" ".tp" ".vr" ".cps" ".fns" ".kys" ".pgs" ".tps" ".vrs" ".pyc" ".pyo")))
 '(current-language-environment "UTF-8")
 '(custom-buffer-done-function (quote kill-buffer))
 '(custom-raised-buttons nil)
 '(cycbuf-buffer-sort-function (quote cycbuf-sort-by-recency))
 '(cycbuf-clear-delay 2)
 '(cycbuf-dont-show-regexp (quote ("^ " "^\\*cycbuf\\*$" "^\\*")))
 '(cycbuf-file-name-replacements (quote (("/Users/johnw/" "~/"))))
 '(cycbuf-max-window-height 10)
 '(default-frame-alist (quote ((font . "-apple-courier-medium-r-normal--15-0-72-72-m-0-iso10646-1") (cursor-color . "#b247ee"))))
 '(default-input-method "latin-1-prefix")
 '(default-major-mode (quote fundamental-mode))
 '(delete-by-moving-to-trash t)
 '(delete-old-versions (quote none))
 '(directory-free-space-args "-kh")
 '(dired-guess-shell-gnutar "tar")
 '(dired-listing-switches "-lh")
 '(dired-load-hook (quote ((lambda nil (load "dired-x")))))
 '(dired-no-confirm (quote (byte-compile chgrp chmod chown copy hardlink symlink touch)))
 '(dired-omit-mode nil t)
 '(dired-recursive-copies (quote always))
 '(dired-recursive-deletes (quote always))
 '(display-time-mode t)
 '(elscreen-display-tab nil)
 '(elscreen-prefix-key "")
 '(emacs-lisp-mode-hook (quote (turn-on-auto-fill eldoc-mode (lambda nil (local-set-key [(meta 46)] (quote find-function)) (local-set-key [(control 109)] (quote newline-and-indent))))))
 '(enable-recursive-minibuffers t)
 '(eshell-history-size 1000)
 '(eshell-ls-dired-initial-args (quote ("-h")))
 '(eshell-ls-exclude-regexp "~\\'")
 '(eshell-ls-initial-args "-h")
 '(eshell-modules-list (quote (eshell-alias eshell-basic eshell-cmpl eshell-dirs eshell-glob eshell-hist eshell-ls eshell-pred eshell-prompt eshell-rebind eshell-script eshell-term eshell-unix eshell-xtra)))
 '(eshell-prefer-to-shell t nil (eshell))
 '(eshell-save-history-on-exit t)
 '(eshell-stringify-t nil)
 '(eshell-term-name "ansi")
 '(eshell-visual-commands (quote ("vi" "top" "screen" "less" "lynx" "ssh" "rlogin" "telnet")))
 '(eval-expr-print-function (quote pp) t)
 '(fill-column 78)
 '(flyspell-abbrev-p nil)
 '(flyspell-incorrect-hook (quote (flyspell-maybe-correct-transposition)))
 '(focus-follows-mouse t)
 '(font-lock-support-mode (quote jit-lock-mode))
 '(frame-title-format (quote (:eval (if buffer-file-name default-directory "%b"))) t)
 '(global-auto-revert-mode t)
 '(global-font-lock-mode t nil (font-lock))
 '(ibuffer-expert t)
 '(ibuffer-formats (quote ((mark modified read-only " " (name 16 -1) " " (size 6 -1 :right) " " (mode 16 16) " " filename) (mark " " (name 16 -1) " " filename))))
 '(ibuffer-maybe-show-regexps nil)
 '(ibuffer-shrink-to-minimum-size t t)
 '(ibuffer-use-other-window t)
 '(ido-auto-merge-work-directories-length 0)
 '(ido-cannot-complete-command (quote ido-exit-minibuffer))
 '(ido-decorations (quote ("{" "}" "," ",..." "[" "]" " [No match]" " [Matched]" " [Not readable]" " [Too big]" " [Confirm]")))
 '(ido-enable-flex-matching t)
 '(ido-ignore-files (quote ("\\`CVS/" "\\`#" "\\`.#" "\\`\\.\\./" "\\`\\./" "\\`\\.DS_Store" "\\`\\.localized")))
 '(ido-mode (quote both) nil (ido))
 '(ido-use-filename-at-point nil)
 '(ido-use-virtual-buffers t)
 '(inhibit-startup-echo-area-message "johnw")
 '(inhibit-startup-screen t)
 '(initial-frame-alist (quote ((top . 25) (left . 515) (width . 100) (height . 76))))
 '(kill-whole-line t)
 '(large-file-warning-threshold nil)
 '(ledger-file "/Volumes/Files/ledger.dat")
 '(line-number-mode t)
 '(initsplit-customizations-alist (quote (("\\`\\(canlock\\|eudc\\|spam\\|nnmail\\|nndraft\\|mm\\|message\\|mail\\|gnus\\|send-mail\\|starttls\\|smtpmail\\|check-mail\\)-" "~/Library/Emacs/.gnus.el" nil))))
 '(line-spacing 2)
 '(lui-time-stamp-position nil)
 '(mac-pass-command-to-system nil)
 '(mac-pass-control-to-system nil)
 '(magit-process-popup-time 15)
 '(magit-push-script "/Users/johnw/bin/push")
 '(mark-holidays-in-calendar t)
 '(next-line-add-newlines nil)
 '(ns-alternate-modifier (quote alt))
 '(ns-command-modifier (quote meta))
 '(nxml-sexp-element-flag t)
 '(nxml-slash-auto-complete-flag t)
 '(org-M-RET-may-split-line (quote ((headline) (default . t))))
 '(org-agenda-auto-exclude-function (quote org-my-auto-exclude-function))
 '(org-agenda-custom-commands (quote (("E" "Errands (next 2 days)" tags "Errand&TODO<>\"DONE\"&TODO<>\"CANCELLED\"&STYLE<>\"habit\"&SCHEDULED<\"<+2d>\"" ((org-agenda-overriding-header "Errands (next 2 days)"))) ("A" "Today's priority #A tasks" agenda "" ((org-agenda-ndays 1) (org-agenda-overriding-header "Today's priority #A tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote notregexp) "\\=.*\\[#A\\]"))))) ("B" "Today's priority #A and #B tasks" agenda "" ((org-agenda-ndays 1) (org-agenda-overriding-header "Today's priority #A and #B tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "\\=.*\\[#C\\]"))))) ("W" "Waiting/delegated tasks" tags "TODO=\"WAITING\"|TODO=\"DELEGATED\"" ((org-agenda-overriding-header "Waiting/delegated tasks:"))) ("u" "Unscheduled tasks" tags "CATEGORY<>\"CEG\"&TODO<>\"\"&TODO<>\"DONE\"&TODO<>\"CANCELLED\"&TODO<>\"NOTE\"" ((org-agenda-overriding-header "Unscheduled tasks: ") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote scheduled) (quote deadline) (quote timestamp) (quote regexp) "\\* \\(DEFERRED\\|SOMEDAY\\)"))) (org-agenda-files (quote ("~/Dropbox/todo.txt"))))) ("U" "Deferred tasks" tags "TODO=\"DEFERRED\"" ((org-agenda-overriding-header "Deferred tasks:"))) ("S" "Someday tasks" tags "TODO=\"SOMEDAY\"" ((org-agenda-overriding-header "Someday tasks:"))) ("l" "Ledger tasks" alltodo "" ((org-agenda-files (quote ("~/src/ledger/plan/TODO"))) (org-agenda-overriding-header "Ledger tasks:"))) ("r" "Uncategorized items" tags "CATEGORY=\"Inbox\"&LEVEL=2" ((org-agenda-overriding-header "Uncategorized items"))) ("w" "Unscheduled work tasks" tags "CATEGORY=\"CEG\"&TODO<>\"DONE\"&TODO<>\"CANCELLED\"&TODO<>\"NOTE\"&LEVEL>1" ((org-agenda-overriding-header "Unscheduled work tasks") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote scheduled) (quote deadline)))) (org-agenda-sorting-strategy (quote (todo-state-up priority-down))))) ("z" "CEG tasks not in Bugzilla" tags "CATEGORY=\"CEG\"&TODO<>\"DONE\"&TODO<>\"CANCELLED\"&TODO<>\"NOTE\"&TODO<>\"\"&LEVEL>1" ((org-agenda-overriding-header "CEG tasks not in Bugzilla") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote regexp) "cegbug:"))))) ("Z" "CEG tasks in Bugzilla" tags "CATEGORY=\"CEG\"&TODO<>\"DONE\"&TODO<>\"CANCELLED\"&TODO<>\"NOTE\"&LEVEL>1" ((org-agenda-overriding-header "CEG tasks in Bugzilla") (org-agenda-skip-function (quote (org-agenda-skip-entry-if (quote notregexp) "cegbug:"))) (org-agenda-sorting-strategy (quote (todo-state-up priority-down))))))))
 '(org-agenda-deadline-leaders (quote ("D: " "D%d: ")))
 '(org-agenda-deadline-relative-text "D%d: ")
 '(org-agenda-deadline-text "D: ")
 '(org-agenda-default-appointment-duration 60)
 '(org-agenda-files (quote ("~/Dropbox/todo.txt" "~/Projects/ledger/plan/TODO")))
 '(org-agenda-fontify-priorities t)
 '(org-agenda-include-diary t)
 '(org-agenda-ndays 1)
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
 '(org-default-notes-file "~/Dropbox/todo.txt")
 '(org-directory "~/Dropbox/")
 '(org-enforce-todo-dependencies t)
 '(org-extend-today-until 8)
 '(org-fast-tag-selection-single-key (quote expert))
 '(org-footnote-section nil)
 '(org-habit-preceding-days 42)
 '(org-hide-leading-stars t)
 '(org-mobile-directory "/Volumes/docs")
 '(org-mobile-files (quote (org-agenda-files org-agenda-text-search-extra-files)))
 '(org-mobile-inbox-for-pull "~/Dropbox/from-mobile.org")
 '(org-modules (quote (org-crypt org-id org-habit org-mac-message org-bookmark org-eval org-R org2rem)))
 '(org-refile-targets (quote ((org-agenda-files :level . 1))))
 '(org-remember-store-without-prompt t)
 '(org-remember-templates (quote (("Task" 116 "* TODO %?
  SCHEDULED: %t
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :END:
  %U" nil "Inbox" nil))))
 '(org-reverse-note-order t)
 '(org-stuck-projects (quote ("+LEVEL=1/-DONE" ("TODO" "STARTED" "NEXT" "NEXTACTION") nil "\\(Appointments\\|Notes\\|Anniversaries\\)")))
 '(org-tag-alist (quote ((#("NASIM" 0 5 (face nil)) . 110) (#("WORK" 0 4 (face nil)) . 119))))
 '(org-tags-column -97)
 '(org-time-clocksum-use-fractional t)
 '(org-todo-keyword-faces (quote (("TODO" :foreground "medium blue" :weight bold) ("APPT" :foreground "medium blue" :weight bold) ("NOTE" :foreground "brown" :weight bold) ("STARTED" :foreground "dark orange" :weight bold) ("WAITING" :foreground "red" :weight bold) ("DELEGATED" :foreground "dark violet" :weight bold) ("DEFERRED" :foreground "dark blue" :weight bold) ("SOMEDAY" :foreground "dark blue" :weight bold))))
 '(org-todo-keywords (quote ((sequence "TODO" "APPT" "|" "DONE" "NOTE"))))
 '(org-todo-repeat-to-state "TODO")
 '(org-use-speed-commands t)
 '(org-use-tag-inheritance nil)
 '(parens-require-spaces t)
 '(pcomplete-compare-entries-function (quote file-newer-than-file-p))
 '(ps-font-size (quote (8 . 10)))
 '(ps-footer-font-size (quote (12 . 14)))
 '(ps-header-font-size (quote (12 . 14)))
 '(ps-header-title-font-size (quote (14 . 16)))
 '(ps-line-number-font-size 10)
 '(ps-print-color-p nil)
 '(python-check-command "epylint")
 '(read-buffer-function (quote ido-read-buffer))
 '(recentf-auto-cleanup 600)
 '(recentf-exclude (quote ("~\\'" "\\`out\\'" "\\.log\\'" "^/[^/]*:")))
 '(recentf-max-saved-items 200)
 '(recentf-mode t)
 '(regex-tool-backend (quote perl))
 '(remember-annotation-functions (quote (org-remember-annotation)))
 '(remember-handler-functions (quote (org-remember-handler)))
 '(require-final-newline (quote ask))
 '(safe-local-variable-values (quote ((after-save-hook archive-done-tasks) (after-save-hook sort-done-tasks) (after-save-hook commit-after-save))))
 '(scroll-bar-mode nil)
 '(session-globals-exclude (quote (load-history flyspell-auto-correct-ring)))
 '(session-registers (quote (t (0 . 127))))
 '(show-paren-delay 0)
 '(show-paren-mode (quote paren))
 '(slime-kill-without-query-p t)
 '(slime-startup-animation nil)
 '(smtpmail-default-smtp-server "smtp.gmail.com")
 '(smtpmail-smtp-server "smtp.gmail.com")
 '(smtpmail-smtp-service 587)
 '(smtpmail-starttls-credentials (quote (("smtp.gmail.com" 587 "" ""))))
 '(special-display-regexps (quote (("#\\(ledger\\)" (menu-bar-lines . 0) (tool-bar-lines . 0) (vertical-scroll-bars) (font . "-apple-lucida grande-medium-r-normal--16-0-72-72-m-0-iso10646-1") (top . 295) (left . 2) (width . 70) (height . 40) (alpha . 0.9) (splittable . t) (unsplittable) (dedicated)) ("journal\\.txt" (menu-bar-lines) (tool-bar-lines) (width . 80) (height . 50) (dedicated) (top . 265) (left . 1130)))))
 '(sql-sqlite-program "sqlite3")
 '(svn-status-hide-unmodified t)
 '(tags-apropos-verbose t)
 '(tags-case-fold-search nil)
 '(temp-buffer-resize-mode t nil (help))
 '(text-mode-hook (quote (auto-fill-mode)))
 '(timeclock-file "/Users/johnw/doc/.timelog")
 '(timeclock-modeline-display nil nil (timeclock))
 '(timeclock-relative nil)
 '(tool-bar-mode nil)
 '(tramp-verbose 3)
 '(uniquify-buffer-name-style (quote post-forward-angle-brackets) nil (uniquify))
 '(user-full-name "John Wiegley")
 '(user-initials "jww")
 '(user-mail-address "jwiegley@gmail.com")
 '(vc-follow-symlinks t)
 '(vc-handled-backends (quote (GIT)))
 '(version-control t)
 '(visible-bell t)
 '(whitespace-auto-cleanup t)
 '(whitespace-rescan-timer-time nil)
 '(whitespace-silent t)
 '(winner-mode t nil (winner))
 '(x-select-enable-clipboard t)
 '(x-stretch-cursor t)
 '(zencoding-preview-default nil))

;;;_ * faces

(custom-set-faces
  ;; custom-set-faces was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 '(circe-highlight-all-nicks-face ((t (:foreground "dark blue"))))
 '(circe-originator-face ((t (:foreground "dark orange"))))
 '(font-lock-comment-face ((((class color)) (:foreground "firebrick"))))
 '(ledger-register-pending-face ((t (:weight bold))))
 '(magit-branch-face ((((class color) (background light)) (:foreground "Blue"))))
 '(magit-diff-none-face ((((class color) (background light)) (:foreground "grey50"))))
 '(org-habit-alert-face ((((background light)) (:background "#f5f946"))))
 '(org-habit-alert-future-face ((((background light)) (:background "#fafca9"))))
 '(org-habit-clear-face ((((background light)) (:background "#8270f9"))))
 '(org-habit-clear-future-face ((((background light)) (:background "#d6e4fc"))))
 '(org-habit-overdue-face ((((background light)) (:background "#f9372d"))))
 '(org-habit-overdue-future-face ((((background light)) (:background "#fc9590"))))
 '(org-habit-ready-face ((((background light)) (:background "#4df946"))))
 '(org-habit-ready-future-face ((((background light)) (:background "#acfca9"))))
 '(org-scheduled ((((class color) (min-colors 88) (background light)) nil)))
 '(org-upcoming-deadline ((((class color) (min-colors 88) (background light)) (:foreground "Brown"))))
 '(slime-highlight-edits-face ((((class color) (background light)) (:background "gray98"))))
 '(trailing-whitespace ((((class color) (background light)) (:background "light salmon")))))

;;;_ * disabled commands

(put 'eval-expression  'disabled nil)   ; Let ESC-ESC work
(put 'narrow-to-region 'disabled nil)   ; Let narrowing work
(put 'narrow-to-page   'disabled nil)   ; Let narrowing work
(put 'upcase-region    'disabled nil)   ; Let downcasing work
(put 'downcase-region  'disabled nil)   ; Let upcasing work
(put 'erase-buffer     'disabled nil)

;;;_* packages

(mapc #'load (directory-files "~/Library/Emacs/lang" t "\\.el$" t))

;;;_ * bookmark+

(load "bookmark+" t)

;;;_ * browse-kill-ring

(load "browse-kill-ring+" t)

;;;_ * cc-mode

(eval-after-load "cc-styles"
  '(progn
     (add-to-list
      'c-style-alist
      '("ceg"
	(c-basic-offset . 3)
	(c-comment-only-line-offset . (0 . 0))
	(c-hanging-braces-alist     . ((substatement-open before after)
				       (arglist-cont-nonempty)))
	(c-offsets-alist . ((statement-block-intro . +)
			    (knr-argdecl-intro . 5)
			    (substatement-open . 0)
			    (substatement-label . 0)
			    (label . 0)
			    (statement-case-open . 0)
			    (statement-cont . +)
			    (arglist-intro . c-lineup-arglist-intro-after-paren)
			    (arglist-close . c-lineup-arglist)
			    (inline-open . 0)
			    (brace-list-open . 0)
			    (topmost-intro-cont
			     . (first c-lineup-topmost-intro-cont
				      c-lineup-gnu-DEFUN-intro-cont))))
	(c-special-indent-hook . c-gnu-impose-minimum)
	(c-block-comment-prefix . "")))
     (add-to-list
      'c-style-alist
      '("edg"
	(indent-tabs-mode . nil)
	(c-basic-offset . 3)
	(c-comment-only-line-offset . (0 . 0))
	(c-hanging-braces-alist     . ((substatement-open before after)
				       (arglist-cont-nonempty)))
	(c-offsets-alist . ((statement-block-intro . +)
			    (knr-argdecl-intro . 5)
			    (substatement-open . 0)
			    (substatement-label . 0)
			    (label . 0)
			    (case-label . +)
			    (statement-case-open . 0)
			    (statement-cont . +)
			    (arglist-intro . c-lineup-arglist-intro-after-paren)
			    (arglist-close . c-lineup-arglist)
			    (inline-open . 0)
			    (brace-list-open . 0)
			    (topmost-intro-cont
			     . (first c-lineup-topmost-intro-cont
				      c-lineup-gnu-DEFUN-intro-cont))))
	(c-special-indent-hook . c-gnu-impose-minimum)
	(c-block-comment-prefix . "")))
     (add-to-list
      'c-style-alist
      '("ledger"
	(indent-tabs-mode . nil)
	(c-basic-offset . 2)
	(c-comment-only-line-offset . (0 . 0))
	(c-hanging-braces-alist     . ((substatement-open before after)
				       (arglist-cont-nonempty)))
	(c-offsets-alist . ((statement-block-intro . +)
			    (knr-argdecl-intro . 5)
			    (substatement-open . 0)
			    (substatement-label . 0)
			    (label . 0)
			    (case-label . +)
			    (statement-case-open . 0)
			    (statement-cont . +)
			    (arglist-intro . c-lineup-arglist-intro-after-paren)
			    (arglist-close . c-lineup-arglist)
			    (inline-open . 0)
			    (brace-list-open . 0)
			    (topmost-intro-cont
			     . (first c-lineup-topmost-intro-cont
				      c-lineup-gnu-DEFUN-intro-cont))))
	(c-special-indent-hook . c-gnu-impose-minimum)
	(c-block-comment-prefix . "")))))

(eval-when-compile
  (defvar c-mode-base-map))

(defun my-c-mode-common-hook ()
  (doxymacs-mode)
  (define-key c-mode-base-map "\C-m" 'newline-and-indent)
  (set (make-local-variable 'parens-require-spaces) nil)
  (setq indicate-empty-lines t)
  (setq fill-column 78)
  (column-marker-3 80)
  (font-lock-add-keywords
   'c++-mode '(("\\<\\(assert\\|DEBUG\\)(" 1 widget-inactive t))))

(which-function-mode t)

(add-hook 'c-mode-common-hook 'my-c-mode-common-hook)

;;;_ * chess

(load "chess-auto" t)

;;;_ * cycbuf

(autoload 'cycbuf-switch-to-next-buffer "cycbuf" nil t)
(autoload 'cycbuf-switch-to-previous-buffer "cycbuf" nil t)

;;;_ * delim-kill

(autoload 'delim-kill "delim-kill" nil t)

;;;_ * doxymacs

(autoload 'doxymacs-mode "doxymacs")
(autoload 'doxymacs-font-lock "doxymacs")

(defun my-doxymacs-font-lock-hook ()
  (if (or (eq major-mode 'c-mode) (eq major-mode 'c++-mode))
      (doxymacs-font-lock)))

(add-hook 'font-lock-mode-hook 'my-doxymacs-font-lock-hook)

;;;_ * edebug

(load "edebug" t)

;;;_ * elint

(defun elint-current-buffer ()
  (interactive)
  (elint-initialize)
  (elint-current-buffer))

(eval-after-load "elint"
  '(progn
     (add-to-list 'elint-standard-variables 'current-prefix-arg)
     (add-to-list 'elint-standard-variables 'command-line-args-left)
     (add-to-list 'elint-standard-variables 'buffer-file-coding-system)
     (add-to-list 'elint-standard-variables 'emacs-major-version)
     (add-to-list 'elint-standard-variables 'window-system)))

;;;_ * elscreen

(require 'elscreen)

(define-key elscreen-map "\C-\\" 'elscreen-toggle)
(define-key elscreen-map "\\"    'toggle-input-method)

;;;_ * emacs-lisp

(defun elisp-indent-or-complete (&optional arg)
  (interactive "p")
  (call-interactively 'lisp-indent-line)
  (unless (or (looking-back "^\\s-*")
	      (bolp)
	      (not (looking-back "[-A-Za-z0-9_*+/=<>!?]+")))
    (call-interactively 'lisp-complete-symbol)))

(eval-after-load "lisp-mode"
  '(progn
    (define-key emacs-lisp-mode-map [tab] 'elisp-indent-or-complete)))

(add-hook 'emacs-lisp-mode-hook 'turn-on-auto-fill)

(mapc (lambda (major-mode)
	(font-lock-add-keywords
	 major-mode
	 `(("(\\(lambda\\)\\>"
	    (0 (ignore
		(compose-region (match-beginning 1)
				(match-end 1) ?λ)))))))
      '(emacs-lisp-mode))

;;;_  + eshell

(eval-after-load "em-unix"
  '(progn
     (unintern 'eshell/rm)))

;;;_  + column-marker

(autoload 'column-marker-1 "column-marker")

(add-hook 'emacs-lisp-mode-hook (lambda () (interactive) (column-marker-1 79)))

;;;_  + paredit

(autoload 'paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)
(autoload 'turn-on-paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)

(dolist (hook '(emacs-lisp-mode-hook))
  (add-hook hook 'turn-on-paredit-mode))

;;;_  + redhank

(autoload 'redshank-mode "redshank"
  "Minor mode for restructuring Lisp code (i.e., refactoring)." t)

(dolist (hook '(emacs-lisp-mode-hook
		lisp-mode-hook
		slime-repl-mode-hook))
  (add-hook hook #'(lambda () (redshank-mode +1))))

;;;_ * ess

(load "ess-site" t)

;;;_ * eval-expr

(when (load "eval-expr" t)
  (eval-expr-install))

;;;_ * flyspell

(load "flyspell-ext" t)

;;;_ * git

(setenv "GIT_PAGER" "")

(require 'magit)
(require 'gist)

(autoload 'column-marker-1 "column-marker")

(add-hook 'magit-log-edit-mode-hook
	  (function
	   (lambda ()
	     (set-fill-column 72)
	     (column-number-mode t)
	     (column-marker-1 72))))

(setq github-username "jwiegley")
(setq github-api-key "14c811944452528f94a5b1e3488487cd")

(defun commit-after-save ()
  (let ((file (file-name-nondirectory (buffer-file-name))))
    (message "Committing changes to Git...")
    (if (= 0 (shell-command
	      (format "git add \"%s\" ; git commit -m \"changes to %s\""
		      file file)))
	(message "Committed changes to %s" file)
      (message "NO changes saved for %s" file))))

(eval-after-load "dired-x"
  '(progn
     (defvar dired-omit-regexp-orig (symbol-function 'dired-omit-regexp))

     (defun dired-omit-regexp ()
       (let ((file (expand-file-name ".git"))
	     parent-dir)
	 (while (and (not (file-exists-p file))
		     (progn
		       (setq parent-dir
			     (file-name-directory
			      (directory-file-name
			       (file-name-directory file))))
		       ;; Give up if we are already at the root dir.
		       (not (string= (file-name-directory file)
				     parent-dir))))
	   ;; Move up to the parent dir and try again.
	   (setq file (expand-file-name ".git" parent-dir)))
	 ;; If we found a change log in a parent, use that.
	 (if (file-exists-p file)
	     (let ((regexp (funcall dired-omit-regexp-orig))
		   (omitted-files (shell-command-to-string
				   "git clean -d -x -n")))
	       (if (= 0 (length omitted-files))
		   regexp
		 (concat
		  regexp
		  (if (> (length regexp) 0)
		      "\\|" "")
		  "\\("
		  (mapconcat
		   #'(lambda (str)
		       (concat "^"
			       (regexp-quote
				(substring str 13
					   (if (= ?/ (aref str (1- (length str))))
					       (1- (length str))
					     nil)))
			       "$"))
		   (split-string omitted-files "\n" t)
		   "\\|")
		  "\\)")))
	   (funcall dired-omit-regexp-orig))))

     (defun dired-delete-file (file &optional recursive)
       (if recursive
	   (call-process "/Users/johnw/bin/del" nil nil nil "-fr" file)
	 (call-process "/Users/johnw/bin/del" nil nil nil file)))))

;;;_ * groovy-mode

(autoload 'groovy-mode "groovy" "" t)

(add-to-list 'interpreter-mode-alist '("groovy" . groovy-mode))
(add-to-list 'auto-mode-alist '("\\.groovy\\'" . groovy-mode))

(defun my-groovy-mode-hook ()
  (define-key groovy-mode-map "\C-m" 'newline-and-indent)
  (setq groovy-indent-level 3)
  (setq indent-tabs-mode nil)
  (set-fill-column 100))

(add-hook 'groovy-mode-hook 'my-groovy-mode-hook)

;;;_ * haskell-mode

(load "haskell-site-file" t)

(defun my-haskell-mode-hook ()
  (flymake-mode)

  (turn-on-haskell-doc-mode)
  (turn-on-haskell-indentation)

  (define-key haskell-mode-map [(control ?c) ?w]
    'flymake-display-err-menu-for-current-line)
  (define-key haskell-mode-map [(control ?c) ?*]
    'flymake-start-syntax-check)
  (define-key haskell-mode-map [(meta ?n)] 'flymake-goto-next-error)
  (define-key haskell-mode-map [(meta ?p)] 'flymake-goto-prev-error))

(add-hook 'haskell-mode-hook 'my-haskell-mode-hook)

(load "inf-haskell" t)
(load "hs-lint" t)

;;;_ * java-mode

(defun my-java-mode-hook ()
  (c-set-style "ceg")
  (setq c-basic-offset 3)
  (setq indent-tabs-mode nil)
  (setq tab-width 3)
  (column-marker-3 100)
  (set-fill-column 100))

(add-hook 'java-mode-hook 'my-java-mode-hook)

;;;_ * ledger

(load "ldg-new")

;;;_ * linum-mode

(autoload 'linum-mode "linum" nil t)

;;;_ * mule

(prefer-coding-system 'utf-8)
(set-terminal-coding-system 'utf-8)
(setq x-select-request-type '(UTF8_STRING COMPOUND_TEXT TEXT STRING))

(defun normalize-file ()
  (interactive)
  (set-buffer-file-coding-system 'unix)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "\r$" nil t)
      (replace-match "")))
  (set-buffer-file-coding-system 'utf-8)
  (untabify (point-min) (point-max))
  (let ((require-final-newline t))
    (save-buffer)))

;;;_ * nroff-mode

(defun update-nroff-timestamp ()
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^\\.Dd ")
      (let ((stamp (format-time-string "%B %e, %Y")))
	(unless (looking-at stamp)
	  (delete-region (point) (line-end-position))
	  (insert stamp)
	  (let (after-save-hook)
	    (save-buffer)))))))

(add-hook 'nroff-mode-hook
	  (function
	   (lambda ()
	     (add-hook 'after-save-hook 'update-nroff-timestamp nil t))))

;;;_ * nxml-mode

;(autoload 'nxml-mode "rng-auto" "" t)

(defalias 'xml-mode 'nxml-mode)

(defun my-nxml-mode-hook ()
  (define-key nxml-mode-map [return] 'newline-and-indent)
  (define-key nxml-mode-map [(control return)] 'other-window))

(add-hook 'nxml-mode-hook 'my-nxml-mode-hook)

;;;_ * nxml-mode

(defun load-nxhtml ()
  (interactive)
  (load "~/Library/Emacs/site-lisp/nxhtml/autostart.el"))

;;;_ * objc++-mode

(add-to-list 'auto-mode-alist '("\\.h\\'" . c++-mode))
(add-to-list 'auto-mode-alist '("\\.m\\'" . c-mode))
(add-to-list 'auto-mode-alist '("\\.mm\\'" . c++-mode))

;;;_ * pcomplete

;;;_ * puppet-mode

(autoload 'puppet-mode "puppet-mode" "Major mode for editing puppet manifests")

(add-to-list 'auto-mode-alist '("\\.pp$" . puppet-mode))

;;;_ * python-mode

(require 'python)

(defvar python-keywords-wanting-colon
  '("def" "class" "if" "elif" "while" "else" "with"
    "try" "except" "finally" "for" "lambda"))

(defvar python-kwc-regexp nil)

(autoload 'word-at-point "thingatpt" nil t)

(defun python-newline-and-indent ()
  "Always make sure that colons appear in the appropriate place."
  (interactive)
  (unless (progn
	    (skip-chars-backward " \t")
	    (memq (char-before) '(?: ?, ?\\)))
    (let ((here (point)))
      (goto-char (line-beginning-position))
      (skip-chars-forward " \t")
      (let ((add-colon-p (member (word-at-point)
				 python-keywords-wanting-colon)))
	(goto-char here)
	(if add-colon-p
	    (let ((last-command-char ?:))
	      (python-electric-colon nil))))))
  (call-interactively 'newline-and-indent))

(defun my-python-mode-hook ()
  (flymake-mode)
  
  (setq indicate-empty-lines t)
  (set (make-local-variable 'parens-require-spaces) nil)
  (setq indent-tabs-mode nil)

  (define-key python-mode-map [return] 'python-newline-and-indent)

  (define-key python-mode-map [(control ?c) ?w]
    'flymake-display-err-menu-for-current-line)
  (define-key python-mode-map [(control ?c) (control ?w)]
    'flymake-start-syntax-check)
  (define-key python-mode-map [(meta ?n)] 'flymake-goto-next-error)
  (define-key python-mode-map [(meta ?p)] 'flymake-goto-prev-error))

(add-hook 'python-mode-hook 'my-python-mode-hook)

;;; flymake

(autoload 'flymake-mode "flymake" "" t)

(eval-after-load "flymake"
  '(progn
     (defun flymake-pylint-init ()
       (let* ((temp-file   (flymake-init-create-temp-buffer-copy
			    'flymake-create-temp-inplace))
	      (local-file  (file-relative-name
			    temp-file
			    (file-name-directory buffer-file-name))))
	 (list "epylint" (list local-file))))

     (add-to-list 'flymake-allowed-file-name-masks
		  '("\\.py\\'" flymake-pylint-init))

     (defun flymake-hslint-init ()
       (let* ((temp-file   (flymake-init-create-temp-buffer-copy
			    'flymake-create-temp-inplace))
	      (local-file  (file-relative-name
			    temp-file
			    (file-name-directory buffer-file-name))))
	 (list "hslint" (list local-file))))

     (add-to-list 'flymake-allowed-file-name-masks
		  '("\\.l?hs\\'" flymake-hslint-init))))

;;;_ * org-mode

(require 'org-install)
(require 'org-attach)
(require 'org-devonthink)
(require 'org-babel-init)
(require 'org-babel-R)
(require 'org-babel-python)
(require 'org-babel-emacs-lisp)
(require 'org-babel-haskell)
(require 'org-babel-sh)

;;(load "org-log" t)

(add-to-list 'auto-mode-alist '("\\.org$" . org-mode))

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
	((string= tag "net")
	 (/= 0 (call-process "/sbin/ping" nil nil nil
			     "-c1" "-q" "-t1" "mail.gnu.org")))
	((string= tag "home")
	 (with-temp-buffer
	   (call-process "/sbin/ifconfig" nil t nil "en0" "inet")
	   (goto-char (point-min))
	   (not (re-search-forward "inet 192\\.168\\.9\\." nil t))))
	((or (string= tag "errand") (string= tag "call"))
	 (let ((hour (nth 2 (decode-time))))
	   (or (< hour 8) (> hour 21)))))
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
	  (search-forward "* CEG")
	  (goto-char (match-beginning 0))
	  (insert tasks))))))

(add-hook 'org-mobile-post-pull-hook 'my-org-convert-incoming-items)

(defun org-insert-bug (bug)
  (interactive "nBug: ")
  (insert (format "[[cegbug:%s][#%s]]" bug bug)))

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
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (if (re-search-backward org-my-ts-regexp begin t)
	  (let ((time (float-time (org-time-string-to-time (match-string 0)))))
	    (assert (floatp time))
	    time)
	(debug)))))

(defun org-get-completed-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (and (re-search-backward "\\(- State \"\\(DONE\\|DEFERRED\\|CANCELLED\\)\"\\s-+\\[\\(.+?\\)\\]\\|CLOSED: \\[\\(.+?\\)\\]\\)" begin t)
	   (time-to-seconds (org-time-string-to-time (or (match-string 3)
							 (match-string 4))))))))

(defun org-my-sort-done-tasks ()
  (interactive)
  (goto-char (point-min))
  (org-sort-entries-or-items t ?F #'org-get-inactive-time #'<)
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
      (let ((org-remember-templates
	     '((110 "* STARTED %?
  - State \"STARTED\"    %U
  SCHEDULED: %t
  :PROPERTIES:
  :ID:       %(shell-command-to-string \"uuidgen\")  :END:
  %U" "~/Dropbox/todo.txt" "Inbox"))))
	(org-remember)))))

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
    (let ((org-remember-templates
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

;;;_ * remember

(require 'remember)

(add-hook 'remember-mode-hook 'org-remember-apply-template)

;;;_ * scala-mode

(load "scala-mode-auto" t)

;;;_ * session

(when (load "session" t)
  (add-hook 'after-init-hook 'session-initialize)

  (defun save-information ()
    (dolist (func kill-emacs-hook)
      (unless (eq func 'exit-gnus-on-exit)
	(funcall func))))

  (run-with-idle-timer 900 t 'save-information))

;;;_ * sunrise-commander

(autoload 'sunrise "sunrise-commander" nil t)

;;;_ * timestamp

(defcustom user-initials nil
  "*Initials of this user."
  :set #'(lambda (symbol value)
	   (if (fboundp 'font-lock-add-keywords)
	       (mapcar
		#'(lambda (mode)
		    (font-lock-add-keywords
		     mode (list (list (concat "\\<\\(" value " [^:\n]+\\):")
				      1 font-lock-warning-face t))))
		'(c-mode c++-mode emacs-lisp-mode lisp-mode
			 python-mode perl-mode java-mode groovy-mode)))
	   (set symbol value))
  :type 'string
  :group 'mail)

(defun insert-user-timestamp ()
  "Insert a quick timestamp using the value of `user-initials'."
  (interactive)
  (insert (format "%s (%s): " user-initials
		  (format-time-string "%Y-%m-%d" (current-time)))))

;;;_ * toggle-code-file

(defun toggle-code-file (&optional arg)
  (interactive "p")
  (cond
   ((string-match "\\.as[cphma]x\\'" buffer-file-name)
    (find-file (concat buffer-file-name ".cs")))
   ((string-match "\\.as[cphma]x\\.cs\\'" buffer-file-name)
    (find-file (substring buffer-file-name 0
			  (- (length buffer-file-name) 3))))
   ((string-match "\\.\\(c\\(c\\|pp\\)?\\|mm?\\)\\'" buffer-file-name)
    (find-file (concat (substring buffer-file-name 0
				  (match-beginning 0)) ".h")))
   ((string-match "\\.h\\'" buffer-file-name)
    (let ((base (substring buffer-file-name 0
			   (match-beginning 0))))
      (dolist (ext '(".cc" ".cpp" ".c" ".mm" ".m"))
	(if (file-readable-p (concat base ext))
	    (find-file (concat base ext))))))))

;;;_ * whitespace

(autoload 'whitespace-buffer "whitespace")
(autoload 'whitespace-cleanup "whitespace" "" t)

(eval-after-load "whitespace"
  '(progn
     (remove-hook 'find-file-hooks 'whitespace-buffer)
     (remove-hook 'kill-buffer-hook 'whitespace-buffer)))

(defun maybe-turn-on-whitespace ()
  "Depending on the file, maybe turn on `whitespace-mode'."
  (let ((file (expand-file-name ".clean"))
	parent-dir)
    (while (and (not (file-exists-p file))
		(progn
		  (setq parent-dir
			(file-name-directory
			 (directory-file-name
			  (file-name-directory file))))
		  ;; Give up if we are already at the root dir.
		  (not (string= (file-name-directory file)
				parent-dir))))
      ;; Move up to the parent dir and try again.
      (setq file (expand-file-name ".clean" parent-dir)))
    ;; If we found a change log in a parent, use that.
    (when (and (file-exists-p file)
	       (not (file-exists-p ".noclean"))
	       (not (and buffer-file-name
			 (string-match "\\.texi$" buffer-file-name))))
      (add-hook 'write-contents-hooks
		#'(lambda ()
		    (ignore (whitespace-buffer))) nil t)
      (whitespace-buffer))))

(add-hook 'find-file-hooks 'maybe-turn-on-whitespace t)

;;;_ * yasnippet

(when (load "yasnippet" t)
  (yas/initialize)
  (yas/load-directory "~/Library/Emacs/snippets/"))

;;;_ * zencoding

(setq zencoding-mode-keymap (make-sparse-keymap))
(define-key zencoding-mode-keymap (kbd "C-c C-c") 'zencoding-expand-line)

(autoload 'zencoding-mode "zencoding-mode" nil t)

(add-hook 'nxml-mode-hook 'zencoding-mode)
(add-hook 'html-mode-hook 'zencoding-mode)

(add-hook 'html-mode-hook
	  (function
	   (lambda ()
	     (interactive)
	     (define-key html-mode-map [return] 'newline-and-indent))))

;;;_ * diminish

(when (load "diminish" t)
  (diminish 'abbrev-mode)
  (diminish 'auto-fill-function)
  (ignore-errors
    (diminish 'yas/minor-mode))

  (defadvice dired-omit-startup (after diminish-dired-omit activate)
    "Make sure to remove \"Omit\" from the modeline."
    (diminish 'dired-omit-mode))

  (eval-after-load "dot-mode" '(diminish 'dot-mode))
  (eval-after-load "eldoc"    '(diminish 'eldoc-mode))
  (eval-after-load "winner"   '(ignore-errors (diminish 'winner-mode))))

;;;_* keybindings

;;;_ * global

(define-key global-map [(control meta backspace)] 'backward-kill-sexp)

(defun smart-beginning-of-line (&optional arg)
  (interactive "p")
  (let ((here (point)))
    (beginning-of-line-text arg)
    (if (= here (point))
	(beginning-of-line arg))))

(define-key global-map [(control ?.)] 'smart-beginning-of-line)

(defun tidy-xml-buffer ()
  (interactive)
  (save-excursion
    (call-process-region (point-min) (point-max) "tidy" t t nil
			 "-xml" "-i" "-wrap" "0" "-omit" "-q")))

(define-key global-map [(control shift ?h)] 'tidy-xml-buffer)

(defun isearch-backward-other-window ()
  (interactive)
  (split-window-vertically)
  (call-interactively 'isearch-backward))

(define-key global-map [(control meta ?r)] 'isearch-backward-other-window)

(defun isearch-forward-other-window ()
  (interactive)
  (split-window-vertically)
  (call-interactively 'isearch-forward))

(define-key global-map [(control meta ?s)] 'isearch-forward-other-window)

(defun collapse-or-expand (&optional arg)
  (interactive "P")
  (if (> (length (window-list)) 1)
      (if arg
	  (delete-window)
	(delete-other-windows))
    (if arg
	(progn
	  (split-window-vertically)
	  (setq this-command 'isearchb-activate)
	  (call-interactively 'isearchb-activate))
      (bury-buffer))))

(define-key global-map [(control meta ?w)] 'delim-kill)

(define-key global-map [(control ?z)] 'collapse-or-expand)

(defun delete-indentation-forward ()
  (interactive)
  (delete-indentation t))

(define-key global-map [(meta ?j)] 'delete-indentation-forward)
(define-key global-map [(meta ?J)] 'delete-indentation)
(define-key global-map [(meta ?n)] 'chop-move-down)
(define-key global-map [(meta ?p)] 'chop-move-up)
(define-key global-map [(meta ?m)] 'org-maybe-remember)
(define-key global-map [(meta ?z)] 'org-inline-note)

(define-prefix-command 'lisp-find-map)
(define-key global-map [(control ?h) ?e] 'lisp-find-map)
(define-key lisp-find-map [?a] 'apropos)
(define-key lisp-find-map [?e] 'view-echo-area-messages)
(define-key lisp-find-map [?f] 'find-function)
(define-key lisp-find-map [?v] 'find-variable)
(define-key lisp-find-map [?k] 'find-function-on-key)

(defun visit-ledger-channel ()
  (interactive)
  (select-window (display-buffer "#ledger" t t)))

(defun get-main-frame ()
  (catch 'found
    (dolist (frame (frame-list))
      (let* ((wind (frame-first-window frame))
	     (title (buffer-name (window-buffer wind))))
	(unless (or (string= "*Org Agenda*" title)
		    (string= "#ledger" title)
		    (string= "journal.txt" title)
		    (string-match "todo\\.txt-[0-9]+" title))
	  (throw 'found frame))))))

(defun main-frame ()
  (interactive)
  (select-frame-set-input-focus (get-main-frame)))

(define-key global-map [(alt ?c)] 'jump-to-org-agenda)
(define-key global-map [(alt ?m)] 'main-frame)
(define-key global-map [(meta ?\])] 'main-frame)
(define-key global-map [(alt ?l)] 'visit-ledger-channel)

(define-key global-map [(meta ?C)] 'jump-to-org-agenda)
(define-key global-map [(meta ?G)] 'gnus)
(define-key global-map [(meta ?N)] 'winner-redo)
(define-key global-map [(meta ?P)] 'winner-undo)
(define-key global-map [(meta ?T)] 'tags-search)

(define-key global-map [(meta ?\')] 'insert-pair)
(define-key global-map [(meta ?\")] 'insert-pair)

(defun align-code (beg end &optional arg)
  (interactive "rP")
  (if (null arg)
      (align beg end)
    (let ((end-mark (copy-marker end)))
      (indent-region beg end-mark nil)
      (align beg end-mark))))

(define-key global-map [(meta ?\[)] 'align-code)
(define-key global-map [(meta ?!)]  'eshell-command)
(define-key global-map [(meta ?`)]  'cycbuf-switch-to-next-buffer)
(define-key global-map [(meta ?~)]  'cycbuf-switch-to-previous-buffer)
;;(define-key global-map [(meta ?`)]  'other-frame)
(define-key global-map [(alt ?`)]   'delete-frame)

(defun mark-line (&optional arg)
  (interactive "p")
  (beginning-of-line)
  (let ((here (point)))
    (dotimes (i arg)
      (end-of-line))
    (set-mark (point))
    (goto-char here)))

(defun mark-sentence (&optional arg)
  (interactive "P")
  (backward-sentence)
  (mark-end-of-sentence arg))

(define-key global-map [(meta shift ?w)] 'mark-word)
(define-key global-map [(meta shift ?l)] 'mark-line)
(define-key global-map [(meta shift ?s)] 'mark-sentence)
(define-key global-map [(meta shift ?x)] 'mark-sexp)
(define-key global-map [(meta shift ?b)] 'python-mark-block)
(define-key global-map [(meta shift ?h)] 'mark-paragraph)
(define-key global-map [(meta shift ?d)] 'mark-defun)

(define-key global-map [(control return)] 'other-window)

(define-key global-map [f5] 'gud-cont)
(define-key global-map [f10] 'gud-next)
(define-key global-map [f11] 'gud-step)
(define-key global-map [(shift f11)] 'gud-finish)

(define-key global-map [(alt ?v)] 'scroll-down)
(define-key global-map [(meta ?v)] 'yank)

(define-key global-map [(alt tab)]
  #'(lambda ()
      (interactive)
      (call-interactively (key-binding (kbd "M-TAB")))))

;;;_ * cursor-mode

;; Change cursor color according to mode; inspired by
;; http://www.emacswiki.org/emacs/ChangingCursorDynamically

(setq djcb-read-only-color       "gray"
      djcb-read-only-cursor-type 'hbar
      djcb-overwrite-color       "red"
      djcb-overwrite-cursor-type 'box
      djcb-normal-color          "#b247ee"
      djcb-normal-cursor-type    'box)

(defun set-cursor-according-to-mode ()
  "change cursor color and type according to some minor modes."
  (interactive)
  (cond
    (buffer-read-only
      (set-cursor-color djcb-read-only-color)
      (setq cursor-type djcb-read-only-cursor-type))
    (overwrite-mode
      (set-cursor-color djcb-overwrite-color)
      (setq cursor-type djcb-overwrite-cursor-type))
    (t 
      (set-cursor-color djcb-normal-color)
      (setq cursor-type djcb-normal-cursor-type))))

;;;_ * ctl-x

(define-key ctl-x-map [?d] 'delete-whitespace-rectangle)
(define-key ctl-x-map [?g] 'magit-status)
(define-key ctl-x-map [?t] 'toggle-truncate-lines)

(defun unfill-paragraph (arg)
  (interactive "*p")
  (let (beg end)
    (forward-paragraph arg)
    (setq end (copy-marker (- (point) 2)))
    (backward-paragraph arg)
    (if (eolp)
	(forward-char))
    (setq beg (point-marker))
    (when (> (count-lines beg end) 1)
      (while (< (point) end)
	(goto-char (line-end-position))
	(let ((sent-end (memq (char-before) '(?. ?\; ?! ??))))
	  (delete-indentation 1)
	  (if sent-end
	      (insert ? )))
	(end-of-line))
      (save-excursion
	(goto-char beg)
	(while (re-search-forward "[^.;!?:]\\([ \t][ \t]+\\)" end t)
	  (replace-match " " nil nil nil 1))))))

(defun unfill-region (beg end)
  (interactive "r")
  (setq end (copy-marker end))
  (save-excursion
    (goto-char beg)
    (while (< (point) end)
      (unfill-paragraph 1)
      (forward-paragraph))))

(defun refill-paragraph (arg)
  (interactive "*P")
  (let ((fun (if (memq major-mode '(c-mode c++-mode))
		 'c-fill-paragraph
	       (or fill-paragraph-function
		   'fill-paragraph)))
	(width (if (numberp arg) arg))
	prefix beg end)
    (forward-paragraph 1)
    (setq end (copy-marker (- (point) 2)))
    (forward-line -1)
    (let ((b (point)))
      (skip-chars-forward "^A-Za-z0-9`'\"(")
      (setq prefix (buffer-substring-no-properties b (point))))
    (backward-paragraph 1)
    (if (eolp)
	(forward-char))
    (setq beg (point-marker))
    (delete-horizontal-space)
    (while (< (point) end)
      (delete-indentation 1)
      (end-of-line))
    (let ((fill-column (or width fill-column))
	  (fill-prefix prefix))
      (if prefix
	  (setq fill-column
		(- fill-column (* 2 (length prefix)))))
      (funcall fun nil)
      (goto-char beg)
      (insert prefix)
      (funcall fun nil)
      (if (memq major-mode '(c-mode c++-mode))
	  (c-recomment-region beg (+ end 2))))
    (goto-char (+ end 2))))

(define-key ctl-x-map [(meta ?q)] 'refill-paragraph)
(define-key ctl-x-map [(meta ?Q)] 'unfill-paragraph)

(if (functionp 'ibuffer)
    (define-key ctl-x-map [(control ?b)] 'ibuffer)
  (define-key ctl-x-map [(control ?b)] 'list-buffers))

(defun duplicate-line (&optional where)
  "Duplicate the line containing point."
  (interactive "d")
  (save-excursion
    (beginning-of-line)
    (let ((beg (point)))
      (end-of-line)
      (copy-region-as-kill beg (point)))
    (end-of-line)
    (if (eobp)
	(insert ?\n)
      (forward-line))
    (open-line 1)
    (yank)))

(define-key ctl-x-map [(control ?d)] 'duplicate-line)

(defun find-existing-file (file-name)
  "Edit file FILENAME.
Switch to a buffer visiting file FILENAME,
creating one if none already exists.
Interactively, or if WILDCARDS is non-nil in a call from Lisp,
expand wildcards (if any) and visit multiple files."
  (interactive
   (list (read-file-name "Find file: " default-directory nil
			 (null current-prefix-arg))))
  (condition-case err
      (find-file file-name)
    (file-error
     (if (and (string-match "^File is not readable:"
			    (error-message-string err))
	      (not (string-match ":" file-name)))
	 (find-file (concat "/[root@localhost]" file-name))
       (signal (car err) (cdr err))))))

;;(define-key ctl-x-map [(control ?f)] 'find-existing-file)
(define-key ctl-x-map [(control ?v)] 'my-ido-choose-from-recentf)

(autoload 'esh-toggle "esh-toggle" nil t)

(define-key ctl-x-map [(control ?z)] 'eshell-toggle)

;;;_ * mode-specific

(define-key mode-specific-map [tab] 'toggle-code-file)

(define-key mode-specific-map [space] 'just-one-space)
(define-key mode-specific-map [? ] 'just-one-space)
(define-key mode-specific-map [?1] 'just-one-space)

(define-key mode-specific-map [?a] 'org-agenda)
(define-key mode-specific-map [?b] 'ignore)
(define-key mode-specific-map [?c] 'compile)

(defun clone-region-set-mode (start end &optional mode)
  (interactive "r")
  (with-current-buffer (clone-indirect-buffer "*clone*" t)
    (narrow-to-region start end)
    (if mode
	(funcall mode)
      (lisp-mode))))

(define-key mode-specific-map [?C] 'clone-region-set-mode)

(defun delete-current-line (&optional arg)
  (interactive "p")
  (let ((here (point)))
    (beginning-of-line)
    (kill-line arg)
    (goto-char here)))

(define-key mode-specific-map [?d] 'delete-current-line)

(define-key mode-specific-map [?e ?a] 'byte-recompile-directory)

(defun do-eval-buffer ()
  (interactive)
  (call-interactively 'eval-buffer)
  (message "Buffer has been evaluated"))

(define-key mode-specific-map [?e ?b] 'do-eval-buffer)
(define-key mode-specific-map [?e ?c] 'cancel-debug-on-entry)
(define-key mode-specific-map [?e ?d] 'debug-on-entry)
(define-key mode-specific-map [?e ?f] 'emacs-lisp-byte-compile-and-load)
(define-key mode-specific-map [?e ?r] 'eval-region)

(defun scratch ()
  (interactive)
  (switch-to-buffer-other-window (get-buffer-create "*scratch*"))
  ;;(lisp-interaction-mode)
  (text-mode)
  (if current-prefix-arg
      (find-file "~/src/snippets.hs")
    (goto-char (point-min))
    (when (looking-at ";")
      (forward-line 4)
      (delete-region (point-min) (point)))
    (goto-char (point-max))))

(define-key mode-specific-map [?e ?s] 'scratch)
(define-key mode-specific-map [?e ?v] 'edit-variable)
(define-key mode-specific-map [?e ?e] 'toggle-debug-on-error)
(define-key mode-specific-map [?e ?E] 'elint-current-buffer)

(define-key mode-specific-map [?f] 'flush-lines)
(define-key mode-specific-map [?g] 'goto-line)
(define-key mode-specific-map [?h] 'ignore)

(define-key mode-specific-map [?i ?b] 'flyspell-buffer)
(define-key mode-specific-map [?i ?c] 'ispell-comments-and-strings)
(define-key mode-specific-map [?i ?d] 'ispell-change-dictionary)
(define-key mode-specific-map [?i ?f] 'flyspell-mode)
(define-key mode-specific-map [?i ?k] 'ispell-kill-ispell)
(define-key mode-specific-map [?i ?m] 'ispell-message)
(define-key mode-specific-map [?i ?r] 'ispell-region)

(define-key mode-specific-map [?j] 'ignore)
(define-key mode-specific-map [?k] 'keep-lines)

(defun my-ledger-start-entry (&optional arg)
  (interactive "p")
  (unless (file-directory-p "/Volumes/Files")
    (shell-command "open /Users/johnw/Documents/Files.sparsebundle"))
  (while (not (file-directory-p "/Volumes/Files"))
    (sleep-for 0 50))
  (find-file-other-window "/Volumes/Files/Accounts/ledger.dat")
  (goto-char (point-max))
  (skip-syntax-backward " ")
  (if (looking-at "\n\n")
      (goto-char (point-max))
    (delete-region (point) (point-max))
    (insert ?\n)
    (insert ?\n))
  (insert (format-time-string "%Y/%m/%d ")))

(define-key mode-specific-map [?l] 'my-ledger-start-entry)

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

(define-key mode-specific-map [?m] 'ignore)
(define-key mode-specific-map [?n] 'insert-user-timestamp)
(define-key mode-specific-map [?o] 'customize-option)
(define-key mode-specific-map [?O] 'customize-group)
(define-key mode-specific-map [?p] 'ignore)
(define-key mode-specific-map [?q] 'fill-region)
(define-key mode-specific-map [?r] 'replace-regexp)
(define-key mode-specific-map [?s] 'replace-string)

(define-key mode-specific-map [?t ?%] 'tags-query-replace)
(define-key mode-specific-map [?t ?a] 'tags-apropos)
(define-key mode-specific-map [?t ?e] 'tags-search)
(define-key mode-specific-map [?t ?v] 'visit-tags-table)

(define-key mode-specific-map [?t ?c] 'timeclock-change)
(define-key mode-specific-map [?t ?i] 'timeclock-in)
(define-key mode-specific-map [?t ?o] 'timeclock-out)
(define-key mode-specific-map [?t ?r] 'timeclock-reread-log)
(define-key mode-specific-map [?t ?u] 'timeclock-update-modeline)
(define-key mode-specific-map [?t (control ?m)] 'timeclock-status-string)

(define-key mode-specific-map [?t ?a] 'tags-apropos)

(define-key mode-specific-map [?u] 'rename-uniquely)
(define-key mode-specific-map [?v] 'visit-url)

(defun view-clipboard ()
  (interactive)
  (delete-other-windows)
  (switch-to-buffer "*Clipboard*")
  (let ((inhibit-read-only t))
    (erase-buffer)
    (clipboard-yank)
    (goto-char (point-min))
    (html-mode)
    (view-mode)))

(define-key mode-specific-map [(shift ?v)] 'view-clipboard)

(define-key mode-specific-map [?w] 'wdired-change-to-wdired-mode)
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
  #'(lambda nil (interactive) (org-todo "CANCELLED")))

(define-key mode-specific-map [?x ?L] 'org-set-dtp-link)
(define-key mode-specific-map [?x ?M] 'org-set-message-link)
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
(define-key mode-specific-map [?y] 'ignore)
(define-key mode-specific-map [?z] 'clean-buffer-list)

(define-key mode-specific-map [?\[] 'align-regexp)
(define-key mode-specific-map [?=]  'count-matches)
(define-key mode-specific-map [?\;] 'comment-or-uncomment-region)

;;;_ * footnote

(eval-after-load "footnote"
  '(define-key footnote-mode-map "#" 'redo-footnotes))

;;;_ * isearch-mode

(define-key isearch-mode-map [(control ?c)] 'isearch-toggle-case-fold)
(define-key isearch-mode-map [(control ?t)] 'isearch-toggle-regexp)
(define-key isearch-mode-map [(control ?^)] 'isearch-edit-string)
(define-key isearch-mode-map [(control ?i)] 'isearch-complete)

;;;_ * mail-mode

(eval-after-load "sendmail"
  '(define-key mail-mode-map [(control ?i)] 'mail-complete))

;;;_ * org-mode

(eval-after-load "org"
  '(progn
     (org-defkey org-mode-map [(control meta return)] 'org-insert-heading-after-current)
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
       (define-key map "w" 'org-agenda-refile)
       (define-key map " " 'org-agenda-tree-to-indirect-buffer)
       (define-key map "F" 'org-agenda-follow-mode)
       (define-key map "q" 'delete-window)
       (define-key map [(meta ?p)] 'org-agenda-earlier)
       (define-key map [(meta ?n)] 'org-agenda-later)

       (define-prefix-command 'org-todo-state-map)

       (define-key map "x" 'org-todo-state-map)

       (define-key org-todo-state-map "d"
	 #'(lambda nil (interactive) (org-agenda-todo "DONE")))
       (define-key org-todo-state-map "r"
	 #'(lambda nil (interactive) (org-agenda-todo "DEFERRED")))
       (define-key org-todo-state-map "y"
	 #'(lambda nil (interactive) (org-agenda-todo "SOMEDAY")))
       (define-key org-todo-state-map "g"
	 #'(lambda nil (interactive) (org-agenda-todo "DELEGATED")))
       (define-key org-todo-state-map "n"
	 #'(lambda nil (interactive) (org-agenda-todo "NOTE")))
       (define-key org-todo-state-map "s"
	 #'(lambda nil (interactive) (org-agenda-todo "STARTED")))
       (define-key org-todo-state-map "t"
	 #'(lambda nil (interactive) (org-agenda-todo "TODO")))
       (define-key org-todo-state-map "w"
	 #'(lambda nil (interactive) (org-agenda-todo "WAITING")))
       (define-key org-todo-state-map "x"
	 #'(lambda nil (interactive) (org-agenda-todo "CANCELLED"))))))

;;;_* startup

;; Finally, load the server and show the current agenda

(add-hook 'after-init-hook
	  (function
	   (lambda ()
	     (org-agenda-list)
	     (org-resolve-clocks))))
(add-hook 'after-init-hook 'server-start)

;; .emacs.el ends here
