;;; -*- mode: emacs-lisp -*-

;;;_* initial packages

;; Add other site-lisp directories, in case they were not setup by the
;; environment.

(dolist
    (path
     (reverse
      (list (expand-file-name "~/Library/Emacs")
	    (expand-file-name "/opt/local/share/doc/git-core/contrib/emacs")
	    ;;(expand-file-name "~/Archives/Git/Sources/git/contrib/emacs")
	    ;;(expand-file-name "~/Sources/puppet/ext/emacs")
	    (expand-file-name "~/src/emacs-chess")
	    (expand-file-name "~/src/eshell")
	    (expand-file-name "~/src/pcomplete")
	    (expand-file-name "~/src/magit")
	    (expand-file-name "~/src/regex-tool")
	    (expand-file-name "~/Library/Emacs/site-lisp/circe")
	    (expand-file-name "~/Library/Emacs/site-lisp/nxml-mode")
	    (expand-file-name "~/Library/Emacs/site-lisp/org-mode/lisp")
	    (expand-file-name "~/Library/Emacs/site-lisp/org-mode/contrib/lisp")
	    (expand-file-name "~/Library/Emacs/site-lisp/remember")
	    (expand-file-name "~/Library/Emacs/site-lisp/yasnippet")
	    (expand-file-name "/usr/local/share/emacs/site-lisp"))))

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

;; Monument
;; '(calendar-latitude [39 3 north])
;; '(calendar-longitude [104 49 west])

;; '(eshell-ls-use-in-dired t nil (em-ls))
;; '(abbrev-mode t)
;; '(sendmail-program "/opt/local/bin/msmtp" t)
;; '(allout-command-prefix "")
;; '(ange-ftp-try-passive-mode t)

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
 '(backup-directory-alist (quote (("/CEG/" . "/Volumes/CEG/.backups") ("/TI/" . "/Volumes/TI/.backups") ("/Files/" . "/Volumes/Files/.backups") (".*" . "~/.emacs.d/backups"))))
 '(backward-delete-char-untabify-method (quote untabify))
 '(bookmark-save-flag 1)
 '(browse-url-browser-function (quote (("\\.\\(gz\\|tgz\\|bz2\\|tbz\\|dmg\\|iso\\|pdf\\|mp3\\)\\'" . browse-url-download-file) (".*" . browse-url-default-macosx-browser))))
 '(c-default-style (quote ((java-mode . "gnu") (awk-mode . "awk") (other . "gnu"))))
 '(calendar-latitude [12 1 north])
 '(calendar-longitude [61 46 west])
 '(circe-fools-list (quote ("Xach" "Xof" "Krystof" "Zhivago" "dalias" "holycow")))
 '(circe-ignore-list (quote ("jordanb_?")))
 '(clean-buffer-list-kill-regexps (quote (".*")))
 '(column-number-mode nil)
 '(compilation-scroll-output t)
 '(completion-ignored-extensions (quote (".svn/" "CVS/" ".o" "~" ".bin" ".lbin" ".so" ".a" ".ln" ".blg" ".bbl" ".elc" ".lof" ".glo" ".idx" ".lot" ".dvi" ".fmt" ".tfm" ".pdf" ".class" ".fas" ".lib" ".mem" ".x86f" ".sparcf" ".xfasl" ".fasl" ".ufsl" ".fsl" ".dxl" ".pfsl" ".dfsl" ".lo" ".la" ".gmo" ".mo" ".toc" ".aux" ".cp" ".fn" ".ky" ".pg" ".tp" ".vr" ".cps" ".fns" ".kys" ".pgs" ".tps" ".vrs" ".pyc" ".pyo")))
 '(custom-buffer-done-function (quote kill-buffer))
 '(custom-raised-buttons nil)
 '(default-frame-alist (quote ((font . "-apple-courier-medium-r-normal--15-0-72-72-m-0-iso10646-1") (cursor-color . "red"))))
 '(default-input-method "latin-1-prefix")
 '(default-major-mode (quote fundamental-mode))
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
 '(emacs-lisp-mode-hook (quote (turn-on-auto-fill eldoc-mode (lambda nil (local-set-key [(meta 46)] (quote find-function)) (local-set-key [(control 109)] (quote newline-and-indent))))))
 '(enable-recursive-minibuffers t)
 '(eshell-history-size 1000)
 '(eshell-ls-dired-initial-args (quote ("-h")))
 '(eshell-ls-exclude-regexp "~\\'")
 '(eshell-ls-initial-args "-h")
 '(eshell-modules-list (quote (eshell-alias eshell-basic eshell-cmpl eshell-dirs eshell-glob eshell-hist eshell-ls eshell-pred eshell-prompt eshell-rebind eshell-script eshell-smart eshell-term eshell-unix eshell-xtra)))
 '(eshell-prefer-to-shell t nil (eshell))
 '(eshell-save-history-on-exit t)
 '(eshell-stringify-t nil)
 '(eshell-term-name "ansi")
 '(eshell-visual-commands (quote ("vi" "top" "screen" "less" "lynx" "ssh" "rlogin" "telnet")))
 '(eval-expr-print-function (quote pp) t)
 '(fill-column 78)
 '(flyspell-abbrev-p nil)
 '(flyspell-incorrect-hook (quote (flyspell-maybe-correct-transposition)))
 '(font-lock-support-mode (quote jit-lock-mode))
 '(frame-title-format (quote (:eval (if buffer-file-name default-directory "%b"))) t)
 '(global-auto-revert-mode t)
 '(global-font-lock-mode t nil (font-lock))
 '(ibuffer-expert t)
 '(ibuffer-formats (quote ((mark modified read-only " " (name 16 -1) " " (size 6 -1 :right) " " (mode 16 16) " " filename) (mark " " (name 16 -1) " " filename))))
 '(ibuffer-maybe-show-regexps nil)
 '(ibuffer-shrink-to-minimum-size t t)
 '(ibuffer-use-other-window t)
 '(inhibit-startup-echo-area-message "johnw")
 '(inhibit-startup-screen t)
 '(initial-frame-alist (quote ((top . 25) (left . 520) (width . 100) (height . 50))))
 '(initsplit-customizations-alist (quote (("^\\(canlock\\|eudc\\|spam\\|nnmail\\|nndraft\\|mm\\|message\\|mail\\|gnus\\|check-mail\\)-" "~/Library/Emacs/.gnus.el" nil))))
 '(iswitchb-max-to-show 10)
 '(iswitchb-mode t)
 '(iswitchb-use-frame-buffer-list t)
 '(iswitchb-use-virtual-buffers t nil (recentf))
 '(kill-whole-line t)
 '(large-file-warning-threshold nil)
 '(ledger-file "/Volumes/Files/ledger.dat")
 '(line-number-mode t)
 '(lui-time-stamp-position nil)
 '(mac-pass-command-to-system nil)
 '(mac-pass-control-to-system nil)
 '(mark-holidays-in-calendar t)
 ;;'(menu-bar-mode nil nil (menu-bar))
 '(next-line-add-newlines nil)
 '(nxml-sexp-element-flag t)
 '(nxml-slash-auto-complete-flag t)
 '(org-M-RET-may-split-line (quote ((headline) (default . t))))
 '(org-agenda-custom-commands (quote (("d" todo #("DELEGATED" 0 9 (face org-warning)) nil) ("c" todo #("DONE|DEFERRED|CANCELLED" 0 23 (face org-warning)) ((org-agenda-files (cons "~/Documents/archive.txt" org-agenda-files)))) ("w" todo #("WAITING" 0 7 (face org-warning)) nil) ("W" agenda "" ((org-agenda-ndays 21))) ("N" alltodo "" ((org-agenda-skip-function (lambda nil (org-agenda-skip-entry-if (quote regexp) "\\=.*\\[#[ABC]\\]"))) (org-agenda-overriding-header "Tasks without any priority: "))) ("A" agenda "" ((org-agenda-skip-function (lambda nil (org-agenda-skip-entry-if (quote notregexp) "\\=.*\\[#A\\]"))) (org-agenda-ndays 1) (org-agenda-overriding-header "Today's Priority #A tasks: "))) ("B" agenda "" ((org-agenda-skip-function (lambda nil (org-agenda-skip-entry-if (quote regexp) "\\=.*\\[#C\\]"))) (org-agenda-ndays 1) (org-agenda-overriding-header "Today's Priority #A and #B tasks: "))) ("u" alltodo "" ((org-agenda-skip-function (lambda nil (org-agenda-skip-entry-if (quote scheduled) (quote deadline) (quote regexp) "<[0-9-]\\{10\\} [^>
]+>"))) (org-agenda-overriding-header "Unscheduled TODO entries: "))))))
 '(org-agenda-deadline-leaders (quote ("D: " "D%d: ")))
 '(org-agenda-deadline-relative-text "D%d: ")
 '(org-agenda-deadline-text "D: ")
 '(org-agenda-default-appointment-duration 60)
 '(org-agenda-files (quote ("~/Documents/todo.txt")))
 '(org-agenda-ndays 7)
 '(org-agenda-prefix-format (quote ((agenda . "  %-11:c%?-12t% s") (timeline . "  % s") (todo . "  %-11:c") (tags . "  %-11:c"))))
 '(org-agenda-scheduled-leaders (quote ("" "S%d: ")))
 '(org-agenda-scheduled-relative-text "S%d: ")
 '(org-agenda-scheduled-text "")
 '(org-agenda-show-all-dates t)
 '(org-agenda-skip-deadline-if-done t)
 '(org-agenda-skip-scheduled-if-done t)
 '(org-agenda-skip-unavailable-files t)
 '(org-agenda-sorting-strategy (quote ((agenda time-up priority-down) (todo category-keep priority-down) (tags category-keep priority-down))))
 '(org-agenda-start-on-weekday nil)
 '(org-agenda-tags-column -100)
 '(org-agenda-text-search-extra-files (quote (agenda-archives)))
 '(org-archive-location "TODO-archive::")
 '(org-archive-save-context-info (quote (time category itags)))
 '(org-cycle-global-at-bob t)
 '(org-deadline-warning-days 14)
 '(org-default-notes-file "~/Documents/todo.txt")
 '(org-directory "~/Documents/")
 '(org-drawers (quote ("PROPERTIES" "OUTPUT" "SCRIPT" "PATCH" "DATA")))
 '(org-extend-today-until 8)
 '(org-fast-tag-selection-single-key (quote expert))
 '(org-hide-leading-stars t)
 '(org-modules (quote (org-mac-message org-bookmark org-depend org-eval org2rem)))
 '(org-remember-store-without-prompt t)
 '(org-remember-templates (quote (("Task" 116 "* TODO %?
  SCHEDULED: %t
  :PROPERTIES:
  :ID: %(shell-command-to-string \"uuidgen\")  :END:
  %U" nil "Inbox" nil))))
 '(org-reverse-note-order t)
 '(org-stuck-projects (quote ("+LEVEL=1/-DONE" ("TODO" "STARTED" "NEXT" "NEXTACTION") nil "\\(Appointments\\|Notes\\|Anniversaries\\)")))
 '(org-tag-alist (quote ((#("NASIM" 0 5 (face nil)) . 110) (#("WORK" 0 4 (face nil)) . 119))))
 '(org-tags-column -97)
 '(org-todo-keyword-faces (quote (("TODO" :foreground "medium blue" :weight bold) ("APPT" :foreground "medium blue" :weight bold) ("NOTE" :foreground "dark violet" :weight bold) ("STARTED" :foreground "dark orange" :weight bold) ("WAITING" :foreground "red" :weight bold) ("DELEGATED" :foreground "red" :weight bold))))
 '(org-todo-keywords (quote ((sequence "TODO" "APPT" "|" "DONE" "NOTE"))))
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
 '(read-buffer-function (quote iswitchb-read-buffer))
 '(recentf-auto-cleanup 600)
 '(recentf-exclude (quote ("~\\'" "\\`out\\'" "\\.log\\'" "^/[^/]*:")))
 '(recentf-max-saved-items 200)
 '(recentf-mode t)
 '(regex-tool-backend (quote perl))
 '(remember-annotation-functions (quote (org-remember-annotation)))
 '(remember-handler-functions (quote (org-remember-handler)))
 '(require-final-newline t)
 '(safe-local-variable-values (quote ((after-save-hook archive-done-tasks) (after-save-hook sort-done-tasks) (after-save-hook commit-after-save))))
 '(scroll-bar-mode nil)
 '(session-globals-exclude (quote (load-history flyspell-auto-correct-ring)))
 '(session-registers (quote (t (0 . 127))))
 '(show-paren-delay 0)
 '(show-paren-mode (quote paren))
 '(slime-kill-without-query-p t)
 '(slime-startup-animation nil)
 '(special-display-regexps (quote (("#\\(ledger\\)" (menu-bar-lines . 0) (tool-bar-lines . 0) (vertical-scroll-bars) (font . "-apple-lucida grande-medium-r-normal--16-0-72-72-m-0-iso10646-1") (top . 295) (left . 2) (width . 80) (height . 34) (alpha . 0.5) (splittable . t) (unsplittable) (dedicated)))))
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
 '(user-mail-address "johnw@newartisans.com")
 '(vc-follow-symlinks t)
 '(vc-handled-backends (quote (GIT)))
 '(version-control t)
 '(visible-bell t)
 '(whitespace-auto-cleanup t)
 '(whitespace-rescan-timer-time nil)
 '(whitespace-silent t)
 '(winner-mode t nil (winner))
 '(x-select-enable-clipboard t)
 '(x-stretch-cursor t))

;;;_ * faces

(custom-set-faces
  ;; custom-set-faces was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 '(circe-highlight-all-nicks-face ((t (:foreground "dark blue"))))
 '(circe-originator-face ((t (:foreground "dark orange"))))
 '(font-lock-comment-face ((((class color)) (:foreground "firebrick"))))
 '(magit-branch-face ((((class color) (background light)) (:foreground "Blue"))))
 '(magit-diff-none-face ((((class color) (background light)) (:foreground "grey50"))))
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

;;;_ * abbrev

;;(if (file-exists-p abbrev-file-name)
;;    (quietly-read-abbrev-file))

;;;_ * anything

;;(autoload 'anything "anything" nil t)

;;;_ * browse-kill-ring

(when (load "browse-kill-ring" t)
  (browse-kill-ring-default-keybindings))

;;;_ * browse-url

(if (file-executable-p "~/bin/sdcli")
    (defun browse-url-download-file (url &optional new-window)
      (call-process (expand-file-name "~/bin/sdcli") nil nil nil "dl" url)))

;;;_ * cc-mode

(eval-when-compile
  (defvar c-mode-base-map))

(defun my-c-mode-common-hook ()
  (doxymacs-mode)
  (define-key c-mode-base-map "\C-m" 'newline-and-indent)
  (set (make-local-variable 'parens-require-spaces) nil)
  (setq indicate-empty-lines t)
  (setq fill-column 72)
  (font-lock-add-keywords
   'c++-mode '(("\\<\\(assert\\|DEBUG\\)(" 1 widget-inactive t))))

(which-function-mode t)

(add-hook 'c-mode-common-hook 'my-c-mode-common-hook)

;;;_ * chess

(load "chess-auto" t)

;;;_ * circe

(autoload 'circe "circe" "Connect to an IRC server" t)

(setq circe-default-realname "http://www.newartisans.com/"
      circe-server-coding-system '(utf-8 . undecided)
      circe-server-auto-join-channels '(("^freenode$" "#ledger"))
      circe-nickserv-passwords '(("freenode" "xco8imer")))

(setq lui-max-buffer-size 30000
      lui-flyspell-p nil
      lui-flyspell-alist '(("." "american")))

(eval-after-load "circe"
  '(progn
     (require 'circe-highlight-all-nicks)
     (enable-circe-highlight-all-nicks)

     (add-to-list 'circe-receive-message-functions 'nickserv-auth)))

(eval-after-load "lui"
  '(progn
     (require 'lui-irc-colors)
     (add-to-list 'lui-pre-output-hook 'lui-irc-colors)
     (add-to-list 'lui-post-output-hook 'lui-hide-joins-and-quits)
     (add-to-list 'lui-post-output-hook 'circe-thou-art-but-a-fool-sir)))

(defun lui-hide-joins-and-quits ()
  "Mark joins and quits with the `fool' property.
This is an appropriate function for `lui-pre-output-hook'."
  (goto-char (point-min))
  (let ((inhibit-read-only t))
    (while (re-search-forward "^\\*\\*\\* \\(Join\\|Quit\\|Part\\|Nick change\\)" nil t)
      (let ((start (match-beginning 0)))
	(save-excursion
	  (goto-char start)
	  (forward-line 1)
	  (while (and (not (eobp)) (looking-at "    "))
	    (forward-line 1))
	  (delete-region start (point)))))))

(defcustom circe-fools-list nil
  "*List of nicks to mark as fools."
  :type '(repeat regexp)
  :group 'circe)

(defun circe-command-FOOL (line)
  "Add the regex on LINE to the `circe-fools-list'."
  (with-current-buffer (circe-server-last-active-buffer)
    (cond
     ((string-match "\\S-+" line)
      (let ((regex (match-string 0 line)))
        (add-to-list 'circe-fools-list regex)
        (circe-server-message
	 (format "Fools list, meet %s (for now)" regex))))
     ((not circe-fools-list)
      (circe-server-message "Your fools list is empty"))
     (t
      (circe-server-message "Your fools list:")
      (mapc (lambda (regex)
              (circe-server-message (format "- %s" regex)))
            circe-fools-list)))))

(defun circe-command-UNFOOL (line)
  "Remove an entry from `circe-fools-list'."
  (with-current-buffer (circe-server-last-active-buffer)
    (cond
     ((string-match "\\S-+" line)
      (let ((regex (match-string 0 line)))
        (setq circe-fools-list (delete regex circe-fools-list))
        (circe-server-message (format "Fools list forgot about %s" regex))))
     (t
      (circe-server-message
       "Who do you want to unfool? UNFOOL requires one argument")))))

(defun circe-thou-art-but-a-fool-sir ()
  (goto-char (point-min))
  (let ((inhibit-read-only t))
    (while (re-search-forward "^<\\([^>]+\\)>" nil t)
      (let ((start (match-beginning 0))
	    (nick (match-string 1))
	    a-foolish-boy-p)
	(if (dolist (regex circe-fools-list)
	      (if (string-match regex nick)
		  (return t)))
	    (save-excursion
	      (goto-char start)
	      (forward-line 1)
	      (while (and (not (eobp)) (looking-at " "))
		(forward-line 1))
	      (put-text-property start (point) 'lui-fool t)))))))

(defun nickserv-auth (nick user host command args)
  "Authenticate to a bitlbee server."
  (when (and (string= command "JOIN")
             (circe-server-my-nick-p nick))
    (with-circe-server-buffer
      (when (string= circe-server-network "irc.freenode.net")
        (circe-server-send "PRIVMSG NickServ IDENTIFY xco8imer")))))

(defun irc ()
  "Connect to IRC."
  (interactive)
  (circe "irc.freenode.net" "6667" "freenode"))

;;;_ * csharp-mode

(autoload 'csharp-mode "csharp-mode" nil t)

(add-to-list 'auto-mode-alist '("\\.cs\\'" . csharp-mode))

(defun my-csharp-mode-hook ()
  (set (make-local-variable 'parens-require-spaces) nil)
  (setq tab-width 8 c-basic-offset 2)
  (setq fill-column (- (window-width) 8)))

(add-hook 'csharp-mode-hook 'my-csharp-mode-hook)

(eval-after-load "whitespace"
  '(add-to-list 'whitespace-modes 'csharp-mode))

(add-to-list 'auto-mode-alist '("\\.as[cphma]x\\'" . html-mode))
(add-to-list 'auto-mode-alist '("\\.master\\'" . html-mode))
(add-to-list 'auto-mode-alist '("\\.css\\'" . css-mode))

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

;;;_ * eval-expr

(when (load "eval-expr" t)
  (eval-expr-install))

;;;_ * flyspell

(load "flyspell-ext" t)

;;;_ * git

(setenv "GIT_PAGER" "")

(require 'magit)
(require 'git)
(require 'gitsum)
(require 'vc-git)

(autoload 'git-blame-mode "git-blame"
  "Minor mode for incremental blame for Git." t)

(add-to-list 'vc-handled-backends 'GIT)

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

(autoload 'groovy-mode "groovy-mode" "" t)

(add-to-list 'interpreter-mode-alist '("groovy" . groovy-mode))
(add-to-list 'auto-mode-alist '("\\.groovy\\'" . groovy-mode))

;;;_ * initsplit

(load "initsplit" t)

;;;_ * java-mode

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

(add-hook 'java-mode-hook
	  #'(lambda ()
	      (c-set-style "ceg")
	      (setq tab-width 3)
	      (setq c-basic-offset 3)
	      (setq indent-tabs-mode t)
	      (set-fill-column 100)))

;;;_ * ledger

(load "~/src/ledger/lisp/ledger" t)

(eval-after-load "whitespace"
  '(add-to-list 'whitespace-modes 'ledger-mode))

;;;_ * mule

(prefer-coding-system 'utf-8)
(set-terminal-coding-system 'utf-8)
(setq x-select-request-type '(UTF8_STRING COMPOUND_TEXT TEXT STRING))

;;;_ * nxml-mode

(autoload 'nxml-mode "rng-auto" "" t)

(defalias 'xml-mode 'nxml-mode)

(defun my-nxml-mode-hook ()
  (define-key nxml-mode-map [return] 'newline-and-indent)
  (define-key nxml-mode-map [(control return)] 'other-window))

(add-hook 'nxml-mode-hook 'my-nxml-mode-hook)

;;;_ * objc++-mode

(add-to-list 'auto-mode-alist '("\\.h\\'" . c++-mode))
(add-to-list 'auto-mode-alist '("\\.m\\'" . c-mode))
(add-to-list 'auto-mode-alist '("\\.mm\\'" . c++-mode))

;;;_ * pcomplete

(autoload 'pcomplete/ssh "pcmpl-ssh")
(autoload 'pcomplete/scp "pcmpl-ssh")

;;;_ * puppet-mode

(autoload 'puppet-mode "puppet-mode" "Major mode for editing puppet manifests")

(add-to-list 'auto-mode-alist '("\\.pp$" . puppet-mode))

;;;_ * python-mode

(require 'python)

(defvar python-keywords-wanting-colon
  '("def" "class" "if" "elif" "while" "else" "with"
    "try" "except" "finally" "for" "lambda"))

(defvar python-kwc-regexp nil)

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
		  '("\\.py\\'" flymake-pylint-init))))

;;;_ * gnus

(setq gnus-home-directory "~/Documents")

(load ".gnus")

(defun gnus-visit-article ()
  (interactive)
  (when (string-match "\\`[0-9]+\\.msg\\'" (file-name-nondirectory buffer-file-name))
    (require 'gnus)
    (let* ((path buffer-file-name)
	   (article (file-name-sans-extension (file-name-nondirectory path)))
	   (dir (file-name-directory path))
	   (case-fold-search nil))
      (when (string-match "/Mail/\\(.+?\\)/$" dir)
	(let ((group (concat "nnml:" (match-string 1 dir))))
	  (setq group (subst-char-in-string ?/ ?. group))
	  (gnus-group-read-group 1 nil group)
	  (gnus-summary-goto-article (string-to-number article) nil t))))))

(add-hook 'find-file-hook 'gnus-visit-article t)

;;;_ * multi-region

(when (require 'multi-region nil t)
  (define-key mode-specific-map [?2] multi-region-map))

;;;_ * muse

(require 'muse-mode)
(require 'muse-html)
(require 'muse-markdown)

;;;_ * org-mode

(require 'org-install)
(require 'org-mac-message)
(require 'org-crypt)
(require 'org-attach)
(require 'org-devonthink)

(load "org-log" t)

(add-to-list 'auto-mode-alist '("\\.org$" . org-mode))

(eval-after-load "org"
  '(defvar org-agenda-last-files (cdr org-agenda-files)))

(defvar org-my-archive-expiry-days 7
  "The number of days after which a completed task should be auto-archived.
This can be 0 for immediate, or a floating point value.")

(defconst org-my-ts-regexp "[[<]\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} [^]>\r\n]*?\\)[]>]"
  "Regular expression for fast inactive time stamp matching.")

(defun org-my-archive-done-tasks ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((done-regexp
	   (concat "\\* \\(" (regexp-opt org-done-keywords) "\\) "))
	  (state-regexp
	   (concat "- State \"\\(?:" (regexp-opt org-done-keywords)
		   "\\)\"\\s-*\\[\\([^]\n]+\\)\\]"))
	  (inactive-regexp))
      (while (re-search-forward done-regexp nil t)
	(let ((end (save-excursion
		     (outline-next-heading)
		     (point)))
	      begin)
	  (goto-char (line-beginning-position))
	  (setq begin (point))
	  (if (or (re-search-forward state-regexp end t)
		  (re-search-forward org-my-ts-regexp end t))
	      (let* ((time-string (match-string 1))
		     (when-closed (org-parse-time-string time-string)))
		(if (>= (time-to-number-of-days
			 (time-subtract (current-time)
					(apply #'encode-time when-closed)))
			org-my-archive-expiry-days)
		    (org-archive-subtree)))
	    (goto-char end)))))
    (save-buffer)))

(defalias 'archive-done-tasks 'org-my-archive-done-tasks)

(defun org-get-inactive-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (when (re-search-backward org-my-ts-regexp begin t)
	(let ((time (float-time (org-time-string-to-time (match-string 0)))))
	  (assert (floatp time))
	  time)))))

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
	     '((110 "* DONE %?
  - State \"DONE\"       %U
  %u" "~/Documents/todo.txt" "Inbox"))))
	(org-remember)))))

(defun org-remember-note ()
  (interactive)
  (if (string= (buffer-name) "*Remember*")
      (call-interactively 'org-ctrl-c-ctrl-c)
    (let ((org-remember-templates
	   '((110 "* NOTE %?\n  %u" "~/Documents/todo.txt" "Inbox"))))
      (call-interactively 'org-remember))))

(defun org-insert-message-link ()
  (interactive)
  (let ((subject (do-applescript "tell application \"Mail\"
        set theMessages to selection
        subject of beginning of theMessages
end tell"))
        (message-id (do-applescript "tell application \"Mail\"
        set theMessages to selection
        message id of beginning of theMessages
end tell")))
    (insert (org-make-link-string
             (concat "message://"
                     (substring message-id 1 (1- (length message-id))))
             (substring subject 1 (1- (length subject)))))))

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

;;;_ * remember

(require 'remember)

(add-hook 'remember-mode-hook 'org-remember-apply-template)

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
  (yas/load-directory "~/Library/Emacs/site-lisp/yasnippet/snippets/"))

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

(define-key global-map [(control ?z)] 'collapse-or-expand)

(defun delete-indentation-forward ()
  (interactive)
  (delete-indentation t))

(define-key global-map [(meta ?j)] 'delete-indentation-forward)
(define-key global-map [(meta ?J)] 'delete-indentation)
(define-key global-map [(meta ?n)] 'chop-move-down)
(define-key global-map [(meta ?p)] 'chop-move-up)
(define-key global-map [(meta ?m)] 'org-maybe-remember)
(define-key global-map [(meta ?z)] 'org-remember-note)

(define-prefix-command 'lisp-find-map)
(define-key global-map [(control ?h) ?e] 'lisp-find-map)
(define-key lisp-find-map [?a] 'apropos)
(define-key lisp-find-map [?e] 'view-echo-area-messages)
(define-key lisp-find-map [?f] 'find-function)
(define-key lisp-find-map [?v] 'find-variable)
(define-key lisp-find-map [?k] 'find-function-on-key)

(define-key global-map [(meta ?C)] 'calendar)
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
(define-key global-map [(meta ?`)]  'other-frame)

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
(define-key global-map [(meta shift ?e)] 'mark-whole-buffer)

(define-key global-map [(control return)] 'other-window)

(define-key global-map [f5] 'gud-cont)
(define-key global-map [f10] 'gud-next)
(define-key global-map [f11] 'gud-step)
(define-key global-map [(shift f11)] 'gud-finish)

(define-key global-map [(alt tab)]
  #'(lambda ()
      (interactive)
      (call-interactively (key-binding (kbd "M-TAB")))))

;;;_ * ctl-x

(define-key ctl-x-map [?g] #'(lambda ()
			       (interactive)
			       (if current-prefix-arg
				   (call-interactively 'git-status)
				 (call-interactively 'magit-status))))

(define-key ctl-x-map [?d] 'delete-whitespace-rectangle)
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

(define-key ctl-x-map [(control ?f)] 'find-existing-file)

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
  (lisp-interaction-mode)
  (if current-prefix-arg
      (erase-buffer))
  (goto-char (point-max)))

(define-key mode-specific-map [?e ?s] 'scratch)
(define-key mode-specific-map [?e ?v] 'edit-variable)
(define-key mode-specific-map [?e ?e] 'toggle-debug-on-error)

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
(define-key mode-specific-map [?l] 'slime-selector)
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

(defun my-org-todo-search ()
  (interactive)
  (find-file-other-window "~/Documents/todo.txt")
  (goto-char (point-min))
  (call-interactively 'isearch-forward))

(defun my-org-todo-archive-search ()
  (interactive)
  (find-file-other-window "~/Documents/archive.txt")
  (goto-char (point-min))
  (call-interactively 'isearch-forward))

(define-key mode-specific-map [?t ?s] 'my-org-todo-search)
(define-key mode-specific-map [?t ?a] 'my-org-todo-archive-search)

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

(define-key mode-specific-map [?x ?l] 'org-insert-dtp-link)
(define-key mode-specific-map [?x ?m] 'org-insert-message-link)
(define-key mode-specific-map [?x ?C] 'cvs-examine)
(define-key mode-specific-map [?x ?S] 'svn-status)
(define-key mode-specific-map [?x ?M] 'org-dtp-message-open)

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

     (defun org-fit-agenda-window ()
       "Fit the window to the buffer size."
       (and (memq org-agenda-window-setup '(reorganize-frame))
	    (fboundp 'fit-window-to-buffer)
	    (fit-window-to-buffer)))))

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
       (define-key map " " 'org-agenda-tree-to-indirect-buffer)
       (define-key map "F" 'org-agenda-follow-mode)
       (define-key map [(meta ?p)] 'org-agenda-earlier)
       (define-key map [(meta ?n)] 'org-agenda-later)

       (define-prefix-command 'org-todo-state-map)

       (define-key map "x" 'org-todo-state-map)

       (define-key org-todo-state-map "x"
	 #'(lambda nil (interactive) (org-agenda-todo "CANCELLED")))
       (define-key org-todo-state-map "d"
	 #'(lambda nil (interactive) (org-agenda-todo "DONE")))
       (define-key org-todo-state-map "r"
	 #'(lambda nil (interactive) (org-agenda-todo "DEFERRED")))
       (define-key org-todo-state-map "g"
	 #'(lambda nil (interactive) (org-agenda-todo "DELEGATED")))
       (define-key org-todo-state-map "s"
	 #'(lambda nil (interactive) (org-agenda-todo "STARTED")))
       (define-key org-todo-state-map "t"
	 #'(lambda nil (interactive) (org-agenda-todo "TODO")))
       (define-key org-todo-state-map "w"
	 #'(lambda nil (interactive) (org-agenda-todo "WAITING"))))))

;;;_* startup

;; Finally, load the server and show the current agenda

(add-hook 'after-init-hook 'org-agenda-list)
(add-hook 'after-init-hook 'server-start)

;; .emacs.el ends here
