(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(Info-fit-frame-flag nil)
 '(after-save-hook
   (quote
    (executable-make-buffer-file-executable-if-script-p)))
 '(align-c++-modes
   (quote
    (csharp-mode c++-mode c-mode java-mode groovy-mode)))
 '(align-to-tab-stop nil)
 '(auto-compression-mode t nil
                         (jka-compr))
 '(auto-image-file-mode t)
 '(auto-save-interval 1024)
 '(backup-directory-alist
   (quote
    (("/Volumes/Files/" . "/Volumes/Files/.backups")
     (".*recentf.*" . "/tmp")
     (".*" . "~/.emacs.d/backups"))))
 '(backward-delete-char-untabify-method
   (quote untabify))
 '(bbdb-default-country "")
 '(bbdb-file "~/Documents/bbdb")
 '(bbdb-offer-save
   (quote savenoprompt))
 '(bbdb-use-pop-up nil)
 '(bbdb/mail-auto-create-p nil)
 '(bc-bookmark-file "~/.emacs.d/data/breadcrumb")
 '(bmkp-bmenu-state-file "~/.emacs.d/data/bmk-bmenu-state.el")
 '(bmkp-bmenu-commands-file "~/.emacs.d/data/bmk-bmenu-commands.el")
 '(bookmark-default-file "~/.emacs.d/data/emacs.bmk")
 '(bookmark-save-flag 1)
 '(browse-url-browser-function
   (quote
    ((".*" . browse-url-default-macosx-browser))))
 '(byte-compile-verbose nil)
 '(c-default-style
   (quote
    ((java-mode . "gnu")
     (awk-mode . "awk")
     (other . "gnu"))))
 '(clean-buffer-list-kill-never-buffer-names
   (quote
    ("*scratch*" "*Messages*" "*server*" "*Group*" "*Org Agenda*" "todo.txt")))
 '(clean-buffer-list-kill-never-regexps
   (quote
    ("^ \\*Minibuf-.*\\*$" "^\\*Summary" "^\\*Article" "^#")))
 '(clean-buffer-list-kill-regexps
   (quote
    (".*")))
 '(column-number-mode t)
 '(company-backends
   (quote
    (company-elisp company-nxml company-css
                   (company-gtags company-etags company-dabbrev-code company-keywords)
                   company-oddmuse company-files company-dabbrev)))
 '(company-idle-delay nil)
 '(compilation-scroll-output t)
 '(completion-ignored-extensions
   (quote
    (".svn/" "CVS/" ".o" "~" ".bin" ".lbin" ".so" ".a" ".ln" ".blg" ".bbl" ".elc" ".lof" ".glo" ".idx" ".lot" ".dvi" ".fmt" ".tfm" ".pdf" ".class" ".fas" ".lib" ".mem" ".x86f" ".sparcf" ".xfasl" ".fasl" ".ufsl" ".fsl" ".dxl" ".pfsl" ".dfsl" ".lo" ".la" ".gmo" ".mo" ".toc" ".aux" ".cp" ".fn" ".ky" ".pg" ".tp" ".vr" ".cps" ".fns" ".kys" ".pgs" ".tps" ".vrs" ".pyc" ".pyo")))
 '(current-language-environment "UTF-8")
 '(custom-buffer-done-function
   (quote kill-buffer))
 '(custom-file "/Users/johnw/.emacs.d/settings.el" t)
 '(custom-raised-buttons nil)
 '(default-frame-alist
    (quote
     ((font . "-apple-Courier-medium-normal-normal-*-15-*-*-*-m-0-iso10646-1")
      (cursor-color . "#b247ee"))))
 '(default-input-method "latin-1-prefix")
 '(default-major-mode
    (quote text-mode)
    t)
 '(delete-by-moving-to-trash t)
 '(delete-old-versions
   (quote none))
 '(directory-free-space-args "-kh")
 '(dired-clean-up-buffers-too nil)
 '(dired-dwim-target t)
 '(dired-guess-shell-gnutar "tar")
 '(dired-listing-switches "-lh")
 '(dired-load-hook
   (quote
    ((lambda nil
       (load "dired-x")))))
 '(dired-no-confirm
   (quote
    (byte-compile chgrp chmod chown copy hardlink symlink touch)))
 '(dired-omit-mode nil t)
 '(dired-recursive-copies
   (quote always))
 '(dired-recursive-deletes
   (quote always))
 '(display-time-mail-function
   (quote
    (lambda nil
      (file-exists-p "/tmp/unread"))))
 '(display-time-mode t)
 '(display-time-use-mail-icon t)
 '(ediff-diff-options "-w")
 '(ediff-highlight-all-diffs nil)
 '(ediff-window-setup-function
   (quote ediff-setup-windows-plain))
 '(edit-server-new-frame nil)
 '(emacs-lisp-mode-hook
   (quote
    (turn-on-auto-fill eldoc-mode
                       (lambda nil
                         (local-set-key
                          [(meta 46)]
                          (quote find-function))
                         (local-set-key
                          [(control 109)]
                          (quote newline-and-indent))))))
 '(enable-recursive-minibuffers t)
 '(erc-auto-query
   (quote window-noselect))
 '(erc-autoaway-message "I'm away (after %i seconds of idle-time)")
 '(erc-autoaway-mode t)
 '(erc-autojoin-channels-alist
   (quote
    (("localhost" "&bitlbee")
     ("freenode.net" "#ledger")
     ("irc.oftc.net" "#llvm"))))
 '(erc-autojoin-mode t)
 '(erc-generate-log-file-name-function
   (quote erc-generate-log-file-name-short))
 '(erc-header-line-format nil)
 '(erc-hide-list
   (quote
    ("JOIN" "NICK" "PART" "QUIT" "MODE")))
 '(erc-keywords
   (quote
    ("wiegley" "ledger" "eshell")))
 '(erc-log-channels-directory "~/Library/Mail/ERC")
 '(erc-log-write-after-send t)
 '(erc-modules
   (quote
    (autoaway autojoin button completion dcc fill identd irccontrols list log match menu move-to-prompt netsplit networks noncommands readonly replace ring scrolltobottom services smiley stamp spelling track)))
 '(erc-nick "johnw")
 '(erc-port 6667)
 '(erc-prompt-for-nickserv-password nil)
 '(erc-replace-alist
   (quote
    (("</?FONT>" . ""))))
 '(erc-server "irc.freenode.net")
 '(erc-services-mode t)
 '(erc-track-enable-keybindings t)
 '(erc-track-exclude-types
   (quote
    ("JOIN" "KICK" "NICK" "PART" "QUIT" "MODE" "333" "353")))
 '(erc-track-faces-priority-list
   (quote
    (erc-error-face
     (erc-nick-default-face erc-current-nick-face)
     erc-current-nick-face erc-keyword-face
     (erc-nick-default-face erc-pal-face)
     erc-pal-face erc-nick-msg-face erc-direct-msg-face)))
 '(erc-track-minor-mode t)
 '(erc-track-mode t)
 '(erc-user-full-name
   (quote user-full-name))
 '(eshell-directory-name "~/.emacs.d/eshell/")
 '(eshell-history-size 1000)
 '(eshell-ls-dired-initial-args
   (quote
    ("-h")))
 '(eshell-ls-exclude-regexp "~\\'")
 '(eshell-ls-initial-args "-h")
 '(eshell-modules-list
   (quote
    (eshell-alias eshell-basic eshell-cmpl eshell-dirs eshell-glob eshell-hist eshell-ls eshell-pred eshell-prompt eshell-rebind eshell-script eshell-smart eshell-term eshell-unix eshell-xtra)))
 '(eshell-prefer-to-shell t nil
                          (eshell))
 '(eshell-prompt-function
   (lambda nil
     (concat
      (abbreviate-file-name
       (eshell/pwd))
      (if
          (=
           (user-uid)
           0)
          " # " " $ "))))
 '(eshell-save-history-on-exit t)
 '(eshell-stringify-t nil)
 '(eshell-term-name "ansi")
 '(eshell-visual-commands
   (quote
    ("vi" "top" "screen" "less" "lynx" "ssh" "rlogin" "telnet")))
 '(eval-expr-print-function
   (quote pp)
   t)
 '(exec-path
   (quote
    ("/Applications/Misc/Emacs.app/Contents/MacOS/bin" "/Users/johnw/bin" "/usr/local/bin" "/opt/local/libexec/git-core" "/opt/local/bin" "/usr/bin" "/bin" "/usr/local/sbin" "/opt/local/sbin" "/usr/sbin" "/sbin" "/usr/X11R6/bin")))
 '(fill-column 78)
 '(find-directory-functions
   (quote
    (dired-noselect)))
 '(find-ls-option
   (quote
    ("-print0 | xargs -0 gls -ld" . "-ld")))
 '(find-ls-subdir-switches "-alh")
 '(flyspell-abbrev-p nil)
 '(flyspell-incorrect-hook
   (quote
    (flyspell-maybe-correct-transposition)))
 '(font-lock-support-mode
   (quote jit-lock-mode))
 '(font-lock-verbose nil)
 '(frame-title-format
   (quote
    (:eval
     (concat
      (if buffer-file-name default-directory "%b")
      "    "
      (number-to-string
       (cdr
        (assq
         (quote width)
         (frame-parameters))))
      "x"
      (number-to-string
       (cdr
        (assq
         (quote height)
         (frame-parameters)))))))
   t)
 '(global-auto-revert-mode t)
 '(global-font-lock-mode t nil
                         (font-lock))
 '(grep-command "grep -nH -e")
 '(grep-find-command
   (quote
    ("find . -type f -print0 | xargs -0 egrep -nH -e " . 48)))
 '(grepp-default-regexp-fn nil)
 '(haskell-check-command "~/.cabal/bin/hlint")
 '(haskell-mode-hook
   (quote
    (turn-on-haskell-indentation turn-on-font-lock turn-on-eldoc-mode turn-on-haskell-doc-mode turn-on-haskell-decl-scan my-haskell-mode-hook)))
 '(haskell-program-name "ghci")
 '(haskell-saved-check-command "~/.cabal/bin/hlint" t)
 '(howm-directory "~/Documents/Notes/")
 '(howm-history-file "~/.emacs.d/data/howm-history")
 '(howm-keyword-file "~/.emacs.d/data/howm-keys")
 '(howm-view-use-grep t)
 '(ibuffer-expert t)
 '(ibuffer-formats
   (quote
    ((mark modified read-only " "
           (name 16 -1)
           " "
           (size 6 -1 :right)
           " "
           (mode 16 16)
           " " filename)
     (mark " "
           (name 16 -1)
           " " filename))))
 '(ibuffer-maybe-show-regexps nil)
 '(ibuffer-shrink-to-minimum-size t t)
 '(ibuffer-use-other-window t)
 '(ido-auto-merge-work-directories-length 0)
 '(ido-cannot-complete-command
   (quote ido-exit-minibuffer))
 '(ido-decorations
   (quote
    ("{" "}" "," ",..." "[" "]" " [No match]" " [Matched]" " [Not readable]" " [Too big]" " [Confirm]")))
 '(ido-enable-flex-matching t)
 '(ido-enable-last-directory-history nil)
 '(ido-enable-tramp-completion nil)
 '(ido-enter-matching-directory
   (quote first))
 '(ido-gather-virtual-filenames
   (quote
    (ido-gather-recent-files ido-gather-git-project-files)))
 '(ido-ignore-files
   (quote
    ("\\`CVS/" "\\`#" "\\`.#" "\\`\\.\\./" "\\`\\./" "\\`\\.DS_Store" "\\`\\.localized" "\\.sparsebundle/" "\\.dmg\\'")))
 '(ido-mode
   (quote both)
   nil
   (ido))
 '(ido-save-directory-list-file "~/.emacs.d/data/ido.last")
 '(ido-use-virtual-buffers t)
 '(indent-tabs-mode nil)
 '(inhibit-startup-echo-area-message "johnw")
 '(inhibit-startup-screen t)
 '(ispell-extra-args
   (quote
    ("--sug-mode=fast" "--keyboard=dvorak")))
 '(kill-whole-line t)
 '(large-file-warning-threshold nil)
 '(ledger-file "~/Documents/Accounts/ledger.dat")
 '(ledger-post-use-ido t)
 '(line-number-mode t)
 '(mac-option-modifier
   (quote alt))
 '(mac-pass-command-to-system nil)
 '(mac-pass-control-to-system nil)
 '(magit-process-popup-time 15)
 '(modelinepos-column-limit 80)
 '(next-line-add-newlines nil)
 '(ns-alternate-modifier
   (quote alt))
 '(ns-command-modifier
   (quote meta))
 '(nxml-sexp-element-flag t)
 '(nxml-slash-auto-complete-flag t)
 '(parens-require-spaces t)
 '(pcomplete-compare-entries-function
   (quote file-newer-than-file-p))
 '(pp^L-^L-string "                                                                              ")
 '(pretty-control-l-mode t)
 '(ps-font-size
   (quote
    (8 . 10)))
 '(ps-footer-font-size
   (quote
    (12 . 14)))
 '(ps-header-font-size
   (quote
    (12 . 14)))
 '(ps-header-title-font-size
   (quote
    (14 . 16)))
 '(ps-line-number-font-size 10)
 '(ps-print-color-p nil)
 '(read-buffer-function
   (quote ido-read-buffer))
 '(recentf-exclude
   (quote
    ("~\\'" "\\`out\\'" "\\.log\\'" "^/[^/]*:")))
 '(recentf-max-saved-items 200)
 '(recentf-mode t)
 '(recentf-save-file "~/.emacs.d/data/recentf")
 '(regex-tool-backend
   (quote perl))
 '(safe-local-variable-values
   (quote
    ((after-save-hook archive-done-tasks)
     (after-save-hook sort-done-tasks)
     (after-save-hook commit-after-save)
     (after-save-hook . byte-compile-file-after-save))))
 '(session-globals-exclude
   (quote
    (load-history flyspell-auto-correct-ring)))
 '(session-registers
   (quote
    (t
     (0 . 127))))
 '(session-save-file "~/.emacs.d/data/session")
 '(session-use-package t nil
                       (session))
 '(show-paren-delay 0)
 '(show-paren-mode
   (quote paren))
 '(slime-kill-without-query-p t)
 '(slime-repl-history-file "~/.emacs.d/data/slime-history.eld")
 '(slime-startup-animation nil)
 '(special-display-regexps
   (quote
    (("\\*compilation\\*"
      (width . 80)
      (height . 60)))))
 '(sql-sqlite-program "sqlite3")
 '(ssl-certificate-verification-policy 1)
 '(svn-status-hide-unmodified t)
 '(tags-apropos-verbose t)
 '(tags-case-fold-search nil)
 '(temp-buffer-resize-mode t nil
                           (help))
 '(text-mode-hook
   (quote
    (turn-on-auto-fill)))
 '(tool-bar-mode nil)
 '(tramp-auto-save-directory "~/.emacs.d/backups")
 '(tramp-default-method "rsyncc")
 '(tramp-default-method-alist
   (quote
    (("\\`\\(127\\.0\\.0\\.1\\|::1\\|localhost6?\\)\\'" "\\`root\\'" "sudo"))))
 '(tramp-persistency-file-name "~/.emacs.d/data/tramp")
 '(trash-directory "~/.Trash")
 '(uniquify-buffer-name-style
   (quote post-forward-angle-brackets)
   nil
   (uniquify))
 '(user-full-name "John Wiegley")
 '(user-initials "jww")
 '(user-mail-address "jwiegley@gmail.com")
 '(vc-follow-symlinks t)
 '(vc-handled-backends
   (quote
    (Git Bzr Hg)))
 '(version-control t)
 '(visible-bell t)
 '(w3m-use-cookies t)
 '(wdired-use-dired-vertical-movement
   (quote sometimes))
 '(whitespace-action
   (quote
    (auto-cleanup)))
 '(whitespace-auto-cleanup t)
 '(whitespace-global-modes nil)
 '(whitespace-rescan-timer-time nil)
 '(whitespace-silent t)
 '(winner-mode t nil
               (winner))
 '(x-select-enable-clipboard t)
 '(x-stretch-cursor t)
 '(yaoddmuse-directory "~/.emacs.d/doc")
 '(zencoding-preview-default nil))

(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(diff-added
   ((t
     (:foreground "DarkGreen"))))
 '(diff-added2
   ((t
     (:foreground "SeaGreen"))))
 '(diff-changed
   ((t
     (:foreground "MediumBlue"))))
 '(diff-context
   ((t
     (:foreground "Black"))))
 '(diff-file-header
   ((t
     (:foreground "White" :background "Gray50"))))
 '(diff-header
   ((t
     (:foreground "Blue"))))
 '(diff-hunk-header
   ((t
     (:foreground "Salmon" :background "Gray90"))))
 '(diff-index
   ((t
     (:foreground "Green"))))
 '(diff-nonexistent
   ((t
     (:foreground "DarkBlue"))))
 '(diff-removed
   ((t
     (:foreground "Red"))))
 '(diff-removed2
   ((t
     (:foreground "Orange"))))
 '(font-lock-comment-face
   ((((class color))
     (:foreground "firebrick"))))
 '(ledger-register-pending-face
   ((t
     (:weight bold))))
 '(magit-branch-face
   ((((class color)
      (background light))
     (:foreground "Blue"))))
 '(magit-diff-none-face
   ((((class color)
      (background light))
     (:foreground "grey50"))))
 '(magit-header
   ((t
     (:weight bold))))
 '(magit-topgit-current
   ((t nil)))
 '(match
   ((t
     (:background "light cyan"))))
 '(slime-highlight-edits-face
   ((((class color)
      (background light))
     (:background "gray98"))))
 '(trailing-whitespace
   ((((class color)
      (background light))
     (:background "light salmon")))))

