(defcustom dot-emacs-use-eglot nil
  "Non-nil if Eglot should be used rather than LSP."
  :type 'boolean)

(defconst emacs-start-time (current-time))

(defvar file-name-handler-alist-old file-name-handler-alist)

(setq package-enable-at-startup nil
      file-name-handler-alist nil
      message-log-max 16384
      gc-cons-threshold 402653184
      gc-cons-percentage 0.6
      auto-window-vscroll nil)

(add-hook 'after-init-hook
          `(lambda ()
             (setq file-name-handler-alist file-name-handler-alist-old
                   gc-cons-threshold 800000
                   gc-cons-percentage 0.1)
             (garbage-collect)) t)

;;; Functions

(eval-and-compile
  (defun emacs-path (path)
    (expand-file-name path user-emacs-directory))

  (defun lookup-password (host user port)
    (require 'auth-source)
    (require 'auth-source-pass)
    (let ((auth (auth-source-search :host host :user user :port port)))
      (if auth
          (let ((secretf (plist-get (car auth) :secret)))
            (if secretf
                (funcall secretf)
              (error "Auth entry for %s@%s:%s has no secret!"
                     user host port)))
        (error "No auth entry found for %s@%s:%s" user host port))))

  (defvar saved-window-configuration nil)

  (defun push-window-configuration ()
    (interactive)
    (push (current-window-configuration) saved-window-configuration))

  (defun pop-window-configuration ()
    (interactive)
    (let ((config (pop saved-window-configuration)))
      (if config
          (set-window-configuration config)
        (if (> (length (window-list)) 1)
            (delete-window)
          (bury-buffer)))))

  (defmacro atomic-modify-buffer (&rest body)
    `(let ((buf (current-buffer)))
       (save-window-excursion
         (with-temp-buffer
           (insert-buffer buf)
           ,@body
           (let ((temp-buf (current-buffer))
                 (inhibit-redisplay t))
             (with-current-buffer buf
               (let ((here (point)))
                 (save-excursion
                   (delete-region (point-min) (point-max))
                   (insert-buffer temp-buf))
                 (goto-char here)))))))))

;;; Environment

(eval-and-compile
  (defconst emacs-environment (getenv "NIX_MYENV_NAME"))

  (setq load-path
        (append '("~/.emacs.d")
                (delete-dups load-path)
                '("~/.emacs.d/lisp")))

  (defun filter (f args)
    (let (result)
      (dolist (arg args)
        (when (funcall f arg)
          (setq result (cons arg result))))
      (nreverse result)))

  (defun nix-read-environment (name)
    (ignore-errors
      (with-temp-buffer
        (insert-file-contents-literally
         (with-temp-buffer
           (insert-file-contents-literally
            (executable-find (concat "load-env-" name)))
           (and (re-search-forward "^source \\(.+\\)$" nil t)
                (match-string 1))))
        (and (or (re-search-forward "^  nativeBuildInputs=\"\\(.+?\\)\"" nil t)
                 (re-search-forward "^  buildInputs=\"\\(.+?\\)\"" nil t))
             (split-string (match-string 1))))))

  (add-to-list 'load-path "~/.emacs.d/lisp/use-package")
  (require 'use-package)

  (defconst load-path-reject-re "/\\.emacs\\.d/\\(lib\\|site-lisp\\)/"
    "Regexp matching `:load-path' values to be rejected.")

  (defun load-path-handler-override (orig-func name keyword args rest state)
    (if (cl-some (apply-partially #'string-match load-path-reject-re) args)
        (use-package-process-keywords name rest state)
      (let ((body (use-package-process-keywords name rest state)))
        (use-package-concat
         (mapcar #'(lambda (path)
                     `(eval-and-compile (add-to-list 'load-path ,path t)))
                 args)
         body))))

  (advice-add 'use-package-handler/:load-path
              :around #'load-path-handler-override)

  (if init-file-debug
      (setq use-package-verbose t
            use-package-expand-minimally nil
            use-package-compute-statistics t
            debug-on-error t)
    (setq use-package-verbose nil
          use-package-expand-minimally t)))

;;; Settings

(eval-and-compile
  (defconst emacs-data-suffix
    (cond ((string= "emacsERC" emacs-environment) "alt")
          ((string-match "emacs2[67]\\(.+\\)$" emacs-environment)
           (match-string 1 emacs-environment))))

  (defconst alternate-emacs (string= emacs-data-suffix "alt"))

  (defconst user-data-directory
    (emacs-path (if emacs-data-suffix
                    (format "data-%s" emacs-data-suffix)
                  "data")))

  (load (emacs-path "settings"))

  ;; Note that deferred loading may override some of these changed values.
  ;; This can happen with `savehist', for example.
  (when emacs-data-suffix
    (let ((settings (with-temp-buffer
                      (insert-file-contents (emacs-path "settings.el"))
                      (read (current-buffer)))))
      (pcase-dolist (`(quote (,var ,value . ,_)) (cdr settings))
        (when (and (stringp value)
                   (string-match "/\\.emacs\\.d/data" value))
          (set var (replace-regexp-in-string
                    "/\\.emacs\\.d/data"
                    (format "/.emacs.d/data-%s" emacs-data-suffix)
                    value)))))))

(defvar Info-directory-list
  (mapcar 'expand-file-name
          (append
           (mapcar (apply-partially #'expand-file-name "share/info")
                   (nix-read-environment emacs-environment))
           '("~/.local/share/info"
             "~/.nix-profile/share/info"))))

(setq disabled-command-function nil) ;; enable all commands

(eval-when-compile
  ;; Disable all warnings about obsolete functions here.
  (dolist (sym '(flet lisp-complete-symbol))
    (setplist sym (use-package-plist-delete (symbol-plist sym)
                                            'byte-obsolete-info))))

;;; Libraries

(use-package alert         :defer t  :load-path "lisp/alert")
(use-package anaphora      :defer t)
(use-package apiwrap       :defer t)
(use-package asoc          :defer t)
(use-package async         :defer t  :load-path "lisp/async")
(use-package button-lock   :defer t)
(use-package ctable        :defer t)
(use-package dash          :defer t)
(use-package deferred      :defer t)
(use-package diminish      :demand t)
(use-package el-mock       :defer t)
(use-package elisp-refs    :defer t)
(use-package epc           :defer t)
(use-package epl           :defer t)
(use-package esxml         :defer t)
(use-package f             :defer t)
(use-package fn            :defer t)
(use-package fringe-helper :defer t)
(use-package fuzzy         :defer t)

(use-package ghub
  :defer t
  :config
  (require 'auth-source-pass)
  (defvar my-ghub-token-cache nil)
  (advice-add
   'ghub--token :around
   #'(lambda (orig-func host username package &optional nocreate forge)
       (or my-ghub-token-cache
           (setq my-ghub-token-cache
                 (funcall orig-func host username package nocreate forge))))))

(use-package ghub+         :defer t)
(use-package ht            :defer t)
(use-package kv            :defer t)
(use-package list-utils    :defer t)
(use-package logito        :defer t)
(use-package loop          :defer t)
(use-package m-buffer      :defer t)
(use-package makey         :defer t)
(use-package marshal       :defer t)
(use-package names         :defer t)
(use-package noflet        :defer t)
(use-package oauth2        :defer t)
(use-package ov            :defer t)
(use-package packed        :defer t)
(use-package parent-mode   :defer t)
(use-package parsebib      :defer t)
(use-package parsec        :defer t)
(use-package peval         :defer t)
(use-package pfuture       :defer t)
(use-package pkg-info      :defer t)
(use-package popup         :defer t)
(use-package popup-pos-tip :defer t)
(use-package popwin        :defer t)
(use-package pos-tip       :defer t)
(use-package request       :defer t)
(use-package rich-minority :defer t)
(use-package s             :defer t)
(use-package simple-httpd  :defer t)
(use-package spinner       :defer t)
(use-package tablist       :defer t)
(use-package uuidgen       :defer t)
(use-package web           :defer t)
(use-package web-server    :defer t)
(use-package websocket     :defer t)
(use-package with-editor   :defer t)
(use-package xml-rpc       :defer t)
(use-package zoutline      :defer t)

;;; Keymaps

(define-key input-decode-map [?\C-m] [C-m])

(eval-and-compile
  (mapc #'(lambda (entry)
            (define-prefix-command (cdr entry))
            (bind-key (car entry) (cdr entry)))
        '(("C-,"   . my-ctrl-comma-map)
          ("<C-m>" . my-ctrl-m-map)

          ("C-h e" . my-ctrl-h-e-map)
          ("C-h x" . my-ctrl-h-x-map)

          ("C-c b" . my-ctrl-c-b-map)
          ("C-c e" . my-ctrl-c-e-map)
          ("C-c m" . my-ctrl-c-m-map)
          ("C-c w" . my-ctrl-c-w-map)
          ("C-c y" . my-ctrl-c-y-map)
          ("C-c H" . my-ctrl-c-H-map)
          ("C-c N" . my-ctrl-c-N-map)
          ("C-c (" . my-ctrl-c-open-paren-map)
          ("C-c -" . my-ctrl-c-minus-map)
          ("C-c =" . my-ctrl-c-equals-map)
          ("C-c ." . my-ctrl-c-r-map)
          )))

;;; Packages

(use-package abbrev
  :defer 5
  :diminish
  :hook
  ((text-mode prog-mode erc-mode LaTeX-mode) . abbrev-mode)
  (expand-load
   . (lambda ()
       (add-hook 'expand-expand-hook #'indent-according-to-mode)
       (add-hook 'expand-jump-hook #'indent-according-to-mode)))
  :config
  (if (file-exists-p abbrev-file-name)
      (quietly-read-abbrev-file)))

(use-package ace-isearch
  :disabled t
  :config
  (global-ace-isearch-mode +1)
  (define-key isearch-mode-map (kbd "C-'") 'ace-isearch-jump-during-isearch)
  :custom
  (ace-isearch-input-length 7)
  (ace-isearch-jump-delay 0.25)
  (ace-isearch-function 'avy-goto-char)
  (ace-isearch-use-jump 'printing-char))

(use-package ace-jump-mode
  :defer t)

(use-package ace-link
  :disabled t
  :defer 10
  :bind ("C-c M-o" . ace-link-addr)
  :config
  (ace-link-setup-default)

  (add-hook 'org-mode-hook
            #'(lambda () (bind-key "C-c C-o" #'ace-link-org org-mode-map)))
  (add-hook 'gnus-summary-mode-hook
            #'(lambda () (bind-key "M-o" #'ace-link-gnus gnus-summary-mode-map)))
  (add-hook 'gnus-article-mode-hook
            #'(lambda () (bind-key "M-o" #'ace-link-gnus gnus-article-mode-map)))
  (add-hook 'ert-results-mode-hook
            #'(lambda () (bind-key "o" #'ace-link-help ert-results-mode-map)))
  (add-hook 'eww-mode-hook
            #'(lambda () (bind-key "f" #'ace-link-eww eww-mode-map))))

(use-package ace-mc
  :bind (("<C-m> h"   . ace-mc-add-multiple-cursors)
         ("<C-m> M-h" . ace-mc-add-single-cursor)))

(use-package ace-window
  :bind* ("<C-return>" . ace-window))

(use-package adoc-mode
  :mode "\\.adoc\\'"
  :config
  (add-hook 'adoc-mode-hook
            #'(lambda ()
                (auto-fill-mode 1)
                ;; (visual-line-mode 1)
                ;; (visual-fill-column-mode 1)
                )))

(use-package agda-input
  :demand t
  :config
  (setq-default default-input-method "Agda")
  ;; (dolist (hook '(minibuffer-setup-hook
  ;;                 fundamental-mode-hook
  ;;                 text-mode-hook
  ;;                 prog-mode-hook))
  ;;   (add-hook hook #'(lambda () (set-input-method "Agda"))))
  )

(use-package agda2-mode
  ;; This declaration depends on the load-path established by agda-input.
  :mode ("\\.agda\\'" "\\.lagda.md\\'")
  :bind (:map agda2-mode-map
              ("C-c C-i" . agda2-insert-helper-function))
  :preface
  (defun agda2-insert-helper-function (&optional prefix)
    (interactive "P")
    (let ((func-def (with-current-buffer "*Agda information*"
                      (buffer-string))))
      (save-excursion
        (forward-paragraph)
        (let ((name (car (split-string func-def " "))))
          (insert "  where\n    " func-def "    " name " x = ?\n")))))
  :init
  (advice-add 'agda2-mode
              :before #'direnv-update-directory-environment))

(use-package aggressive-indent
  :diminish
  :hook (emacs-lisp-mode . aggressive-indent-mode))

(use-package align
  :bind (("M-["   . align-code)
         ("C-c [" . align-regexp))
  :commands align
  :preface
  (defun align-code (beg end &optional arg)
    (interactive "rP")
    (if (null arg)
        (align beg end)
      (let ((end-mark (copy-marker end)))
        (indent-region beg end-mark nil)
        (align beg end-mark)))))

(use-package anki-editor
  :commands anki-editor-submit)

(use-package aria2
  :commands aria2-downloads-list)

(use-package ascii
  :bind ("C-c e A" . ascii-toggle)
  :commands (ascii-on ascii-off)
  :preface
  (defun ascii-toggle ()
    (interactive)
    (if ascii-display
        (ascii-off)
      (ascii-on))))

(use-package auctex
  :demand t
  :no-require t
  :mode ("\\.tex\\'" . TeX-latex-mode)
  :config
  (defun latex-help-get-cmd-alist ()    ;corrected version:
    "Scoop up the commands in the index of the latex info manual.
   The values are saved in `latex-help-cmd-alist' for speed."
    ;; mm, does it contain any cached entries
    (if (not (assoc "\\begin" latex-help-cmd-alist))
        (save-window-excursion
          (setq latex-help-cmd-alist nil)
          (Info-goto-node (concat latex-help-file "Command Index"))
          (goto-char (point-max))
          (while (re-search-backward "^\\* \\(.+\\): *\\(.+\\)\\." nil t)
            (let ((key (buffer-substring (match-beginning 1) (match-end 1)))
                  (value (buffer-substring (match-beginning 2)
                                           (match-end 2))))
              (add-to-list 'latex-help-cmd-alist (cons key value))))))
    latex-help-cmd-alist)

  (add-hook 'TeX-after-compilation-finished-functions
            #'TeX-revert-document-buffer))

(use-package auth-source-pass
  :config
  (auth-source-pass-enable)

  (defvar auth-source-pass--cache (make-hash-table :test #'equal))

  (defun auth-source-pass--reset-cache ()
    (setq auth-source-pass--cache (make-hash-table :test #'equal)))

  (defun auth-source-pass--read-entry (entry)
    "Return a string with the file content of ENTRY."
    (run-at-time 45 nil #'auth-source-pass--reset-cache)
    (let ((cached (gethash entry auth-source-pass--cache)))
      (or cached
          (puthash
           entry
           (with-temp-buffer
             (insert-file-contents (expand-file-name
                                    (format "%s.gpg" entry)
                                    (getenv "PASSWORD_STORE_DIR")))
             (buffer-substring-no-properties (point-min) (point-max)))
           auth-source-pass--cache))))

  (defun auth-source-pass-entries ()
    "Return a list of all password store entries."
    (let ((store-dir (getenv "PASSWORD_STORE_DIR")))
      (mapcar
       (lambda (file) (file-name-sans-extension (file-relative-name file store-dir)))
       (directory-files-recursively store-dir "\.gpg$")))))

(use-package auto-yasnippet
  :after yasnippet
  :bind (("C-c y a" . aya-create)
         ("C-c y e" . aya-expand)
         ("C-c y o" . aya-open-line)))

(use-package avy
  :bind* ("C-." . avy-goto-char-timer)
  :config
  (avy-setup-default))

(use-package avy-zap
  :bind (("M-z" . avy-zap-to-char-dwim)
         ("M-Z" . avy-zap-up-to-char-dwim)))

(use-package backup-each-save
  :commands backup-each-save
  :preface
  (defun my-make-backup-file-name (file)
    (make-backup-file-name-1 (expand-file-name (file-truename file))))

  (defun backup-each-save-filter (filename)
    (not (string-match
          (concat "\\(^/tmp\\|\\.emacs\\.d/data\\(-alt\\)?/"
                  "\\|\\.newsrc\\(\\.eld\\)?\\|"
                  "\\(archive/sent/\\|recentf\\`\\)\\)")
          filename)))

  (defun my-dont-backup-files-p (filename)
    (unless (string-match filename "\\(archive/sent/\\|recentf\\`\\)")
      (normal-backup-enable-predicate filename)))

  :hook after-save
  :config
  (setq backup-each-save-filter-function 'backup-each-save-filter
        backup-enable-predicate 'my-dont-backup-files-p))

(use-package backup-walker
  :commands backup-walker-start)

(use-package beacon
  :diminish
  :commands beacon-mode)

(use-package biblio
  :commands biblio-lookup)

(use-package bm
  :unless alternate-emacs
  :bind (("C-c b b" . bm-toggle)
         ("C-c b n" . bm-next)
         ("C-c b p" . bm-previous))
  :commands (bm-repository-load
             bm-buffer-save
             bm-buffer-save-all
             bm-buffer-restore)
  :init
  (add-hook 'after-init-hook #'bm-repository-load)
  (add-hook 'find-file-hooks #'bm-buffer-restore)
  (add-hook 'after-revert-hook #'bm-buffer-restore)
  (add-hook 'kill-buffer-hook #'bm-buffer-save)
  (add-hook 'after-save-hook #'bm-buffer-save)
  (add-hook 'vc-before-checkin-hook #'bm-buffer-save)
  (add-hook 'kill-emacs-hook #'(lambda nil
                                 (bm-buffer-save-all)
                                 (bm-repository-save))))

(use-package bookmark+
  :after bookmark
  :bind ("M-B" . bookmark-bmenu-list)
  :commands bmkp-jump-dired)

(use-package boogie-friends)

(use-package browse-at-remote
  :bind ("C-c B" . browse-at-remote))

(use-package browse-kill-ring
  :defer 5
  :commands browse-kill-ring)

(use-package browse-kill-ring+
  :after browse-kill-ring
  :config (browse-kill-ring-default-keybindings))

(use-package bytecomp-simplify
  :defer 15)

(use-package c-includes
  :disabled t
  :commands c-includes
  :after cc-mode
  :bind (:map c-mode-base-map
              ("C-c C-i"  . c-includes-current-file)))

(use-package calc
  :defer t
  :custom
  (math-additional-units
   '((GiB "1024 * MiB" "Giga Byte")
     (MiB "1024 * KiB" "Mega Byte")
     (KiB "1024 * B" "Kilo Byte")
     (B nil "Byte")
     (Gib "1024 * Mib" "Giga Bit")
     (Mib "1024 * Kib" "Mega Bit")
     (Kib "1024 * b" "Kilo Bit")
     (b "B / 8" "Bit")))
  :config
  (setq math-units-table nil))

(use-package cargo
  :commands cargo-minor-mode
  :bind (:map cargo-mode-map
              ("C-c C-c C-y" . cargo-process-clippy))
  :config
  (defadvice cargo-process-clippy
      (around my-cargo-process-clippy activate)
    (let ((cargo-process--command-flags
           (concat cargo-process--command-flags
                   "--all-targets "
                   "--all-features "
                   "-- "
                   "-D warnings "
                   "-D clippy::all "
                   "-D clippy::mem_forget "
                   "-C debug-assertions=off")))
      ad-do-it))

  (defun cargo-fix ()
    (interactive)
    (async-shell-command
     (concat "cargo fix"
             " --clippy --tests --benches --allow-dirty --allow-staged"))))

(use-package cc-mode
  :mode (("\\.h\\(h?\\|xx\\|pp\\)\\'" . c++-mode)
         ("\\.m\\'" . c-mode)
         ("\\.mm\\'" . c++-mode))
  :bind (:map c++-mode-map
              ("<" . self-insert-command)
              (">" . self-insert-command))
  :bind (:map c-mode-base-map
              ("#" . self-insert-command)
              ("{" . self-insert-command)
              ("}" . self-insert-command)
              ("/" . self-insert-command)
              ("*" . self-insert-command)
              (";" . self-insert-command)
              ("," . self-insert-command)
              (":" . self-insert-command)
              ("(" . self-insert-command)
              (")" . self-insert-command)
              ("<return>" . newline-and-indent)
              ("M-q" . c-fill-paragraph)
              ("M-j"))
  :preface
  (defun my-c-mode-common-hook ()
    (require 'flycheck)
    ;; (flycheck-define-checker
    ;;  c++-ledger
    ;;  "A C++ syntax checker for the Ledger project specifically."
    ;;  :command ("ninja"
    ;;            "-C"
    ;;            (eval (expand-file-name "~/Products/ledger"))
    ;;            (eval (concat "src/CMakeFiles/libledger.dir/"
    ;;                          (file-name-nondirectory (buffer-file-name))
    ;;                          ".o")))
    ;;  :error-patterns
    ;;  ((error line-start
    ;;          (message "In file included from") " " (or "<stdin>" (file-name))
    ;;          ":" line ":" line-end)
    ;;   (info line-start (or "<stdin>" (file-name)) ":" line ":" column
    ;;         ": note: " (optional (message)) line-end)
    ;;   (warning line-start (or "<stdin>" (file-name)) ":" line ":" column
    ;;            ": warning: " (optional (message)) line-end)
    ;;   (error line-start (or "<stdin>" (file-name)) ":" line ":" column
    ;;          ": " (or "fatal error" "error") ": " (optional (message)) line-end))
    ;;  :error-filter
    ;;  (lambda (errors)
    ;;    (let ((errors (flycheck-sanitize-errors errors)))
    ;;      (dolist (err errors)
    ;;        ;; Clang will output empty messages for #error/#warning pragmas
    ;;        ;; without messages. We fill these empty errors with a dummy message
    ;;        ;; to get them past our error filtering
    ;;        (setf (flycheck-error-message err)
    ;;              (or (flycheck-error-message err) "no message")))
    ;;      (flycheck-fold-include-levels errors "In file included from")))
    ;;  :modes c++-mode
    ;;  :next-checkers ((warning . c/c++-cppcheck)))

    (flycheck-mode 1)
    ;; (flycheck-select-checker 'c++-ledger)
    (setq-local flycheck-check-syntax-automatically nil)
    (setq-local flycheck-highlighting-mode nil)

    (set (make-local-variable 'parens-require-spaces) nil)

    (let ((bufname (buffer-file-name)))
      (when bufname
        (cond
         ((string-match "/ledger/" bufname)
          (c-set-style "ledger"))
         ((string-match "/edg/" bufname)
          (c-set-style "edg"))
         (t
          (c-set-style "clang")))))

    (font-lock-add-keywords
     'c++-mode '(("\\<\\(assert\\|DEBUG\\)(" 1 font-lock-warning-face t))))

  :hook (c-mode-common . my-c-mode-common-hook)
  :config
  (add-to-list
   'c-style-alist
   '("edg"
     (indent-tabs-mode . nil)
     (c-basic-offset . 2)
     (c-comment-only-line-offset . (0 . 0))
     (c-hanging-braces-alist
      . ((substatement-open before after)
         (arglist-cont-nonempty)))
     (c-offsets-alist
      . ((statement-block-intro . +)
         (knr-argdecl-intro . 5)
         (substatement-open . 0)
         (substatement-label . 0)
         (label . 0)
         (case-label . +)
         (statement-case-open . 0)
         (statement-cont . +)
         (arglist-intro . +)
         (arglist-close . +)
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
     (c-hanging-braces-alist
      . ((substatement-open before after)
         (arglist-cont-nonempty)))
     (c-offsets-alist
      . ((statement-block-intro . +)
         (knr-argdecl-intro . 5)
         (substatement-open . 0)
         (substatement-label . 0)
         (label . 0)
         (case-label . 0)
         (statement-case-open . 0)
         (statement-cont . +)
         (arglist-intro . +)
         (arglist-close . +)
         (inline-open . 0)
         (brace-list-open . 0)
         (topmost-intro-cont
          . (first c-lineup-topmost-intro-cont
                   c-lineup-gnu-DEFUN-intro-cont))))
     (c-special-indent-hook . c-gnu-impose-minimum)
     (c-block-comment-prefix . "")))

  (add-to-list
   'c-style-alist
   '("clang"
     (indent-tabs-mode . nil)
     (c-basic-offset . 2)
     (c-comment-only-line-offset . (0 . 0))
     (c-hanging-braces-alist
      . ((substatement-open before after)
         (arglist-cont-nonempty)))
     (c-offsets-alist
      . ((statement-block-intro . +)
         (knr-argdecl-intro . 5)
         (substatement-open . 0)
         (substatement-label . 0)
         (label . 0)
         (case-label . 0)
         (statement-case-open . 0)
         (statement-cont . +)
         (arglist-intro . +)
         (arglist-close . +)
         (inline-open . 0)
         (brace-list-open . 0)
         (topmost-intro-cont
          . (first c-lineup-topmost-intro-cont
                   c-lineup-gnu-DEFUN-intro-cont))))
     (c-special-indent-hook . c-gnu-impose-minimum)
     (c-block-comment-prefix . ""))))

(use-package centered-cursor-mode
  :commands centered-cursor-mode)

(use-package change-inner
  :bind (("M-i"     . change-inner)
         ("M-o M-o" . change-outer)))

(use-package chess
  :load-path "lisp/chess"
  :commands chess)

(use-package chess-ics
  :after chess
  :commands chess-ics
  :config
  (defun chess ()
    (interactive)
    (chess-ics "freechess.org" 5000 "jwiegley"
               (lookup-password "freechess.org" "jwiegley" 80))))

(use-package circe
  :if alternate-emacs
  :defer t)

(use-package cl-info
  ;; jww (2017-12-10): Need to configure.
  :disabled t)

(use-package cmake-font-lock
  :hook (cmake-mode . cmake-font-lock-activate))

(use-package cmake-mode
  :mode ("CMakeLists.txt" "\\.cmake\\'"))

(use-package col-highlight
  :commands col-highlight-mode)

(use-package color-moccur
  :commands (isearch-moccur isearch-all isearch-moccur-all)
  :bind (("M-s O" . moccur)
         :map isearch-mode-map
         ("M-o" . isearch-moccur)
         ("M-O" . isearch-moccur-all)))

(use-package command-log-mode
  :bind (("C-c e M" . command-log-mode)
         ("C-c e L" . clm/open-command-log-buffer)))

(use-package company
  :defer 5
  :diminish
  :commands (company-mode company-indent-or-complete-common)
  :init
  (dolist (hook '(emacs-lisp-mode-hook
                  c-mode-common-hook))
    (add-hook hook
              #'(lambda ()
                  (local-set-key (kbd "<tab>")
                                 #'company-indent-or-complete-common))))
  :config
  ;; From https://github.com/company-mode/company-mode/issues/87
  ;; See also https://github.com/company-mode/company-mode/issues/123
  (defadvice company-pseudo-tooltip-unless-just-one-frontend
      (around only-show-tooltip-when-invoked activate)
    (when (company-explicit-action-p)
      ad-do-it))

  ;; See http://oremacs.com/2017/12/27/company-numbers/
  (defun ora-company-number ()
    "Forward to `company-complete-number'.

  Unless the number is potentially part of the candidate.
  In that case, insert the number."
    (interactive)
    (let* ((k (this-command-keys))
           (re (concat "^" company-prefix k)))
      (if (cl-find-if (lambda (s) (string-match re s))
                      company-candidates)
          (self-insert-command 1)
        (company-complete-number (string-to-number k)))))

  (let ((map company-active-map))
    (mapc
     (lambda (x)
       (define-key map (format "%d" x) 'ora-company-number))
     (number-sequence 0 9))
    (define-key map " " (lambda ()
                          (interactive)
                          (company-abort)
                          (self-insert-command 1))))

  (defun check-expansion ()
    (save-excursion
      (if (outline-on-heading-p t)
          nil
        (if (looking-at "\\_>") t
          (backward-char 1)
          (if (looking-at "\\.") t
            (backward-char 1)
            (if (looking-at "->") t nil))))))

  (define-key company-mode-map [tab]
    '(menu-item "maybe-company-expand" nil
                :filter (lambda (&optional _)
                          (when (check-expansion)
                            #'company-complete-common))))

  (eval-after-load "coq"
    '(progn
       (defun company-mode/backend-with-yas (backend)
         (if (and (listp backend) (member 'company-yasnippet backend))
             backend
           (append (if (consp backend) backend (list backend))
                   '(:with company-yasnippet))))
       (setq company-backends
             (mapcar #'company-mode/backend-with-yas company-backends))))

  (global-company-mode 1))

(use-package company-auctex
  :after (company latex))

(use-package company-cabal
  :after (company haskell-cabal))

(use-package company-coq
  :after coq
  :commands company-coq-mode
  :bind (:map company-coq-map
              ("M-<return>"))
  :bind (:map coq-mode-map
              ("C-M-h" . company-coq-toggle-definition-overlay)))

(use-package company-elisp
  :after company
  :config
  (push 'company-elisp company-backends))

(setq-local company-backend '(company-elisp))

(use-package company-math
  :defer t)

(use-package company-quickhelp
  :after company
  :bind (:map company-active-map
              ("C-c ?" . company-quickhelp-manual-begin)))

(use-package company-restclient
  :after (company restclient))

(use-package company-rtags
  :disabled t
  :load-path "~/.nix-profile/share/emacs/site-lisp/rtags"
  :after (company rtags)
  :config
  (push 'company-rtags company-backends))

(use-package company-terraform
  :after (company terraform-mode))

(use-package compile
  :no-require
  :bind (("C-c c" . compile)
         ("M-O"   . show-compilation))
  :bind (:map compilation-mode-map
              ("z" . delete-window))
  :preface
  (defun show-compilation ()
    (interactive)
    (let ((it
           (catch 'found
             (dolist (buf (buffer-list))
               (when (string-match "\\*compilation\\*" (buffer-name buf))
                 (throw 'found buf))))))
      (if it
          (display-buffer it)
        (call-interactively 'compile))))

  (defun compilation-ansi-color-process-output ()
    (ansi-color-process-output nil)
    (set (make-local-variable 'comint-last-output-start)
         (point-marker)))

  :hook (compilation-filter . compilation-ansi-color-process-output))

(use-package copy-as-format
  :bind (("C-c w m" . copy-as-format-markdown)
         ("C-c w g" . copy-as-format-slack)
         ("C-c w o" . copy-as-format-org-mode)
         ("C-c w r" . copy-as-format-rst)
         ("C-c w s" . copy-as-format-github)
         ("C-c w w" . copy-as-format))
  :init
  (setq copy-as-format-default "github"))

(use-package coq-lookup
  :bind ("C-h q" . coq-lookup))

(use-package counsel
  :after ivy
  :demand t
  :diminish
  :custom (counsel-find-file-ignore-regexp
           (concat "\\(\\`\\.[^.]\\|"
                   (regexp-opt completion-ignored-extensions)
                   "\\'\\)"))
  :bind (("C-*"     . counsel-org-agenda-headlines)
         ("C-x C-f" . counsel-find-file)
         ("C-c e l" . counsel-find-library)
         ("C-c e q" . counsel-set-variable)
         ("C-h e l" . counsel-find-library)
         ("C-h e u" . counsel-unicode-char)
         ("C-h f"   . counsel-describe-function)
         ("C-x r b" . counsel-bookmark)
         ("M-x"     . counsel-M-x)
         ;; ("M-y"     . counsel-yank-pop)

         ("M-s f" . counsel-file-jump)
         ;; ("M-s g" . counsel-rg)
         ("M-s j" . counsel-dired-jump))
  :commands counsel-minibuffer-history
  :init
  (bind-key "M-r" #'counsel-minibuffer-history minibuffer-local-map)
  :config
  (add-to-list 'ivy-sort-matches-functions-alist
               '(counsel-find-file . ivy--sort-files-by-date))

  (defun counsel-recoll-function (string)
    "Run recoll for STRING."
    (if (< (length string) 3)
        (counsel-more-chars 3)
      (counsel--async-command
       (format "recollq -t -b %s"
               (shell-quote-argument string)))
      nil))

  (defun counsel-recoll (&optional initial-input)
    "Search for a string in the recoll database.
  You'll be given a list of files that match.
  Selecting a file will launch `swiper' for that file.
  INITIAL-INPUT can be given as the initial minibuffer input."
    (interactive)
    (counsel-require-program "recollq")
    (ivy-read "recoll: " 'counsel-recoll-function
              :initial-input initial-input
              :dynamic-collection t
              :history 'counsel-git-grep-history
              :action (lambda (x)
                        (when (string-match "file://\\(.*\\)\\'" x)
                          (let ((file-name (match-string 1 x)))
                            (find-file file-name)
                            (unless (string-match "pdf$" x)
                              (swiper ivy-text)))))
              :unwind #'counsel-delete-process
              :caller 'counsel-recoll)))

(use-package counsel-gtags
  ;; jww (2017-12-10): Need to configure.
  :disabled t
  :after counsel)

(use-package counsel-jq
  :commands counsel-jq)

(use-package counsel-osx-app
  :bind* ("S-M-SPC" . counsel-osx-app)
  :commands counsel-osx-app
  :config
  (setq counsel-osx-app-location
        (list "/Applications"
              "/Applications/Misc"
              "/Applications/Utilities"
              (expand-file-name "~/Applications")
              (expand-file-name "~/.nix-profile/Applications")
              "/Applications/Xcode.app/Contents/Applications")))

(use-package counsel-projectile
  :after (counsel projectile)
  :config
  (counsel-projectile-mode 1))

(use-package counsel-tramp
  :commands counsel-tramp)

(use-package crosshairs
  :bind ("M-o c" . crosshairs-mode))

(use-package crux
  :bind ("C-c e i" . crux-find-user-init-file))

(use-package css-mode
  :mode "\\.css\\'")

(use-package csv-mode
  :mode "\\.csv\\'"
  :config
  (defun csv-remove-commas ()
    (interactive)
    (goto-char (point-min))
    (while (re-search-forward "\"\\([^\"]+\\)\"" nil t)
      (replace-match (replace-regexp-in-string "," "" (match-string 1)))))

  (defun maybe-add (x y)
    (if (equal x "")
        (if (equal y "")
            ""
          y)
      (if (equal y "")
          x
        (format "%0.2f" (+ (string-to-number x) (string-to-number y))))))

  (defun parse-desc (desc)
    (cond
     ((string-match "\\(BOT \\+\\|SOLD -\\)\\([0-9]+\\) \\(.+\\) @\\([0-9.]+\\)\\( .+\\)?" desc)
      (list (match-string 1 desc)
            (match-string 2 desc)
            (match-string 3 desc)
            (match-string 4 desc)
            (match-string 5 desc)))))

  (defun maybe-add-descs (x y)
    (let ((x-info (parse-desc x))
          (y-info (parse-desc y)))
      (and (string= (nth 0 x-info) (nth 0 y-info))
           (string= (nth 2 x-info) (nth 2 y-info))
           (string= (nth 3 x-info) (nth 3 y-info))
           (format "%s%d %s @%s%s"
                   (nth 0 y-info)
                   (+ (string-to-number (nth 1 x-info))
                      (string-to-number (nth 1 y-info)))
                   (nth 2 y-info)
                   (nth 3 y-info)
                   (or (nth 4 y-info) "")))))

  (defun csv-merge-lines ()
    (interactive)
    (goto-char (line-beginning-position))
    (let ((start (point-marker))
          (fields-a (csv--collect-fields (line-end-position))))
      (forward-line 1)
      (let ((fields-b (csv--collect-fields (line-end-position))))
        (when (string= (nth 3 fields-a) (nth 3 fields-b))
          (let ((desc (maybe-add-descs (nth 4 fields-a) (nth 4 fields-b))))
            (when desc
              (delete-region start (line-end-position))
              (setcar (nthcdr 4 fields-b) desc)
              (setcar (nthcdr 5 fields-b)
                      (maybe-add (nth 5 fields-a) (nth 5 fields-b)))
              (setcar (nthcdr 6 fields-b)
                      (maybe-add (nth 6 fields-a) (nth 6 fields-b)))
              (setcar (nthcdr 7 fields-b)
                      (maybe-add (nth 7 fields-a) (nth 7 fields-b)))
              (insert (mapconcat #'identity fields-b ","))
              (forward-char 1)
              (forward-line -1))))))))

(use-package cursor-chg
  :commands change-cursor-mode
  :config
  (change-cursor-mode 1)
  (toggle-cursor-type-when-idle 1))

(use-package cus-edit
  :bind (("C-c o" . customize-option)
         ("C-c O" . customize-group)
         ("C-c F" . customize-face)))

(use-package dafny-mode
  :bind (:map dafny-mode-map
              ("M-n" . flycheck-next-error)
              ("M-p" . flycheck-previous-error)))

(use-package debbugs-gnu
  :disabled t
  :commands (debbugs-gnu debbugs-gnu-search)
  :bind ("C-c #" . gnus-read-ephemeral-emacs-bug-group))

(use-package deadgrep
  :bind ("M-s g" . deadgrep))

(use-package dedicated
  :bind ("C-c W" . dedicated-mode))

(use-package deft
  :bind ("C-, C-," . deft))

(use-package diff-hl
  :commands (diff-hl-mode diff-hl-dired-mode)
  :hook (magit-post-refresh . diff-hl-magit-post-refresh))

(use-package diff-hl-flydiff
  :commands diff-hl-flydiff-mode)

(use-package diff-mode
  :commands diff-mode)

(use-package diffview
  :commands (diffview-current diffview-region diffview-message))

(use-package dired
  :bind ("C-c j" . dired-two-pane)
  :bind (:map dired-mode-map
              ("j"     . dired)
              ("z"     . pop-window-configuration)
              ("e"     . ora-ediff-files)
              ("l"     . dired-up-directory)
              ("q"     . pop-window-configuration)
              ("Y"     . ora-dired-rsync)
              ("M-!"   . shell-command)
              ("<tab>" . dired-next-window)
              ("M-G")
              ("M-s f"))
  :diminish dired-omit-mode
  :hook (dired-mode . dired-hide-details-mode)
  ;; :hook (dired-mode . dired-omit-mode)
  :preface
  (defun dired-two-pane ()
    (interactive)
    (push-window-configuration)
    (let ((here default-directory))
      (delete-other-windows)
      (dired "~/dl")
      (split-window-horizontally)
      (dired here)))

  (defun dired-next-window ()
    (interactive)
    (let ((next (car (cl-remove-if-not #'(lambda (wind)
                                           (with-current-buffer (window-buffer wind)
                                             (eq major-mode 'dired-mode)))
                                       (cdr (window-list))))))
      (when next
        (select-window next))))

  (defvar mark-files-cache (make-hash-table :test #'equal))

  (defun mark-similar-versions (name)
    (let ((pat name))
      (if (string-match "^\\(.+?\\)-[0-9._-]+$" pat)
          (setq pat (match-string 1 pat)))
      (or (gethash pat mark-files-cache)
          (ignore (puthash pat t mark-files-cache)))))

  (defun dired-mark-similar-version ()
    (interactive)
    (setq mark-files-cache (make-hash-table :test #'equal))
    (dired-mark-sexp '(mark-similar-versions name)))

  (defun ora-dired-rsync (dest)
    (interactive
     (list
      (expand-file-name
       (read-file-name "Rsync to: " (dired-dwim-target-directory)))))
    (let ((files (dired-get-marked-files
                  nil current-prefix-arg))
          (tmtxt/rsync-command "rsync -aP "))
      (dolist (file files)
        (setq tmtxt/rsync-command
              (concat tmtxt/rsync-command
                      (shell-quote-argument file)
                      " ")))
      (setq tmtxt/rsync-command
            (concat tmtxt/rsync-command
                    (shell-quote-argument dest)))
      (async-shell-command tmtxt/rsync-command "*rsync*")
      (other-window 1)))

  (defun ora-ediff-files ()
    (interactive)
    (let ((files (dired-get-marked-files))
          (wnd (current-window-configuration)))
      (if (<= (length files) 2)
          (let ((file1 (car files))
                (file2 (if (cdr files)
                           (cadr files)
                         (read-file-name
                          "file: "
                          (dired-dwim-target-directory)))))
            (if (file-newer-than-file-p file1 file2)
                (ediff-files file2 file1)
              (ediff-files file1 file2))
            (add-hook 'ediff-after-quit-hook-internal
                      `(lambda ()
                         (setq ediff-after-quit-hook-internal nil)
                         (set-window-configuration ,wnd))))
        (error "no more than 2 files should be marked"))))

  :config
  (add-hook 'dired-mode-hook
            #'(lambda () (bind-key "M-G" #'switch-to-gnus dired-mode-map))))

(use-package dired-toggle
  :bind ("C-c ~" . dired-toggle)
  :preface
  (defun my-dired-toggle-mode-hook ()
    (interactive)
    (visual-line-mode 1)
    (setq-local visual-line-fringe-indicators '(nil right-curly-arrow))
    (setq-local word-wrap nil))
  :hook (dired-toggle-mode . my-dired-toggle-mode-hook))

(use-package dired-x
  :after dired
  :config
  ;; (defvar dired-omit-regexp-orig (symbol-function 'dired-omit-regexp))

  ;; ;; Omit files that Git would ignore
  ;; (defun dired-omit-regexp ()
  ;;   (let ((file (expand-file-name ".git"))
  ;;         parent-dir)
  ;;     (while (and (not (file-exists-p file))
  ;;                 (progn
  ;;                   (setq parent-dir
  ;;                         (file-name-directory
  ;;                          (directory-file-name
  ;;                           (file-name-directory file))))
  ;;                   ;; Give up if we are already at the root dir.
  ;;                   (not (string= (file-name-directory file)
  ;;                                 parent-dir))))
  ;;       ;; Move up to the parent dir and try again.
  ;;       (setq file (expand-file-name ".git" parent-dir)))
  ;;     ;; If we found a change log in a parent, use that.
  ;;     (if (file-exists-p file)
  ;;         (let ((regexp (funcall dired-omit-regexp-orig))
  ;;               (omitted-files
  ;;                (shell-command-to-string "git clean -d -x -n")))
  ;;           (if (= 0 (length omitted-files))
  ;;               regexp
  ;;             (concat
  ;;              regexp
  ;;              (if (> (length regexp) 0)
  ;;                  "\\|" "")
  ;;              "\\("
  ;;              (mapconcat
  ;;               #'(lambda (str)
  ;;                   (concat
  ;;                    "^"
  ;;                    (regexp-quote
  ;;                     (substring str 13
  ;;                                (if (= ?/ (aref str (1- (length str))))
  ;;                                    (1- (length str))
  ;;                                  nil)))
  ;;                    "$"))
  ;;               (split-string omitted-files "\n" t)
  ;;               "\\|")
  ;;              "\\)")))
  ;;       (funcall dired-omit-regexp-orig))))
  )

(use-package dired+
  :after dired-x
  :config
  (defun dired-do-delete (&optional arg)  ; Bound to `D'
    "Delete all marked (or next ARG) files.
NOTE: This deletes marked, not flagged, files.
`dired-recursive-deletes' controls whether deletion of
non-empty directories is allowed."
    (interactive "P")
    ;; This is more consistent with the file-marking feature than
    ;; `dired-do-flagged-delete'.  But it can be confusing to the user,
    ;; especially since this is usually bound to `D', which is also the
    ;; `dired-del-marker'.  So offer this warning message:
    (unless arg
      (message "NOTE: Deletion of files marked `%c' (not those flagged `%c')."
               dired-marker-char dired-del-marker))
    (diredp-internal-do-deletions
     ;; This can move point if ARG is an integer.
     (dired-map-over-marks (cons (dired-get-filename) (point)) arg)
     arg
     'USE-TRASH-CAN))

  (defun dired-do-flagged-delete (&optional no-msg) ; Bound to `x'
    "In Dired, delete the files flagged for deletion.
NOTE: This deletes flagged, not marked, files.
If arg NO-MSG is non-nil, no message is displayed.

User option `dired-recursive-deletes' controls whether deletion of
non-empty directories is allowed."
    (interactive)
    (unless no-msg
      (message "NOTE: Deletion of files flagged `%c' (not those marked `%c')"
               dired-del-marker dired-marker-char)
      ;; Too slow/annoying, but without it the message is never seen: (sit-for 2)
      )
    (let* ((dired-marker-char  dired-del-marker)
           (regexp             (dired-marker-regexp))
           (case-fold-search   nil))
      (if (save-excursion (goto-char (point-min)) (re-search-forward regexp nil t))
          (diredp-internal-do-deletions
           ;; This cannot move point since last arg is nil.
           (dired-map-over-marks (cons (dired-get-filename) (point)) nil)
           nil
           'USE-TRASH-CAN)                ; This arg is for Emacs 24+ only.
        (unless no-msg (message "(No deletions requested.)"))))))

(use-package dired-rsync
  :disabled t
  :after dired
  :config
  (bind-key "C-c C-r" 'dired-rsync dired-mode-map))

(use-package direnv
  :demand t
  :preface
  (defun patch-direnv-environment (&rest _args)
    (setenv "PATH" (concat emacs-binary-path ":" (getenv "PATH")))
    (setq exec-path (cons (file-name-as-directory emacs-binary-path)
                          exec-path)))
  :init
  (defconst emacs-binary-path (directory-file-name
                               (file-name-directory
                                (executable-find "emacsclient"))))
  :config
  (defvar flycheck-executable-for-buffer (make-hash-table :test #'equal))
  (defun locate-flycheck-executable (cmd)
    ;; (add-hook 'post-command-hook #'direnv--maybe-update-environment)
    (let ((exe (gethash (cons cmd (buffer-name))
                        flycheck-executable-for-buffer)))
      (if exe
          exe
        (direnv-update-environment default-directory)
        (let ((exe (executable-find cmd)))
          (puthash (cons cmd (buffer-name)) exe
                   flycheck-executable-for-buffer)))))
  (eval-after-load 'flycheck
    '(setq flycheck-executable-find #'locate-flycheck-executable))
  (add-hook 'coq-mode-hook
            #'(lambda ()
                ;; (add-hook 'post-command-hook #'direnv--maybe-update-environment)
                (direnv-update-environment default-directory)))
  (advice-add 'direnv-update-directory-environment
              :after #'patch-direnv-environment)
  (add-hook 'git-commit-mode-hook #'patch-direnv-environment)
  (add-hook 'magit-status-mode-hook #'patch-direnv-environment)
  (defvar my-direnv-last-buffer nil)
  (defun update-on-buffer-change ()
    (unless (eq (current-buffer) my-direnv-last-buffer)
      (setq my-direnv-last-buffer (current-buffer))
      (direnv-update-environment default-directory)))
  (add-hook 'post-command-hook #'update-on-buffer-change))

(use-package discover-my-major
  :bind (("C-h <C-m>" . discover-my-major)
         ("C-h M-m"   . discover-my-mode)))

(use-package docker
  :bind ("C-c d" . docker)
  :diminish
  :init
  (use-package docker-image     :commands docker-images)
  (use-package docker-container :commands docker-containers)
  (use-package docker-volume    :commands docker-volumes)
  (use-package docker-network   :commands docker-containers)
  (use-package docker-machine   :commands docker-machines)
  (use-package docker-compose   :commands docker-compose))

(use-package docker-compose-mode
  :mode "docker-compose.*\.yml\\'")

(use-package docker-tramp
  :after tramp
  :defer 5)

(use-package dockerfile-mode
  :mode "Dockerfile[a-zA-Z.-]*\\'")

(use-package dot-gnus
  :bind (("M-G"   . switch-to-gnus)
         ("C-x m" . compose-mail))
  :init
  ;; Have to set these here, because initsplit sends their customization
  ;; values to gnus-settings.el.
  (setq gnus-init-file (emacs-path "dot-gnus")
        gnus-home-directory "~/Messages/Gnus/")

  (defun fetchmail-password ()
    (lookup-password "imap.fastmail.com" "johnw" 993)))

(use-package dot-org
  :commands my-org-startup
  :bind* (("M-C"   . jump-to-org-agenda)
          ("M-m"   . org-smart-capture)
          ("M-M"   . org-inline-note)
          ("C-c a" . org-agenda)
          ("C-c S" . org-store-link)
          ("C-c l" . org-insert-link))
  :config
  (unless alternate-emacs
    (run-with-idle-timer 300 t 'jump-to-org-agenda)
    (my-org-startup)))

(use-package doxymacs
  :commands (doxymacs-mode doxymacs-font-lock)
  :config
  (doxymacs-mode 1)
  (doxymacs-font-lock))

(use-package dumb-jump
  :hook ((coq-mode haskell-mode) . dumb-jump-mode))

(use-package ebdb-com
  :commands ebdb)

(use-package edbi
  :commands edbi:sql-mode)

(use-package ediff
  :bind (("C-c = b" . ediff-buffers)
         ("C-c = B" . ediff-buffers3)
         ("C-c = c" . compare-windows)
         ("C-c = =" . ediff-files)
         ("C-c = f" . ediff-files)
         ("C-c = F" . ediff-files3)
         ("C-c = m" . count-matches)
         ("C-c = r" . ediff-revision)
         ("C-c = p" . ediff-patch-file)
         ("C-c = P" . ediff-patch-buffer)
         ("C-c = l" . ediff-regions-linewise)
         ("C-c = w" . ediff-regions-wordwise))
  :init
  (defun test-compare ()
    (interactive)
    (delete-other-windows)
    (let ((here (point)))
      (search-forward "got:")
      (split-window-below)
      (goto-char here))
    (search-forward "expected:")
    (call-interactively #'compare-windows))

  (defun test-ediff ()
    (interactive)
    (goto-char (point-min))
    (search-forward "expected:")
    (forward-line 1)
    (goto-char (line-beginning-position))
    (let ((begin (point)))
      (search-forward "(")
      (goto-char (match-beginning 0))
      (forward-sexp)
      (let ((text (buffer-substring begin (point)))
            (expected (get-buffer-create "*expected*")))
        (with-current-buffer expected
          (erase-buffer)
          (insert text))
        (let ((here (point)))
          (search-forward "got:")
          (forward-line 1)
          (goto-char (line-beginning-position))
          (setq begin (point))
          (search-forward "(")
          (goto-char (match-beginning 0))
          (forward-sexp)
          (setq text (buffer-substring begin (point)))
          (let ((got (get-buffer-create "*got*")))
            (with-current-buffer got
              (erase-buffer)
              (insert text))
            (ediff-buffers expected got)))))))

(use-package ediff-keep
  :after ediff)

(use-package edit-env
  :commands edit-env)

(use-package edit-indirect
  :bind (("C-c '" . edit-indirect-region)))

(use-package edit-rectangle
  :bind ("C-x r e" . edit-rectangle))

(use-package edit-server
  :disabled t
  :if (and window-system
           (not alternate-emacs))
  :defer 5
  :config
  (edit-server-start))

(use-package edit-var
  :bind ("C-c e v" . edit-variable))

(use-package eglot
  :if dot-emacs-use-eglot
  :commands eglot
  :config
  ;; (add-to-list 'eglot-server-programs '(rust-mode "rust-analyzer"))
  (defvar flymake-list-only-diagnostics nil)
  (defun project-root (project)
    (car (project-roots project)))
  )

(use-package eldoc
  :diminish
  :hook ((c-mode-common emacs-lisp-mode) . eldoc-mode))

(use-package elint
  :commands (elint-initialize elint-current-buffer)
  :bind ("C-c e E" . my-elint-current-buffer)
  :preface
  (defun my-elint-current-buffer ()
    (interactive)
    (elint-initialize)
    (elint-current-buffer))
  :config
  (add-to-list 'elint-standard-variables 'current-prefix-arg)
  (add-to-list 'elint-standard-variables 'command-line-args-left)
  (add-to-list 'elint-standard-variables 'buffer-file-coding-system)
  (add-to-list 'elint-standard-variables 'emacs-major-version)
  (add-to-list 'elint-standard-variables 'window-system))

(use-package elisp-depend
  :commands elisp-depend-print-dependencies)

(use-package elisp-docstring-mode
  :commands elisp-docstring-mode)

(use-package elisp-slime-nav
  :diminish
  :commands (elisp-slime-nav-mode
             elisp-slime-nav-find-elisp-thing-at-point))

(use-package elmacro
  :bind (("C-c m e" . elmacro-mode)
         ("C-x C-)" . elmacro-show-last-macro)))

(use-package emamux
  :commands emamux:send-command)

(use-package emojify
  :after erc
  :defer 15
  :config
  (global-emojify-mode)
  ;; (global-emojify-mode-line-mode -1)
  )

(use-package engine-mode
  :defer 5
  :config
  (defengine google "https://www.google.com/search?q=%s"
    :keybinding "/")
  (engine-mode 1))

(use-package epa
  :config
  (epa-file-enable))

(use-package erc
  :commands (erc erc-tls)
  :bind (:map erc-mode-map
              ("C-c r" . reset-erc-track-mode))
  :preface
  (defun irc (&optional arg)
    (interactive "P")
    (if arg
        (pcase-dolist (`(,server . ,nick)
                       '(("irc.libera.chat"  . "johnw")
                         ("irc.gitter.im"    . "jwiegley")))
          (erc-tls :server server :port 6697 :nick (concat nick "_")
                   :password (lookup-password server nick 6697)))
      (let ((pass (lookup-password "irc.libera.chat" "johnw" 6697)))
        (when (> (length pass) 32)
          (error "Failed to read ZNC password"))
        (erc :server "127.0.0.1" :port 6697 :nick "johnw"
             :password (concat "johnw/gitter:" pass))
        (sleep-for 5)
        (erc :server "127.0.0.1" :port 6697 :nick "johnw"
             :password (concat "johnw/libera:" pass)))))

  (defun reset-erc-track-mode ()
    (interactive)
    (setq erc-modified-channels-alist nil)
    (erc-modified-channels-update)
    (erc-modified-channels-display)
    (force-mode-line-update))

  (defun setup-irc-environment ()
    (set (make-local-variable 'scroll-conservatively) 100)
    (setq erc-timestamp-only-if-changed-flag nil
          erc-timestamp-format "%H:%M "
          erc-fill-prefix "          "
          erc-fill-column 78
          erc-insert-timestamp-function 'erc-insert-timestamp-left
          ivy-use-virtual-buffers nil
          line-spacing 4))

  (defun accept-certificate ()
    (interactive)
    (when (re-search-backward "/znc[\n ]+AddTrustedServerFingerprint[\n ]+\\(.+\\)" nil t)
      (goto-char (point-max))
      (erc-send-input (concat "/znc AddTrustedServerFingerprint " (match-string 1)))))

  (defcustom erc-foolish-content '()
    "Regular expressions to identify foolish content.
    Usually what happens is that you add the bots to
    `erc-ignore-list' and the bot commands to this list."
    :group 'erc
    :type '(repeat regexp))

  (defun erc-foolish-content (msg)
    "Check whether MSG is foolish."
    (erc-list-match erc-foolish-content msg))

  :init
  (add-hook 'erc-mode-hook #'setup-irc-environment)
  (when alternate-emacs
    (add-hook 'emacs-startup-hook #'irc))

  (eval-after-load 'erc-identd
    '(defun erc-identd-start (&optional port)
       "Start an identd server listening to port 8113.
  Port 113 (auth) will need to be redirected to port 8113 on your
  machine -- using iptables, or a program like redir which can be
  run from inetd. The idea is to provide a simple identd server
  when you need one, without having to install one globally on
  your system."
       (interactive (list (read-string "Serve identd requests on port: " "8113")))
       (unless port (setq port erc-identd-port))
       (when (stringp port)
         (setq port (string-to-number port)))
       (when erc-identd-process
         (delete-process erc-identd-process))
       (setq erc-identd-process
	     (make-network-process :name "identd"
			           :buffer nil
			           :host 'local :service port
			           :server t :noquery t
			           :filter 'erc-identd-filter))
       (set-process-query-on-exit-flag erc-identd-process nil)))

  :config
  (erc-track-minor-mode 1)
  (erc-track-mode 1)

  (add-hook 'erc-insert-pre-hook
            #'(lambda (s)
                (when (erc-foolish-content s)
                  (setq erc-insert-this nil))))

  (bind-key "<f5>" #'accept-certificate))

(use-package erc-alert
  :disabled t
  :after erc)

(use-package erc-highlight-nicknames
  :after erc)

(use-package erc-macros
  :after erc)

(use-package erc-patch
  :disabled t
  :after erc)

(use-package erc-question
  :disabled t
  :after erc)

(use-package erc-yank
  :load-path "lisp/erc-yank"
  :after erc
  :bind (:map erc-mode-map
              ("C-y" . erc-yank )))

(use-package erefactor
  :disabled t
  :bind (:map emacs-lisp-mode-map
              ("C-c C-v" . erefactor-map)))

(use-package ert
  :bind ("C-c e t" . ert-run-tests-interactively))

(use-package esh-toggle
  :bind ("C-x C-z" . eshell-toggle))

(use-package eshell
  :commands (eshell eshell-command)
  :preface
  (defvar eshell-isearch-map
    (let ((map (copy-keymap isearch-mode-map)))
      (define-key map [(control ?m)] 'eshell-isearch-return)
      (define-key map [return]       'eshell-isearch-return)
      (define-key map [(control ?r)] 'eshell-isearch-repeat-backward)
      (define-key map [(control ?s)] 'eshell-isearch-repeat-forward)
      (define-key map [(control ?g)] 'eshell-isearch-abort)
      (define-key map [backspace]    'eshell-isearch-delete-char)
      (define-key map [delete]       'eshell-isearch-delete-char)
      map)
    "Keymap used in isearch in Eshell.")

  (defun eshell-initialize ()
    (defun eshell-spawn-external-command (beg end)
      "Parse and expand any history references in current input."
      (save-excursion
        (goto-char end)
        (when (looking-back "&!" beg)
          (delete-region (match-beginning 0) (match-end 0))
          (goto-char beg)
          (insert "spawn "))))

    (add-hook 'eshell-expand-input-functions #'eshell-spawn-external-command)

    (use-package em-unix
      :defer t
      :config
      (unintern 'eshell/su nil)
      (unintern 'eshell/sudo nil)))

  :init
  (add-hook 'eshell-first-time-mode-hook #'eshell-initialize))

(use-package eshell-bookmark
  :hook (eshell-mode . eshell-bookmark-setup))

(use-package eshell-up
  :commands eshell-up)

(use-package eshell-z
  :after eshell)

(use-package etags
  :bind ("M-T" . tags-search))

(use-package eval-expr
  :bind ("M-:" . eval-expr)
  :config
  (defun eval-expr-minibuffer-setup ()
    (local-set-key (kbd "<tab>") #'lisp-complete-symbol)
    (set-syntax-table emacs-lisp-mode-syntax-table)
    (paredit-mode)))

(use-package eval-in-repl
  ;; jww (2017-12-10): Need to configure.
  :disabled t)

(use-package evil
  :commands evil-mode)

(use-package expand-region
  :bind ("C-=" . er/expand-region))

(use-package eyebrowse
  :bind-keymap ("C-\\" . eyebrowse-mode-map)
  :bind (:map eyebrowse-mode-map
              ("C-\\ C-\\" . eyebrowse-last-window-config)
              ("A-1" . eyebrowse-switch-to-window-config-1)
              ("A-2" . eyebrowse-switch-to-window-config-2)
              ("A-3" . eyebrowse-switch-to-window-config-3)
              ("A-4" . eyebrowse-switch-to-window-config-4))
  :config
  (eyebrowse-mode t))

(use-package fancy-narrow
  :bind (("C-c N N" . fancy-narrow-to-region)
         ("C-c N W" . fancy-widen))
  :commands (fancy-narrow-to-region fancy-widen))

(use-package feebleline
  :bind (("M-o m" . feebleline-mode))
  :config
  (window-divider-mode t))

(use-package fence-edit
  :commands fence-edit-code-at-point)

(use-package fetchmail-mode
  :commands fetchmail-mode)

(use-package ffap
  :bind ("C-c v" . ffap))

(use-package flycheck
  :commands (flycheck-mode
             flycheck-next-error
             flycheck-previous-error)
  :init
  (dolist (where '((emacs-lisp-mode-hook . emacs-lisp-mode-map)
                   (haskell-mode-hook    . haskell-mode-map)
                   (js2-mode-hook        . js2-mode-map)
                   (c-mode-common-hook   . c-mode-base-map)
                   ;; (rust-mode-hook       . rust-mode-map)
                   (rustic-mode-hook     . rustic-mode-map)))
    (add-hook (car where)
              `(lambda ()
                 (bind-key "M-n" #'flycheck-next-error ,(cdr where))
                 (bind-key "M-p" #'flycheck-previous-error ,(cdr where)))))
  :config
  (defalias 'show-error-at-point-soon
    'flycheck-show-error-at-point)

  (defun magnars/adjust-flycheck-automatic-syntax-eagerness ()
    "Adjust how often we check for errors based on if there are any.
  This lets us fix any errors as quickly as possible, but in a
  clean buffer we're an order of magnitude laxer about checking."
    (setq flycheck-idle-change-delay
          (if flycheck-current-errors 0.3 3.0)))

  ;; Each buffer gets its own idle-change-delay because of the
  ;; buffer-sensitive adjustment above.
  (make-variable-buffer-local 'flycheck-idle-change-delay)

  (add-hook 'flycheck-after-syntax-check-hook
            #'magnars/adjust-flycheck-automatic-syntax-eagerness)

  ;; Remove newline checks, since they would trigger an immediate check
  ;; when we want the idle-change-delay to be in effect while editing.
  (setq-default flycheck-check-syntax-automatically '(save
                                                      idle-change
                                                      mode-enabled))

  (defun flycheck-handle-idle-change ()
    "Handle an expired idle time since the last change.
  This is an overwritten version of the original
  flycheck-handle-idle-change, which removes the forced deferred.
  Timers should only trigger inbetween commands in a single
  threaded system and the forced deferred makes errors never show
  up before you execute another command."
    (flycheck-clear-idle-change-timer)
    (flycheck-buffer-automatically 'idle-change)))

(use-package flycheck-haskell
  :commands flycheck-haskell-setup)

(use-package flycheck-package
  :after flycheck)

(use-package flyspell
  :bind (("C-c i b" . flyspell-buffer)
         ("C-c i f" . flyspell-mode))
  :config
  (defun my-flyspell-maybe-correct-transposition (beg end candidates)
    (unless (let (case-fold-search)
              (string-match "\\`[A-Z0-9]+\\'"
                            (buffer-substring-no-properties beg end)))
      (flyspell-maybe-correct-transposition beg end candidates))))

(use-package focus
  :commands focus-mode)

(use-package font-lock-studio
  :commands (font-lock-studio
             font-lock-studio-region))

(use-package forge
  :after magit
  :preface
  (defun my-quick-create-pull-request (title branch)
    (interactive "sTitle: \nsBranch: ")
    (setq branch (concat "johnw/" branch))
    ;; Split this commit to another branch.
    (magit-branch-spinoff branch)
    ;; Push that branch to the remote.
    (call-interactively #'magit-push-current-to-pushremote)
    (sleep-for 3)
    ;; Create a pullreq using the same title.
    (forge-create-pullreq (concat "origin/" branch) "origin/master"))
  :config
  (transient-insert-suffix 'forge-dispatch "c i"
    '("p" "quick-pr" my-quick-create-pull-request))
  (remove-hook 'magit-status-sections-hook 'forge-insert-issues))

(use-package format-all
  :commands (format-all-buffer
             format-all-mode)
  :config
  (defun format-all--resolve-system (choices)
    "Get first choice matching `format-all--system-type' from CHOICES."
    (cl-dolist (choice choices)
      (cond ((atom choice)
             (cl-return choice))
            ((eql format-all--system-type (car choice))
             (cl-return (cadr choice)))))))

(use-package free-keys
  :commands free-keys)

(use-package fullframe
  :defer t
  :init
  (autoload #'fullframe "fullframe"))

(use-package ggtags
  ;; jww (2017-12-10): Need to configure.
  :disabled t
  :commands ggtags-mode
  :diminish)

(use-package gist
  :no-require t
  :bind ("C-c G" . my-gist-region-or-buffer)
  :preface
  (defun my-gist-region-or-buffer (start end)
    (interactive "r")
    (copy-region-as-kill start end)
    (deactivate-mark)
    (let ((file-name buffer-file-name))
      (with-temp-buffer
        (if file-name
            (call-process "gist" nil t nil "-f" file-name "-P")
          (call-process "gist" nil t nil "-P"))
        (kill-ring-save (point-min) (1- (point-max)))
        (message (buffer-substring (point-min) (1- (point-max))))))))

(use-package git-annex
  :load-path "lisp/git-annex"
  :after dired
  :defer t)

(use-package git-link
  :bind ("C-c Y" . git-link)
  :commands (git-link git-link-commit git-link-homepage))

(use-package git-timemachine
  :commands git-timemachine)

(use-package git-undo
  :load-path "lisp/git-undo"
  :commands git-undo)

(use-package gitattributes-mode
  :defer 5)

(use-package gitconfig-mode
  :defer 5)

(use-package gitignore-mode
  :defer 5)

(use-package github-review
  :after forge
  :commands github-review-start
  :config
  (transient-insert-suffix 'forge-dispatch "c p"
    '("c r" "github-review" github-review-forge-pr-at-point)))

(use-package gitpatch
  :commands gitpatch-mail)

(use-package go-jira
  :no-require t
  :init
  (defvar jira-token nil)
  (defun jira-create ()
    (interactive)
    (unless jira-token
      (setq jira-token (lookup-password "go-jira.atlassian.net" "johnw" 6697)))
    (setenv "JIRA_API_TOKEN" jira-token)
    (require 'with-editor)
    (start-process "go-jira" (get-buffer-create " *go-jira*")
                   "jira" "create" "-b"
                   "--editor" (concat with-editor-emacsclient-executable
                                      " -s /tmp/emacs501/server")
                   "-t" (expand-file-name "~/doc/tasks/jira.template"))))

(use-package google-this
  :bind-keymap ("C-c /" . google-this-mode-submap)
  :bind* ("M-SPC" . google-this-search)
  :bind (:map google-this-mode-map
              ("/" . google-this-search)))

(use-package goto-last-change
  :bind ("C-x C-/" . goto-last-change))

(use-package goto-line-preview
  :config
  (global-set-key [remap goto-line] 'goto-line-preview))

(use-package graphviz-dot-mode
  :mode "\\.dot\\'")

(use-package grep
  :bind (("M-s n" . find-name-dired)
         ("M-s F" . find-grep)
         ("M-s G" . grep)
         ("M-s d" . find-grep-dired)))

(use-package gud
  :commands gud-gdb
  :bind (("<f9>"    . gud-cont)
         ("<f10>"   . gud-next)
         ("<f11>"   . gud-step)
         ("S-<f11>" . gud-finish))
  :init
  (defun show-debugger ()
    (interactive)
    (let ((gud-buf
           (catch 'found
             (dolist (buf (buffer-list))
               (if (string-match "\\*gud-" (buffer-name buf))
                   (throw 'found buf))))))
      (if gud-buf
          (switch-to-buffer-other-window gud-buf)
        (call-interactively 'gud-gdb)))))

(use-package haskell-edit
  :load-path "lisp/haskell-config"
  :after haskell-mode
  :bind (:map haskell-mode-map
              ("C-c M-q" . haskell-edit-reformat)))

(use-package haskell-mode
  :mode (("\\.hs\\(c\\|-boot\\)?\\'" . haskell-mode)
         ("\\.lhs\\'" . literate-haskell-mode)
         ("\\.cabal\\'" . haskell-cabal-mode))
  :bind (:map haskell-mode-map
              ("C-c C-h" . my-haskell-hoogle)
              ("C-c C-," . haskell-navigate-imports)
              ("C-c C-." . haskell-mode-format-imports)
              ("C-c C-u" . my-haskell-insert-undefined)
              ("M-s")
              ("M-t"))
  :preface
  (defun my-haskell-insert-undefined ()
    (interactive) (insert "undefined"))

  (defun snippet (name)
    (interactive "sName: ")
    (find-file (expand-file-name (concat name ".hs") "~/src/notes"))
    (haskell-mode)
    (goto-char (point-min))
    (when (eobp)
      (insert "hdr")
      (yas-expand)))

  (defvar hoogle-server-process nil)
  (defun my-haskell-hoogle (query &optional arg)
    "Do a Hoogle search for QUERY."
    (interactive
     (let ((def (haskell-ident-at-point)))
       (if (and def (symbolp def)) (setq def (symbol-name def)))
       (list (read-string (if def
                              (format "Hoogle query (default %s): " def)
                            "Hoogle query: ")
                          nil nil def)
             current-prefix-arg)))
    (let ((pe process-environment)
          (ep exec-path)
          (default-hoo (expand-file-name
                        "default.hoo"
                        (locate-dominating-file "." "default.hoo"))))
      (unless (and hoogle-server-process
                   (process-live-p hoogle-server-process))
        (message "Starting local Hoogle server on port 8687...")
        (with-current-buffer (get-buffer-create " *hoogle-web*")
          (cd temporary-file-directory)
          (let ((process-environment pe)
                (exec-path ep))
            (setq hoogle-server-process
                  (start-process "hoogle-web" (current-buffer)
                                 (executable-find "hoogle")
                                 "server"
                                 ;; (concat "--database=" default-hoo)
                                 "--local" "--port=8687"))))
        (message "Starting local Hoogle server on port 8687...done")))
    (browse-url
     (format "http://127.0.0.1:8687/?hoogle=%s"
             (replace-regexp-in-string
              " " "+" (replace-regexp-in-string "\\+" "%2B" query)))))

  (defvar haskell-prettify-symbols-alist
    '(("::"     . ?∷)
      ("forall" . ?∀)
      ("exists" . ?∃)
      ("->"     . ?→)
      ("<-"     . ?←)
      ("=>"     . ?⇒)
      ("~>"     . ?⇝)
      ("<~"     . ?⇜)
      ("<>"     . ?⨂)
      ("msum"   . ?⨁)
      ("\\"     . ?λ)
      ("not"    . ?¬)
      ("&&"     . ?∧)
      ("||"     . ?∨)
      ("/="     . ?≠)
      ("<="     . ?≤)
      (">="     . ?≥)
      ("<<<"    . ?⋘)
      (">>>"    . ?⋙)

      ("`elem`"             . ?∈)
      ("`notElem`"          . ?∉)
      ("`member`"           . ?∈)
      ("`notMember`"        . ?∉)
      ("`union`"            . ?∪)
      ("`intersection`"     . ?∩)
      ("`isSubsetOf`"       . ?⊆)
      ("`isNotSubsetOf`"    . ?⊄)
      ("`isSubsequenceOf`"  . ?⊆)
      ("`isProperSubsetOf`" . ?⊂)
      ("undefined"          . ?⊥)))

  :config
  (require 'haskell)
  (require 'haskell-doc)
  (require 'haskell-commands)

  (defun my-update-cabal-repl (&rest _args)
    (aif (getenv "CABAL_REPL")
        (let ((args (nthcdr 2 (split-string it))))
          (setq-local haskell-process-args-cabal-repl
                      (delete-dups
                       (append haskell-process-args-cabal-repl args))))))

  (defun my-haskell-mode-hook ()
    (haskell-indentation-mode)
    (interactive-haskell-mode)
    (diminish 'interactive-haskell-mode)
    (when (and (boundp 'brittany-enabled)
               brittany-enabled)
      (let ((brittany (find-brittany)))
        (when brittany
          (setq-local haskell-stylish-on-save t)
          (setq-local haskell-mode-stylish-haskell-path brittany)
          (setq-local haskell-mode-stylish-haskell-args '("-")))))
    (advice-add 'direnv-update-directory-environment
                :after #'my-update-cabal-repl)
    (whitespace-mode 1)
    (flycheck-mode 1)
    (flycheck-haskell-setup)
    (add-hook 'hack-local-variables-hook
              #'(lambda ()
                  (when nil
                    (setq-local flycheck-ghc-search-path nil)
                    (setq-local flycheck-ghc-args nil)))
              t)
    (setq-local prettify-symbols-alist haskell-prettify-symbols-alist)
    (prettify-symbols-mode 1)
    (bug-reference-prog-mode 1)
    (when (executable-find "ormolu")
      (require 'format-all)
      (define-format-all-formatter ormolu
        (:executable "ormolu")
        (:install "stack install ormolu")
        (:languages "Haskell" "Literate Haskell")
        (:features)
        (:format
         (format-all--buffer-easy
          executable
          (when (buffer-file-name)
            (list "--stdin-input-file" (buffer-file-name))))))
      (format-all--set-chain "Haskell" '(ormolu))
      ;; (format-all-mode 1)
      ))

  (add-hook 'haskell-mode-hook #'my-haskell-mode-hook)

  (eval-after-load 'align
    '(nconc
      align-rules-list
      (mapcar #'(lambda (x)
                  `(,(car x)
                    (regexp . ,(cdr x))
                    (modes quote (haskell-mode literate-haskell-mode))))
              '((haskell-types       . "\\(\\s-+\\)\\(::\\|∷\\)\\s-+")
                (haskell-assignment  . "\\(\\s-+\\)=\\s-+")
                (haskell-arrows      . "\\(\\s-+\\)\\(->\\|→\\)\\s-+")
                (haskell-left-arrows . "\\(\\s-+\\)\\(<-\\|←\\)\\s-+")))))

  (defun haskell-process-load-complete
      (session process buffer reload module-buffer &optional cont)
    "Handle the complete loading response. BUFFER is the string of
  text being sent over the process pipe. MODULE-BUFFER is the
  actual Emacs buffer of the module being loaded."
    (when (get-buffer (format "*%s:splices*" (haskell-session-name session)))
      (with-current-buffer (haskell-interactive-mode-splices-buffer session)
        (erase-buffer)))
    (let* ((ok (cond
                ((haskell-process-consume
                  process
                  "Ok, \\(?:\\([0-9]+\\|one\\)\\) modules? loaded\\.$")
                 t)
                ((haskell-process-consume
                  process
                  "Failed, \\(?:[0-9]+\\) modules? loaded\\.$")
                 nil)
                ((haskell-process-consume
                  process
                  "Ok, modules loaded: \\(.+\\)\\.$")
                 t)
                ((haskell-process-consume
                  process
                  "Failed, modules loaded: \\(.+\\)\\.$")
                 nil)
                (t
                 (error (message "Unexpected response from haskell process.")))))
           (modules (haskell-process-extract-modules buffer))
           (cursor (haskell-process-response-cursor process))
           (warning-count 0))
      (haskell-process-set-response-cursor process 0)
      (haskell-check-remove-overlays module-buffer)
      (while
          (haskell-process-errors-warnings module-buffer session process buffer)
        (setq warning-count (1+ warning-count)))
      (haskell-process-set-response-cursor process cursor)
      (if (and (not reload)
               haskell-process-reload-with-fbytecode)
          (haskell-process-reload-with-fbytecode process module-buffer)
        (haskell-process-import-modules process (car modules)))
      (if ok
          (haskell-mode-message-line (if reload "Reloaded OK." "OK."))
        (haskell-interactive-mode-compile-error session "Compilation failed."))
      (when cont
        (condition-case-unless-debug e
            (funcall cont ok)
          (error (message "%S" e))
          (quit nil))))))

(use-package hcl-mode
  :mode "\.nomad\\'")

(use-package helm
  :defer t
  :bind (:map helm-map
              ("<tab>" . helm-execute-persistent-action)
              ("C-i"   . helm-execute-persistent-action)
              ("C-z"   . helm-select-action)
              ("A-v"   . helm-previous-page))
  :config
  (helm-autoresize-mode 1))

(use-package helm-descbinds
  :bind ("C-h b" . helm-descbinds)
  :init
  (fset 'describe-bindings 'helm-descbinds))

(use-package helm-describe-modes
  :after helm
  :bind ("C-h m" . helm-describe-modes))

(use-package helm-firefox
  :bind ("A-M-b" . helm-firefox-bookmarks))

(use-package helm-font
  :commands (helm-select-xfont helm-ucs))

(use-package helm-google
  :commands helm-google)

(use-package helm-navi
  :after (helm navi)
  :commands helm-navi)

(use-package helm-sys
  :commands helm-top)

(use-package helpful
  :bind (("C-h e F" . helpful-function)
         ("C-h e C" . helpful-command)
         ("C-h e M" . helpful-macro)
         ("C-h e L" . helpful-callable)
         ("C-h e S" . helpful-at-point)
         ("C-h e V" . helpful-variable)))

(use-package hi-lock
  :bind (("M-o l" . highlight-lines-matching-regexp)
         ("M-o r" . highlight-regexp)
         ("M-o w" . highlight-phrase)))

(use-package hideif
  :diminish hide-ifdef-mode
  :hook (c-mode-common . hide-ifdef-mode))

(use-package hideshow
  :diminish hs-minor-mode
  :hook (prog-mode . hs-minor-mode)
  :bind (:map prog-mode-map
              ("C-c h" . hs-toggle-hiding)))

(use-package highlight
  :bind (("C-c H H" . hlt-highlight-region)
         ("C-c H U" . hlt-unhighlight-region)))

(use-package highlight-cl
  :hook (emacs-lisp-mode . highlight-cl-add-font-lock-keywords))

(use-package highlight-defined
  :commands highlight-defined-mode)

(use-package highlight-numbers
  :hook (prog-mode . highlight-numbers-mode))

(use-package hilit-chg
  :bind ("M-o C" . highlight-changes-mode))

(use-package hippie-exp
  :bind (("M-/"   . hippie-expand)
         ("C-M-/" . dabbrev-completion)))

(use-package hl-line
  :commands hl-line-mode
  :bind ("M-o h" . hl-line-mode))

(use-package hl-line+
  :after hl-line)

(use-package hydra
  :defer t
  :config
  (defhydra hydra-zoom (global-map "<f2>")
    "zoom"
    ("g" text-scale-increase "in")
    ("l" text-scale-decrease "out")))

(use-package ibuffer
  :bind ("C-x C-b" . ibuffer)
  :init
  (add-hook 'ibuffer-mode-hook
            #'(lambda ()
                (ibuffer-switch-to-saved-filter-groups "default"))))

(use-package iedit
  :defer t)

(use-package ielm
  :commands ielm
  :bind (:map ielm-map ("<return>" . my-ielm-return))
  :config
  (defun my-ielm-return ()
    (interactive)
    (let ((end-of-sexp (save-excursion
                         (goto-char (point-max))
                         (skip-chars-backward " \t\n\r")
                         (point))))
      (if (>= (point) end-of-sexp)
          (progn
            (goto-char (point-max))
            (skip-chars-backward " \t\n\r")
            (delete-region (point) (point-max))
            (call-interactively #'ielm-return))
        (call-interactively #'paredit-newline)))))

(use-package iflipb
  :disabled t
  :bind* ("<S-return>" . my-iflipb-next-buffer)
  :commands (iflipb-next-buffer iflipb-previous-buffer)
  :preface
  (defvar my-iflipb-auto-off-timeout-sec 1)
  (defvar my-iflipb-auto-off-timer nil)
  (defvar my-iflipb-auto-off-timer-canceler-internal nil)
  (defvar my-iflipb-ing-internal nil)

  (defun my-iflipb-auto-off ()
    (setq my-iflipb-auto-off-timer-canceler-internal nil
          my-iflipb-ing-internal nil)
    (when my-iflipb-auto-off-timer
      (message nil)
      (cancel-timer my-iflipb-auto-off-timer)
      (setq my-iflipb-auto-off-timer nil)))

  (defun my-iflipb-next-buffer (arg)
    (interactive "P")
    (iflipb-next-buffer arg)
    (if my-iflipb-auto-off-timer-canceler-internal
        (cancel-timer my-iflipb-auto-off-timer-canceler-internal))
    (setq my-iflipb-auto-off-timer
          (run-with-idle-timer my-iflipb-auto-off-timeout-sec 0
                               'my-iflipb-auto-off)
          my-iflipb-ing-internal t))

  (defun my-iflipb-previous-buffer ()
    (interactive)
    (iflipb-previous-buffer)
    (if my-iflipb-auto-off-timer-canceler-internal
        (cancel-timer my-iflipb-auto-off-timer-canceler-internal))
    (setq my-iflipb-auto-off-timer
          (run-with-idle-timer my-iflipb-auto-off-timeout-sec 0
                               'my-iflipb-auto-off)
          my-iflipb-ing-internal t))

  :config
  (setq iflipb-always-ignore-buffers
        "\\`\\( \\|diary\\|ipa\\|\\.newsrc-dribble\\'\\)"
        iflipb-wrap-around t)

  (defun iflipb-first-iflipb-buffer-switch-command ()
    (not (and (or (eq last-command 'my-iflipb-next-buffer)
                  (eq last-command 'my-iflipb-previous-buffer))
              my-iflipb-ing-internal))))

(use-package image-file
  :defer 5
  :config
  (auto-image-file-mode 1)
  (add-hook 'image-mode-hook #'image-transform-reset))

(use-package imenu-list
  :commands imenu-list-minor-mode)

(use-package indent
  :commands indent-according-to-mode)

(use-package indent-shift
  :bind (("C-c <" . indent-shift-left)
         ("C-c >" . indent-shift-right)))

(use-package info
  :bind ("C-h C-i" . info-lookup-symbol)
  :config
  (add-hook 'Info-mode-hook
            #'(lambda ()
                (setq buffer-face-mode-face '(:family "Bookerly"))
                (buffer-face-mode)
                (text-scale-adjust 1))))

(use-package info-look
  :defer t
  :init
  (autoload 'info-lookup-add-help "info-look"))

(use-package info-lookmore
  :after info-look
  :config
  (info-lookmore-elisp-cl)
  (info-lookmore-elisp-userlast)
  (info-lookmore-elisp-gnus)
  (info-lookmore-apropos-elisp))

(use-package initsplit
  :demand t
  :load-path "lisp/initsplit")

(use-package ialign
  :bind ("C-c {" . ialign-interactive-align))

(use-package inventory
  :commands (inventory sort-package-declarations))

(use-package ipcalc
  :commands ipcalc)

(use-package isearch
  :no-require t
  :bind (("C-M-r" . isearch-backward-other-window)
         ("C-M-s" . isearch-forward-other-window))
  :bind (:map isearch-mode-map
              ("C-c" . isearch-toggle-case-fold)
              ("C-t" . isearch-toggle-regexp)
              ("C-^" . isearch-edit-string)
              ("C-i" . isearch-complete))
  :preface
  (defun isearch-backward-other-window ()
    (interactive)
    (split-window-vertically)
    (other-window 1)
    (call-interactively 'isearch-backward))

  (defun isearch-forward-other-window ()
    (interactive)
    (split-window-vertically)
    (other-window 1)
    (call-interactively 'isearch-forward)))

(use-package ispell
  :no-require t
  :bind (("C-c i c" . ispell-comments-and-strings)
         ("C-c i d" . ispell-change-dictionary)
         ("C-c i k" . ispell-kill-ispell)
         ("C-c i m" . ispell-message)
         ("C-c i r" . ispell-region)))

(use-package ivy
  :diminish
  :demand t

  :bind (("C-x b" . ivy-switch-buffer)
         ("C-x B" . ivy-switch-buffer-other-window)
         ("M-H"   . ivy-resume))

  :bind (:map ivy-minibuffer-map
              ("<tab>" . ivy-alt-done)
              ("SPC"   . ivy-alt-done-or-space)
              ("C-d"   . ivy-done-or-delete-char)
              ("C-i"   . ivy-partial-or-done)
              ("C-r"   . ivy-previous-line-or-history)
              ("M-r"   . ivy-reverse-i-search))

  :bind (:map ivy-switch-buffer-map
              ("C-k" . ivy-switch-buffer-kill))

  :custom
  (ivy-dynamic-exhibit-delay-ms 200)
  (ivy-height 10)
  (ivy-initial-inputs-alist nil t)
  (ivy-magic-tilde nil)
  (ivy-re-builders-alist '((t . ivy--regex-ignore-order)))
  (ivy-use-virtual-buffers t)
  (ivy-wrap t)

  :preface
  (defun ivy-done-or-delete-char ()
    (interactive)
    (call-interactively
     (if (eolp)
         #'ivy-immediate-done
       #'ivy-delete-char)))

  (defun ivy-alt-done-or-space ()
    (interactive)
    (call-interactively
     (if (= ivy--length 1)
         #'ivy-alt-done
       #'self-insert-command)))

  (defun ivy-switch-buffer-kill ()
    (interactive)
    (debug)
    (let ((bn (ivy-state-current ivy-last)))
      (when (get-buffer bn)
        (kill-buffer bn))
      (unless (buffer-live-p (ivy-state-buffer ivy-last))
        (setf (ivy-state-buffer ivy-last)
              (with-ivy-window (current-buffer))))
      (setq ivy--all-candidates (delete bn ivy--all-candidates))
      (ivy--exhibit)))

  ;; This is the value of `magit-completing-read-function', so that we see
  ;; Magit's own sorting choices.
  (defun my-ivy-completing-read (&rest args)
    (let ((ivy-sort-functions-alist '((t . nil))))
      (apply 'ivy-completing-read args)))

  :config
  (ivy-mode 1)
  (ivy-set-occur 'ivy-switch-buffer 'ivy-switch-buffer-occur)

  (defun ivy--switch-buffer-matcher (regexp candidates)
    "Return REGEXP matching CANDIDATES.
Skip buffers that match `ivy-ignore-buffers'."
    (let ((res (ivy--re-filter regexp candidates)))
      (if (or (null ivy-use-ignore)
              (null ivy-ignore-buffers))
          res
        (or (cl-remove-if
             (lambda (buf)
               (cl-find-if
                (lambda (f-or-r)
                  (if (functionp f-or-r)
                      (funcall f-or-r buf)
                    (string-match-p f-or-r buf)))
                ivy-ignore-buffers))
             res)
            (and (eq ivy-use-ignore t)
                 res))))))

(use-package ivy-bibtex
  :commands ivy-bibtex)

(use-package ivy-hydra
  :after (ivy hydra)
  :defer t)

(use-package ivy-pass
  :commands ivy-pass)

(use-package ivy-rich
  :after ivy
  :demand t
  :config
  (ivy-rich-mode 1)
  (setq ivy-virtual-abbreviate 'full
        ivy-rich-switch-buffer-align-virtual-buffer t
        ivy-rich-path-style 'abbrev))

(use-package ivy-rtags
  :disabled t
  :load-path "~/.nix-profile/share/emacs/site-lisp/rtags"
  :after (ivy rtags))

(use-package jq-mode
  :mode "\\.jq\\'")

(use-package js2-mode
  :mode "\\.js\\'"
  :config
  (add-to-list 'flycheck-disabled-checkers #'javascript-jshint)
  (flycheck-add-mode 'javascript-eslint 'js2-mode)
  (flycheck-mode 1))

(use-package js3-mode
  ;; jww (2017-12-10): Need to configure.
  :disabled t)

(use-package json-mode
  :mode "\\.json\\'")

(use-package json-reformat
  :after json-mode)

(use-package json-snatcher
  :after json-mode)

(use-package key-chord
  :commands key-chord-mode)

(use-package keypression
  :commands key-chord-mode)

(use-package know-your-http-well
  :commands (http-header
             http-method
             http-relation
             http-status-code
             media-type))

(use-package kotl-mode
  :mode "\\.kotl\\'")

(use-package latex
  :config
  (require 'preview)
  ;; (load (emacs-path "site-lisp/auctex/style/minted"))

  (info-lookup-add-help :mode 'LaTeX-mode
                        :regexp ".*"
                        :parse-rule "\\\\?[a-zA-Z]+\\|\\\\[^a-zA-Z]"
                        :doc-spec '(("(latex2e)Concept Index")
                                    ("(latex2e)Command Index")))

  (defvar latex-prettify-symbols-alist
    '(("\N{THIN SPACE}" . ?\⟷)))

  (bind-key "C-x SPC"
            #'(lambda ()
                (interactive)
                (insert "\N{THIN SPACE}"))
            LaTeX-mode-map)
  (bind-key "C-x A"
            #'(lambda ()
                (interactive)
                (insert "ٰ"))
            LaTeX-mode-map)
  (bind-key "A-َ"
            #'(lambda ()
                (interactive)
                (insert "ٰ"))
            LaTeX-mode-map)
  (bind-key "A-ه"
            #'(lambda ()
                (interactive)
                (insert "ۀ"))
            LaTeX-mode-map)
  (bind-key "A-د"
            #'(lambda ()
                (interactive)
                (insert "ذ"))
            LaTeX-mode-map)
  (bind-key "A-ت"
            #'(lambda ()
                (interactive)
                (insert "ة"))
            LaTeX-mode-map)

  (add-hook 'LaTeX-mode-hook
            #'(lambda
                ()
                (setq-local prettify-symbols-alist latex-prettify-symbols-alist)
                (prettify-symbols-mode 1))))

(use-package ledger-mode
  :mode "\\.ledger\\'"
  :load-path "~/src/ledger/lisp"
  :commands ledger-mode
  :bind ("C-c L" . my-ledger-start-entry)
  :preface
  (defun my-ledger-start-entry (&optional arg)
    (interactive "p")
    (find-file-other-window "/Volumes/Files/Accounts/ledger.dat")
    (goto-char (point-max))
    (skip-syntax-backward " ")
    (if (looking-at "\n\n")
        (goto-char (point-max))
      (delete-region (point) (point-max))
      (insert ?\n)
      (insert ?\n))
    (insert (format-time-string "%Y/%m/%d ")))

  (defun ledger-matchup ()
    (interactive)
    (while (re-search-forward "\\(\\S-+Unknown\\)\\s-+\\$\\([-,0-9.]+\\)"
                              nil t)
      (let ((account-beg (match-beginning 1))
            (account-end (match-end 1))
            (amount (match-string 2))
            account answer)
        (goto-char account-beg)
        (set-window-point (get-buffer-window) (point))
        (recenter)
        (redraw-display)
        (with-current-buffer (get-buffer "nrl-mastercard-old.dat")
          (goto-char (point-min))
          (when (re-search-forward (concat "\\(\\S-+\\)\\s-+\\$" amount)
                                   nil t)
            (setq account (match-string 1))
            (goto-char (match-beginning 1))
            (set-window-point (get-buffer-window) (point))
            (recenter)
            (redraw-display)
            (setq answer
                  (read-char (format "Is this a match for %s (y/n)? "
                                     account)))))
        (when (eq answer ?y)
          (goto-char account-beg)
          (delete-region account-beg account-end)
          (insert account))
        (forward-line))))

  (defun my-ledger-add-symbols ()
    (interactive)
    (while (re-search-forward " \\(BOT\\|SOLD\\) [+-][0-9,]+ \\(\\S-+\\) " nil t)
      (forward-line 2)
      (goto-char (line-beginning-position))
      (insert "    ; Symbol: " (match-string 2) ?\n)))
  :config
  (add-hook 'ledger-mode-hook
            #'(lambda ()
                (auto-fill-mode -1))))

(use-package link-hint
  :defer 10
  :bind ("C-c C-o" . link-hint-open-link)
  :config
  (add-hook 'eww-mode-hook
            #'(lambda () (bind-key "f" #'link-hint-open-link eww-mode-map)))
  (add-hook 'w3m-mode-hook
            #'(lambda () (bind-key "f" #'link-hint-open-link w3m-mode-map))))

(use-package lively
  :bind ("C-x C-E" . lively))

(use-package lisp-mode
  :defer t
  :hook ((emacs-lisp-mode lisp-mode)
         . (lambda () (add-hook 'after-save-hook #'check-parens nil t)))
  :init
  (dolist (mode '(ielm-mode
                  inferior-emacs-lisp-mode
                  inferior-lisp-mode
                  lisp-interaction-mode
                  lisp-mode
                  emacs-lisp-mode))
    (font-lock-add-keywords
     mode
     '(("(\\(lambda\\)\\>"
        (0 (ignore
            (compose-region (match-beginning 1)
                            (match-end 1) ?λ))))
       ("(\\(ert-deftest\\)\\>[         '(]*\\(setf[    ]+\\sw+\\|\\sw+\\)?"
        (1 font-lock-keyword-face)
        (2 font-lock-function-name-face
           nil t))))))

(use-package lispy
  :commands lispy-mode
  :bind (:map lispy-mode-map
              ("M-j"))
  :bind (:map emacs-lisp-mode-map
              ("C-1"     . lispy-describe-inline)
              ("C-2"     . lispy-arglist-inline)
              ("C-c C-j" . lispy-goto)))

(use-package llvm-mode
  :disabled t
  :mode "\\.ll\\'")

(use-package lsp-haskell
  :after lsp-mode
  :config
  (setq lsp-haskell-server-path "haskell-language-server-wrapper"))

(use-package lsp-mode
  :commands lsp
  :custom
  (lsp-completion-enable t)
  (lsp-completion-provider :capf)
  (lsp-eldoc-enable-hover nil)
  (lsp-eldoc-render-all t)
  (lsp-enable-eldoc nil)
  (lsp-haskell-process-args-hie '("-l" "/tmp/hie.log"))
  (lsp-headerline-breadcrumb-enable nil)
  (lsp-highlight-symbol-at-point nil)
  (lsp-idle-delay 0.6)
  (lsp-inhibit-message t)
  (lsp-prefer-capf t)
  (lsp-prefer-flymake nil)
  ;; what to use when checking on-save. "check" is default, I prefer clippy
  (lsp-rust-analyzer-cargo-watch-command "clippy")
  (lsp-rust-analyzer-server-display-inlay-hints t)
  (lsp-rust-clippy-preference "on")
  :config
  (use-package lsp-lens)
  (use-package lsp-headerline)
  (setq read-process-output-max 16384
        gc-cons-threshold 1600000))

(use-package lsp-ui
  :after lsp-mode
  :hook (lsp-mode . lsp-ui-mode)
  :custom
  (lsp-ui-doc-enable nil)
  (lsp-ui-doc-max-height 60)
  (lsp-ui-doc-text-scale-level 4)
  (lsp-ui-peek-always-show t)
  (lsp-ui-sideline-enable nil)
  (lsp-ui-sideline-show-diagnostics nil)
  (lsp-ui-sideline-show-hover t)
  :config
  (define-key lsp-ui-mode-map [remap xref-find-definitions]
    #'lsp-ui-peek-find-definitions)
  (define-key lsp-ui-mode-map [remap xref-find-references]
    #'lsp-ui-peek-find-references))

(use-package lua-mode
  :mode "\\.lua\\'"
  :interpreter "lua")

(use-package macrostep
  :bind ("C-c e m" . macrostep-expand))

(use-package magit
  :bind (("C-x g" . magit-status)
         ("C-x G" . magit-status-with-prefix))
  :bind (:map magit-mode-map
              ("U" . magit-unstage-all)
              ("M-h") ("M-s") ("M-m") ("M-w"))
  :bind (:map magit-file-section-map ("<C-return>"))
  :bind (:map magit-hunk-section-map ("<C-return>"))
  :preface
  ;; History can be viewed with:
  ;; git log refs/snapshots/$(git symbolic-ref HEAD)
  (defun magit-monitor (&optional no-display)
    "Start git-monitor in the current directory."
    (interactive)
    (let* ((path (file-truename
                  (directory-file-name
                   (expand-file-name default-directory))))
           (name (format "*git-monitor: %s*"
                         (file-name-nondirectory path))))
      (unless (and (get-buffer name)
                   (with-current-buffer (get-buffer name)
                     (string= path (directory-file-name default-directory))))
        (with-current-buffer (get-buffer-create name)
          (cd path)
          (if (file-regular-p ".git")
              (let ((branch (string-chop-newline
                             (shell-command-to-string
                              "git branch --show-current")))
                    (repo
                     (with-temp-buffer
                       (insert-file-contents-literally ".git")
                       (goto-char (point-min))
                       (and (looking-at "^gitdir: \\(.+?/\\.git/\\)")
                            (match-string 1)))))
                (when repo
                  (ignore-errors
                    (start-process "*git-monitor*" (current-buffer)
                                   "git-monitor"
                                   "--git-dir" repo
                                   "--work-dir" path
                                   "-r" (concat "refs/heads/" branch)))))
            (ignore-errors
              (start-process "*git-monitor*" (current-buffer)
                             "git-monitor" "--work-dir" path)))))))

  (defun magit-status-with-prefix ()
    (interactive)
    (let ((current-prefix-arg '(4)))
      (call-interactively 'magit-status)))

  (defun endless/visit-pull-request-url ()
    "Visit the current branch's PR on Github."
    (interactive)
    (browse-url
     (format "https://github.com/%s/pull/new/%s"
             (replace-regexp-in-string
              "\\`.+github\\.com:\\(.+?\\)\\(\\.git\\)?\\'" "\\1"
              (magit-get "remote" (magit-get-remote) "url"))
             (magit-get-current-branch))))

  :hook (magit-mode . hl-line-mode)
  :config
  (use-package magit-commit
    :config
    (use-package git-commit))

  (use-package magit-files
    :config
    ;;(global-magit-file-mode)
    )

  (add-hook 'magit-status-mode-hook #'(lambda () (magit-monitor t)))

  (define-key magit-mode-map "G" #'endless/visit-pull-request-url)

  (eval-after-load 'magit-pull
    '(transient-insert-suffix 'magit-pull "p"
       '("F" "default" magit-fetch-from-upstream)))

  (eval-after-load 'magit-push
    '(transient-insert-suffix 'magit-push "p"
       '("P" "default" magit-push-current-to-upstream)))

  ;; (remove-hook 'magit-status-sections-hook 'magit-insert-status-headers)
  ;; (remove-hook 'magit-status-sections-hook 'magit-insert-tags-header)
  ;; (remove-hook 'magit-status-sections-hook 'magit-insert-unpushed-to-pushremote)
  ;; (remove-hook 'magit-status-sections-hook 'magit-insert-unpushed-to-upstream-or-recent)
  ;; (remove-hook 'magit-status-sections-hook 'magit-insert-unpulled-from-pushremote)
  ;; (remove-hook 'magit-status-sections-hook 'magit-insert-unpulled-from-upstream)
  )

(use-package magit-popup
  :defer t)

(use-package magit-imerge
  ;; jww (2017-12-10): Need to configure.
  :disabled t
  :after magit)

(use-package malyon
  :commands malyon
  :config
  (defun replace-invisiclues ()
    (interactive)
    (query-replace-regexp
     "^\\( +\\)\\(\\([A-Z]\\)\\. \\)?\\(.+\\)"
     (quote (replace-eval-replacement
             concat "\\1\\2" (replace-quote (rot13 (match-string 4)))))
     nil (if (use-region-p) (region-beginning))
     (if (use-region-p) (region-end)) nil nil)))

(use-package markdown-mode
  :mode (("\\`README\\.md\\'" . gfm-mode)
         ("\\.md\\'"          . markdown-mode)
         ("\\.markdown\\'"    . markdown-mode))
  :init (setq markdown-command "multimarkdown"))

(use-package markdown-preview-mode
  :after markdown-mode
  :config
  (setq markdown-preview-stylesheets
        (list (concat "https://github.com/dmarcotte/github-markdown-preview/"
                      "blob/master/data/css/github.css"))))

(use-package math-symbol-lists
  :defer t)

(use-package mc-calc
  :after multiple-cursors
  :bind (("<C-m> = c" . mc-calc)
         ("<C-m> = =" . mc-calc-eval)
         ("<C-m> = g" . mc-calc-grab)
         ("<C-m> = b" . mc-calc-copy-to-buffer)))

(use-package mc-extras
  :after multiple-cursors
  :bind (("<C-m> M-C-f" . mc/mark-next-sexps)
         ("<C-m> M-C-b" . mc/mark-previous-sexps)
         ("<C-m> <"     . mc/mark-all-above)
         ("<C-m> >"     . mc/mark-all-below)
         ("<C-m> C-d"   . mc/remove-current-cursor)
         ("<C-m> C-k"   . mc/remove-cursors-at-eol)
         ("<C-m> M-d"   . mc/remove-duplicated-cursors)
         ("<C-m> |"     . mc/move-to-column)
         ("<C-m> ~"     . mc/compare-chars)))

(use-package mc-freeze
  :after multiple-cursors
  :bind ("<C-m> f" . mc/freeze-fake-cursors-dwim))

(use-package mc-rect
  :after multiple-cursors
  :bind ("<C-m> ]" . mc/rect-rectangle-to-multiple-cursors))

(use-package mediawiki
  :commands mediawiki-open)

(use-package memory-usage
  :commands memory-usage)

(use-package mhtml-mode
  :bind (:map html-mode-map
              ("<return>" . newline-and-indent)))

(use-package mic-paren
  :defer 5
  :config
  (paren-activate))

(use-package midnight
  :bind ("C-c z" . clean-buffer-list))

(use-package minibuffer
  :config
  (defun my-minibuffer-setup-hook ()
    (setq gc-cons-threshold most-positive-fixnum))

  (defun my-minibuffer-exit-hook ()
    (setq gc-cons-threshold 800000))

  (add-hook 'minibuffer-setup-hook #'my-minibuffer-setup-hook)
  (add-hook 'minibuffer-exit-hook #'my-minibuffer-exit-hook))

(use-package minimap
  :commands minimap-mode)

(use-package mmm-mode
  :defer t)

(use-package moccur-edit
  :after color-moccur)

(use-package monitor
  :defer t
  :init
  (autoload #'define-monitor "monitor"))

(use-package motoko-mode
  :mode (("\\.mo\\'" . motoko-mode)))

(use-package mule
  :no-require t
  :config
  (prefer-coding-system 'utf-8)
  (set-terminal-coding-system 'utf-8)
  (setq x-select-request-type '(UTF8_STRING COMPOUND_TEXT TEXT STRING)))

(use-package multi-term
  :bind (("C-c t" . multi-term-next)
         ("C-c T" . multi-term))
  :init
  (defun screen ()
    (interactive)
    (let (term-buffer)
      ;; Set buffer.
      (setq term-buffer
            (let ((multi-term-program (executable-find "screen"))
                  (multi-term-program-switches "-DR"))
              (multi-term-get-buffer)))
      (set-buffer term-buffer)
      (multi-term-internal)
      (switch-to-buffer term-buffer)))

  :config
  (require 'term)

  (defalias 'my-term-send-raw-at-prompt 'term-send-raw)

  (defun my-term-end-of-buffer ()
    (interactive)
    (call-interactively #'end-of-buffer)
    (if (and (eobp) (bolp))
        (delete-char -1)))

  (defadvice term-process-pager (after term-process-rebind-keys activate)
    (define-key term-pager-break-map  "\177" 'term-pager-back-page)))

(use-package multifiles
  :bind ("C-c m f" . mf/mirror-region-in-multifile))

(use-package multiple-cursors
  :after phi-search
  :defer 5

  ;; - Sometimes you end up with cursors outside of your view. You can scroll
  ;;   the screen to center on each cursor with `C-v` and `M-v`.
  ;;
  ;; - If you get out of multiple-cursors-mode and yank - it will yank only
  ;;   from the kill-ring of main cursor. To yank from the kill-rings of every
  ;;   cursor use yank-rectangle, normally found at C-x r y.

  :bind (("<C-m> ^"     . mc/edit-beginnings-of-lines)
         ("<C-m> `"     . mc/edit-beginnings-of-lines)
         ("<C-m> $"     . mc/edit-ends-of-lines)
         ("<C-m> '"     . mc/edit-ends-of-lines)
         ("<C-m> R"     . mc/reverse-regions)
         ("<C-m> S"     . mc/sort-regions)
         ("<C-m> W"     . mc/mark-all-words-like-this)
         ("<C-m> Y"     . mc/mark-all-symbols-like-this)
         ("<C-m> a"     . mc/mark-all-like-this-dwim)
         ("<C-m> c"     . mc/mark-all-dwim)
         ("<C-m> l"     . mc/insert-letters)
         ("<C-m> n"     . mc/insert-numbers)
         ("<C-m> r"     . mc/mark-all-in-region)
         ("<C-m> s"     . set-rectangular-region-anchor)
         ("<C-m> %"     . mc/mark-all-in-region-regexp)
         ("<C-m> t"     . mc/mark-sgml-tag-pair)
         ("<C-m> w"     . mc/mark-next-like-this-word)
         ("<C-m> x"     . mc/mark-more-like-this-extended)
         ("<C-m> y"     . mc/mark-next-like-this-symbol)
         ("<C-m> C-x"   . reactivate-mark)
         ("<C-m> C-SPC" . mc/mark-pop)
         ("<C-m> ("     . mc/mark-all-symbols-like-this-in-defun)
         ("<C-m> C-("   . mc/mark-all-words-like-this-in-defun)
         ("<C-m> M-("   . mc/mark-all-like-this-in-defun)
         ("<C-m> ["     . mc/vertical-align-with-space)
         ("<C-m> {"     . mc/vertical-align)

         ("S-<down-mouse-1>")
         ("S-<mouse-1>" . mc/add-cursor-on-click))

  :bind (:map selected-keymap
              ("c"   . mc/edit-lines)
              ("."   . mc/mark-next-like-this)
              ("<"   . mc/unmark-next-like-this)
              ("C->" . mc/skip-to-next-like-this)
              (","   . mc/mark-previous-like-this)
              (">"   . mc/unmark-previous-like-this)
              ("C-<" . mc/skip-to-previous-like-this)
              ("y"   . mc/mark-next-symbol-like-this)
              ("Y"   . mc/mark-previous-symbol-like-this)
              ("w"   . mc/mark-next-word-like-this)
              ("W"   . mc/mark-previous-word-like-this))

  :preface
  (defun reactivate-mark ()
    (interactive)
    (activate-mark)))

(use-package nginx-mode
  :commands nginx-mode)

(use-package nix-shell
  :no-require t
  :init
  (defun nix-shell ()
    (interactive)
    (let ((explicit-shell-file-name "shell")
          (explicit-shell-args nil))
      (call-interactively 'shell))))

(use-package nix-mode
  :mode "\\.nix\\'")

(use-package nix-update
  :load-path "lisp/nix-update"
  :bind ("C-c U" . nix-update-fetch))

(use-package nov
  :mode ("\\.epub\\'" . nov-mode))

(use-package nroff-mode
  :commands nroff-mode
  :config
  (defun update-nroff-timestamp ()
    (save-excursion
      (goto-char (point-min))
      (when (re-search-forward "^\\.Dd " nil t)
        (let ((stamp (format-time-string "%B %e, %Y")))
          (unless (looking-at stamp)
            (delete-region (point) (line-end-position))
            (insert stamp)
            (let (after-save-hook)
              (save-buffer)))))))

  (add-hook 'nroff-mode-hook
            #'(lambda () (add-hook 'after-save-hook #'update-nroff-timestamp nil t))))

(use-package nxml-mode
  :commands nxml-mode
  :bind (:map nxml-mode-map
              ("<return>" . newline-and-indent)
              ("C-c M-h"  . tidy-xml-buffer))
  :preface
  (defun tidy-xml-buffer ()
    (interactive)
    (save-excursion
      (call-process-region (point-min) (point-max) "tidy" t t nil
                           "-xml" "-i" "-wrap" "0" "-omit" "-q" "-utf8")))
  :init
  (defalias 'xml-mode 'nxml-mode)
  :config
  (autoload 'sgml-skip-tag-forward "sgml-mode")
  (add-to-list 'hs-special-modes-alist
               '(nxml-mode
                 "<!--\\|<[^/>]*[^/]>"
                 "-->\\|</[^/>]*[^/]>"
                 "<!--"
                 sgml-skip-tag-forward
                 nil)))

(use-package olivetti
  :commands olivetti-mode)

(use-package operate-on-number
  :bind ("C-c N" . operate-on-number-at-point))

(use-package origami
  :hook (rust-mode . origami-mode)
  :bind (:map origami-mode-map
              ("C-, C-h" . origami-toggle-node))
  :init
  ;; We need to tell origami how to work under rust mode
  (with-eval-after-load "origami"
    (add-to-list 'origami-parser-alist '(rust-mode . origami-c-style-parser)))
  :custom
  ;; Highlights the line the fold starts on
  (origami-show-fold-header t)
  :config
  (defun origami-header-overlay-range (fold-overlay)
    "Given a `fold-overlay', return the range that the corresponding
header overlay should cover. Result is a cons cell of (begin . end)."
    (with-current-buffer (overlay-buffer fold-overlay)
      (let ((fold-begin
             (save-excursion
               (goto-char (overlay-start fold-overlay))
               (line-beginning-position)))
            (fold-end
             ;; Find the end of the folded region -- include the following
             ;; newline if possible. The header will span the entire fold.
             (save-excursion
               (save-match-data
                 (goto-char (overlay-end fold-overlay))
                 (when (looking-at ".")
                   (forward-char 1)
                   (when (looking-at "\n")
                     (forward-char 1)))
                 (point)))))
        (cons fold-begin fold-end)))))

(use-package outline
  :diminish outline-minor-mode
  :hook ((emacs-lisp-mode LaTeX-mode) . outline-minor-mode))

(use-package ovpn-mode
  :commands ovpn
  :config
  (advice-add
   'ovpn-mode-pull-authinfo :around
   #'(lambda (ad-do-it config)
       (if (string= config "OpenVPN_PoC_2019_johnwiegley.ovpn")
           (list "johnwiegley"
                 (concat (lookup-password "demonet OpenVPN" "johnwiegley" 80)
                         (password-store--run "otp" "demonet OpenVPN")))
         (funcall ad-do-it config)))))

(use-package package-lint
  :commands package-lint-current-buffer)

(use-package pact-mode
  :mode "\\.pact\\'"
  :config
  (add-hook 'pact-mode-hook
            #'(lambda ()
                (bind-key "C-c C-c"
                          #'(lambda () (interactive)
                              (save-excursion
                                (call-interactively 'pact-compile)))
                          'slime-mode-map))))

(use-package pandoc-mode
  :hook (markdown-mode
         (pandoc-mode   . pandoc-load-default-settings)))

(use-package paradox
  :commands paradox-list-packages)

(use-package paredit
  :diminish
  :hook ((lisp-mode emacs-lisp-mode) . paredit-mode)
  :bind (:map paredit-mode-map
              ("[")
              ("M-k"   . paredit-raise-sexp)
              ("M-I"   . paredit-splice-sexp)
              ("C-M-l" . paredit-recentre-on-sexp)
              ("C-c ( n"   . paredit-add-to-next-list)
              ("C-c ( p"   . paredit-add-to-previous-list)
              ("C-c ( j"   . paredit-join-with-next-list)
              ("C-c ( J"   . paredit-join-with-previous-list))
  :bind (:map lisp-mode-map       ("<return>" . paredit-newline))
  :bind (:map emacs-lisp-mode-map ("<return>" . paredit-newline))
  :hook (paredit-mode
         . (lambda ()
             (unbind-key "M-r" paredit-mode-map)
             (unbind-key "M-s" paredit-mode-map)))
  :config
  (require 'eldoc)
  (eldoc-add-command 'paredit-backward-delete
                     'paredit-close-round))

(use-package paredit-ext
  :after paredit)

(use-package pass
  :commands (pass pass-view-mode)
  :mode ("\\.passwords/.*\\.gpg\\'" . pass-view-mode)
  :preface
  (defun insert-password ()
    (interactive)
    (shell-command "apg -m24 -x24 -a1 -n1" t))

  (add-hook 'pass-view-mode-hook #'pass-view--prepare-otp))

(use-package password-store
  :defer 5
  :commands (password-store-insert
             password-store-copy
             password-store-get)
  :config
  (defun password-store--run-edit (entry)
    (require 'pass)
    (find-file (concat (expand-file-name entry (password-store-dir)) ".gpg")))

  (defun password-store-insert (entry login password)
    "Insert a new ENTRY containing PASSWORD."
    (interactive (list (read-string "Password entry: ")
                       (read-string "Login: ")
                       (read-passwd "Password: " t)))
    (message "%s" (shell-command-to-string
                   (if (string= "" login)
                       (format "echo %s | %s insert -m -f %s"
                               (shell-quote-argument password)
                               password-store-executable
                               (shell-quote-argument entry))
                     (format "echo -e '%s\nlogin: %s' | %s insert -m -f %s"
                             password login password-store-executable
                             (shell-quote-argument entry)))))))

(use-package password-store-otp
  :defer t
  :config
  (defun password-store-otp-append-from-image (entry)
    "Check clipboard for an image and scan it to get an OTP URI,
append it to ENTRY."
    (interactive (list (read-string "Password entry: ")))
    (let ((qr-image-filename (password-store-otp--get-qr-image-filename entry)))
      (when (not (zerop (call-process "screencapture" nil nil nil
                                      "-T5" qr-image-filename)))
        (error "Couldn't get image from clipboard"))
      (with-temp-buffer
        (condition-case nil
            (call-process "zbarimg" nil t nil "-q" "--raw"
                          qr-image-filename)
          (error
           (error "It seems you don't have `zbar-tools' installed")))
        (password-store-otp-append
         entry
         (buffer-substring (point-min) (point-max))))
      (when (not password-store-otp-screenshots-path)
        (delete-file qr-image-filename)))))

(use-package pcre2el
  :commands (rxt-mode rxt-global-mode))

(use-package pdf-tools
  :magic ("%PDF" . pdf-view-mode)
  :config
  (dolist
      (pkg
       '(pdf-annot pdf-cache pdf-dev pdf-history pdf-info pdf-isearch
                   pdf-links pdf-misc pdf-occur pdf-outline pdf-sync
                   pdf-util pdf-view pdf-virtual))
    (require pkg))
  (pdf-tools-install))

(use-package per-window-point
  :defer 5
  :commands pwp-mode
  :config
  (pwp-mode 1))

(use-package persistent-scratch
  :unless (or (null window-system)
              alternate-emacs
              noninteractive)
  :defer 5
  :config
  (persistent-scratch-autosave-mode)
  (with-demoted-errors "Error: %S"
    (persistent-scratch-setup-default))
  :commands persistent-scratch-setup-default)

(use-package personal
  :init
  (define-key key-translation-map (kbd "A-TAB") (kbd "C-TAB"))

  :commands unfill-region
  :bind (("M-L"  . mark-line)
         ("M-S"  . mark-sentence)
         ("M-j"  . delete-indentation-forward)

         ("M-D"  . my-open-Messages)
         ("M-R"  . my-open-PathFinder)
         ("M-K"  . my-open-KeyboardMaestro)

         ("C-c )"   . close-all-parentheses)
         ("C-c 0"   . recursive-edit-preserving-window-config-pop)
         ("C-c 1"   . recursive-edit-preserving-window-config)
         ("C-c C-0" . copy-current-buffer-name)
         ("C-c C-z" . delete-to-end-of-buffer)
         ("C-c M-q" . unfill-paragraph)
         ("C-c e P" . check-papers)
         ("C-c e b" . do-eval-buffer)
         ("C-c e r" . do-eval-region)
         ("C-c e s" . scratch)
         ("C-c n"   . insert-user-timestamp)
         ("C-x C-d" . duplicate-line)
         ("C-x C-v" . find-alternate-file-with-sudo)
         ("C-x K"   . delete-current-buffer-file)
         ("C-x M-q" . refill-paragraph)
         ("C-x C-n" . next-line)
         ("C-x C-p" . previous-line))
  :preface
  (defun my-open-Messages ()
    (interactive)
    (call-process "/usr/bin/open" nil nil nil
                  "/Applications/Messages.app"))

  (defun my-open-PathFinder ()
    (interactive)
    (call-process "/usr/bin/open" nil nil nil
                  (expand-file-name
                   "~/Applications/Path Finder.app")))

  (defun my-open-KeyboardMaestro ()
    (interactive)
    (call-process "/usr/bin/open" nil nil nil
                  (expand-file-name
                   "~/Applications/Keyboard Maestro.app")))

  :init
  (bind-keys ("<C-M-backspace>" . backward-kill-sexp)

             ("M-'"   . insert-pair)
             ("M-J"   . delete-indentation)
             ("M-\""  . insert-pair)
             ("M-`"   . other-frame)
             ("M-g c" . goto-char)

             ("C-c SPC" . just-one-space)
             ("C-c M-;" . comment-and-copy)
             ("C-c e c" . cancel-debug-on-entry)
             ("C-c e d" . debug-on-entry)
             ("C-c e e" . toggle-debug-on-error)
             ("C-c e f" . emacs-lisp-byte-compile-and-load)
             ("C-c e j" . emacs-lisp-mode)
             ("C-c e z" . byte-recompile-directory)
             ("C-c f"   . flush-lines)
             ("C-c g"   . goto-line)
             ("C-c k"   . keep-lines)
             ("C-c m k" . kmacro-keymap)
             ("C-c m m" . emacs-toggle-size)
             ("C-c q"   . fill-region)
             ("C-c s"   . replace-string)
             ("C-c u"   . rename-uniquely)
             ("C-h e a" . apropos-value)
             ("C-h e e" . view-echo-area-messages)
             ("C-h e f" . find-function)
             ("C-h e k" . find-function-on-key)
             ("C-h e v" . find-variable)
             ("C-h h")
             ("C-h v"   . describe-variable)
             ("C-x C-e" . pp-eval-last-sexp)
             ("C-x d"   . delete-whitespace-rectangle)
             ("C-x t"   . toggle-truncate-lines)
             ("C-z"     . delete-other-windows))

  :init
  (defun my-adjust-created-frame ()
    (set-frame-font
     "-*-DejaVu Sans Mono-normal-normal-normal-*-16-*-*-*-m-0-iso10646-1")
    (set-frame-size (selected-frame) 75 50)
    (set-frame-position (selected-frame) 10 35))

  (advice-add 'make-frame-command :after #'my-adjust-created-frame))

(use-package phi-search
  :defer 5)

(use-package phi-search-mc
  :after (phi-search multiple-cursors)
  :config
  (phi-search-mc/setup-keys)
  (add-hook 'isearch-mode-mode #'phi-search-from-isearch-mc/setup-keys))

(use-package plantuml-mode
  :mode "\\.plantuml\\'")

(use-package po-mode
  :mode "\\.\\(po\\'\\|po\\.\\)")

(use-package popup-ruler
  :bind ("C-c R" . popup-ruler))

(use-package pp-c-l
  :hook (prog-mode . pretty-control-l-mode))

(use-package prodigy
  :commands prodigy)

(use-package projectile
  :defer 5
  :diminish
  :bind* (("C-c TAB" . projectile-find-other-file)
          ("C-c P" . (lambda () (interactive)
                       (projectile-cleanup-known-projects)
                       (projectile-discover-projects-in-search-path))))
  :bind-keymap ("C-c p" . projectile-command-map)
  :config
  (projectile-global-mode)

  (defun my-projectile-invalidate-cache (&rest _args)
    ;; We ignore the args to `magit-checkout'.
    (projectile-invalidate-cache nil))

  (eval-after-load 'magit-branch
    '(progn
       (advice-add 'magit-checkout
                   :after #'my-projectile-invalidate-cache)
       (advice-add 'magit-branch-and-checkout
                   :after #'my-projectile-invalidate-cache))))

(use-package proof-site
  :preface
  (defun my-layout-proof-windows ()
    (interactive)
    (proof-layout-windows)
    (proof-prf))

  :config
  (use-package coq
    :defer t
    :config
    (defalias 'coq-SearchPattern #'coq-SearchIsos)

    (bind-keys :map coq-mode-map
               ("M-RET"       . proof-goto-point)
               ("RET"         . newline-and-indent)
               ("C-c h")
               ("C-c C-p"     . my-layout-proof-windows)
               ("C-c C-a C-s" . coq-Search)
               ("C-c C-a C-o" . coq-SearchPattern)
               ("C-c C-a C-a" . coq-Search)
               ("C-c C-a C-r" . coq-SearchRewrite))

    (add-hook 'coq-mode-hook
              #'(lambda ()
                  (set-input-method "Agda")
                  (holes-mode -1)
                  (when (featurep 'company)
                    (company-coq-mode 1))
                  (abbrev-mode -1)

                  (bind-key "A-g" #'(lambda () (interactive) (insert "Γ")) 'coq-mode-map)
                  (bind-key "A-t" #'(lambda () (interactive) (insert "τ")) 'coq-mode-map)
                  (bind-key "A-r" #'(lambda () (interactive) (insert "ρ")) 'coq-mode-map)
                  (bind-key "A-k" #'(lambda () (interactive) (insert "κ")) 'coq-mode-map)

                  (set (make-local-variable 'fill-nobreak-predicate)
                       #'(lambda ()
                           (pcase (get-text-property (point) 'face)
                             ('font-lock-comment-face nil)
                             ((and (pred listp)
                                   x (guard (memq 'font-lock-comment-face x)))
                              nil)
                             (_ t)))))))

  (use-package pg-user
    :defer t
    :config
    (defadvice proof-retract-buffer
        (around my-proof-retract-buffer activate)
      (condition-case err ad-do-it
        (error (shell-command "killall coqtop"))))))

(use-package protobuf-mode
  :mode "\\.proto\\'")

(use-package prover
  :after coq)

(use-package ps-print
  :defer t
  :preface
  (defun ps-spool-to-pdf (beg end &rest ignore)
    (interactive "r")
    (let ((temp-file (concat (make-temp-name "ps2pdf") ".pdf")))
      (call-process-region beg end (executable-find "ps2pdf")
                           nil nil nil "-" temp-file)
      (call-process (executable-find "open") nil nil nil temp-file)))
  :config
  (setq ps-print-region-function 'ps-spool-to-pdf))

(use-package python-mode
  :mode "\\.py\\'"
  :interpreter "python"
  :bind (:map python-mode-map
              ("C-c c")
              ("C-c C-z" . python-shell))
  :config
  (defvar python-mode-initialized nil)

  (defun my-python-mode-hook ()
    (unless python-mode-initialized
      (setq python-mode-initialized t)

      (info-lookup-add-help
       :mode 'python-mode
       :regexp "[a-zA-Z_0-9.]+"
       :doc-spec
       '(("(python)Python Module Index" )
         ("(python)Index"
          (lambda
            (item)
            (cond
             ((string-match
               "\\([A-Za-z0-9_]+\\)() (in module \\([A-Za-z0-9_.]+\\))" item)
              (format "%s.%s" (match-string 2 item)
                      (match-string 1 item)))))))))

    (set (make-local-variable 'parens-require-spaces) nil)
    (setq indent-tabs-mode nil))

  (add-hook 'python-mode-hook #'my-python-mode-hook))

(use-package rainbow-delimiters
  :hook (prog-mode . rainbow-delimiters-mode))

(use-package rainbow-mode
  :commands rainbow-mode)

(use-package recentf
  :defer 10
  :commands (recentf-mode
             recentf-add-file
             recentf-apply-filename-handlers)
  :preface
  (defun recentf-add-dired-directory ()
    (if (and dired-directory
             (file-directory-p dired-directory)
             (not (string= "/" dired-directory)))
        (let ((last-idx (1- (length dired-directory))))
          (recentf-add-file
           (if (= ?/ (aref dired-directory last-idx))
               (substring dired-directory 0 last-idx)
             dired-directory)))))
  :hook (dired-mode . recentf-add-dired-directory)
  :config
  (recentf-mode 1))

(use-package rect
  :bind ("C-c ]" . rectangle-mark-mode))

(use-package redshank
  :diminish
  :hook ((lisp-mode emacs-lisp-mode) . redshank-mode))

(use-package reftex
  :after auctex
  :hook (LaTeX-mode . reftex-mode))

(use-package regex-tool
  :load-path "lisp/regex-tool"
  :commands regex-tool)

(use-package repl-toggle
  ;; jww (2017-12-10): Need to configure.
  :disabled t)

(use-package restclient
  :mode ("\\.rest\\'" . restclient-mode))

(use-package reveal-in-osx-finder
  :no-require t
  :bind ("C-c M-v" .
         (lambda () (interactive)
           (call-process "/usr/bin/open" nil nil nil
                         "-R" (expand-file-name
                               (or (buffer-file-name)
                                   default-directory))))))

(use-package riscv-mode
  :commands riscv-mode)

(use-package rtags
  ;; jww (2018-01-09): https://github.com/Andersbakken/rtags/issues/1123
  :disabled t
  :load-path "~/.nix-profile/share/emacs/site-lisp/rtags"
  :commands rtags-mode
  :bind (("C-c . D" . rtags-dependency-tree)
         ("C-c . F" . rtags-fixit)
         ("C-c . R" . rtags-rename-symbol)
         ("C-c . T" . rtags-tagslist)
         ("C-c . d" . rtags-create-doxygen-comment)
         ("C-c . c" . rtags-display-summary)
         ("C-c . e" . rtags-print-enum-value-at-point)
         ("C-c . f" . rtags-find-file)
         ("C-c . i" . rtags-include-file)
         ("C-c . i" . rtags-symbol-info)
         ("C-c . m" . rtags-imenu)
         ("C-c . n" . rtags-next-match)
         ("C-c . p" . rtags-previous-match)
         ("C-c . r" . rtags-find-references)
         ("C-c . s" . rtags-find-symbol)
         ("C-c . v" . rtags-find-virtuals-at-point))
  :bind (:map c-mode-base-map
              ("M-." . rtags-find-symbol-at-point)))

(use-package ruby-mode
  :mode "\\.rb\\'"
  :interpreter "ruby"
  :bind (:map ruby-mode-map
              ("<return>" . my-ruby-smart-return))
  :preface
  (defun my-ruby-smart-return ()
    (interactive)
    (when (memq (char-after) '(?\| ?\" ?\'))
      (forward-char))
    (call-interactively 'newline-and-indent)))

(use-package rust-mode
  :mode "\\.rs\\'"
  :init
  (add-hook 'rust-mode-hook #'my-rust-mode-init)
  :preface
  (defun my-update-cargo-path (&rest _args)
    (setq cargo-process--custom-path-to-bin
          (executable-find "cargo")))

  (defun my-cargo-target-dir (path)
    (replace-regexp-in-string "kadena" "Products" path))

  (defun my-update-cargo-args (ad-do-it name command &optional last-cmd opens-external)
    (let* ((cmd (car (split-string command)))
           (new-args
            (if (member cmd '("build" "check" "clippy" "doc" "test"))
                (let ((args
                       (format "--target-dir=%s -j8"
                               (my-cargo-target-dir
                                (replace-regexp-in-string
                                 "target" "target--custom"
                                 (regexp-quote (getenv "CARGO_TARGET_DIR")))))))
                  (if (member cmd '("build"))
                      (concat "--message-format=short " args)
                    args))
              ""))
           (cargo-process--command-flags
            (pcase (split-string cargo-process--command-flags " -- ")
              (`(,before ,after)
               (concat before " " new-args " -- " after))
              (_ (concat cargo-process--command-flags new-args)))))
      (funcall ad-do-it name command last-cmd opens-external)))

  (defun my-rust-mode-init ()
    (advice-add 'direnv-update-directory-environment
                :after #'my-update-cargo-path)
    (advice-add 'cargo-process--start :around #'my-update-cargo-args)
    (direnv-update-environment default-directory)

    (cargo-minor-mode 1)
    (yas-minor-mode-on)

    (if dot-emacs-use-eglot
        (progn
          (require 'eglot)
          (when (functionp 'eglot)
            (bind-key "M-n" #'flymake-goto-next-error rust-mode-map)
            (bind-key "M-p" #'flymake-goto-prev-error rust-mode-map)

            (bind-key "C-c C-c v" #'(lambda ()
                                      (interactive)
                                      (shell-command "rustdocs std"))
                      rust-mode-map)

            (defun my-rust-project-find-function (dir)
              (let ((root (locate-dominating-file dir "Cargo.toml")))
                (and root (cons 'transient root))))

            (with-eval-after-load 'project
              (add-to-list 'project-find-functions 'my-rust-project-find-function))

            (let* ((current-server (eglot-current-server))
                   (live-p (and current-server (jsonrpc-running-p current-server))))
              (unless live-p
                (call-interactively #'eglot)))

            (company-mode 1)))
      (when (functionp 'lsp)
        (lsp)))))

(use-package rustic
  :disabled t
  :unless dot-emacs-use-eglot
  :mode ("\\.rs\\'" . rustic-mode)
  :preface
  (defun my-update-cargo-args (ad-do-it command &optional args)
    (let* ((cmd (car (split-string command)))
           (new-args
            (if (member cmd '("build" "check" "clippy" "doc" "test"))
                (let ((args
                       (format "--target-dir=%s -j8"
                               (my-cargo-target-dir
                                (replace-regexp-in-string
                                 "target" "target--custom"
                                 (regexp-quote (getenv "CARGO_TARGET_DIR")))))))
                  (if (member cmd '("build"))
                      (concat "--message-format=short " args)
                    args))
              ""))
           (args
            (pcase (and args (split-string args " -- "))
              (`(,before ,after)
               (concat before " " new-args " -- " after))
              (_ (concat args new-args)))))
      (funcall ad-do-it command args)))

  (defun my-rustic-mode-hook ()
    (advice-add 'rustic-run-cargo-command :around #'my-update-cargo-args)
    (direnv-update-environment default-directory)

    (setq lsp-rust-analyzer-server-command
          (list (substring (shell-command-to-string "which rust-analyzer") 0 -1)))
    (setq rustic-analyzer-command lsp-rust-analyzer-server-command)

    (flycheck-mode 1)
    (yas-minor-mode-on)

    ;; so that run C-c C-c C-r works without having to confirm, but don't try to
    ;; save rust buffers that are not file visiting. Once
    ;; https://github.com/brotzeit/rustic/issues/253 has been resolved this should
    ;; no longer be necessary.
    (when buffer-file-name
      (setq-local buffer-save-without-query t)))
  :bind (:map rustic-mode-map
              ("M-j"         . lsp-ui-imenu)
              ("M-?"         . lsp-find-references)
              ("C-c d"       . lsp-ui-doc-show)
              ("C-c h"       . lsp-ui-doc-hide)
              ("C-c C-c l"   . flycheck-list-errors)
              ("C-c C-c a"   . lsp-execute-code-action)
              ("C-c C-c r"   . lsp-rename)
              ("C-c C-c q"   . lsp-workspace-restart)
              ("C-c C-c Q"   . lsp-workspace-shutdown)
              ("C-c C-c s"   . lsp-rust-analyzer-status)
              ("C-c C-c C-y" . rustic-cargo-clippy))
  :config
  (setq rustic-format-on-save t)
  (add-hook 'rustic-mode-hook 'my-rustic-mode-hook))

(use-package rustic-flycheck
  :after rustic
  :config
  (defun my-rust-project-find-function (dir)
    (let ((root (locate-dominating-file dir "Cargo.toml")))
      (and root (cons 'transient root))))

  (with-eval-after-load 'project
    (add-to-list 'project-find-functions 'my-rust-project-find-function))

  (defun project-root (project)
    (car (project-roots project)))

  (defun first-dominating-file (file name)
    (aif (locate-dominating-file file name)
        (or (first-dominating-file
             (file-name-directory (directory-file-name it)) name) it)))

  (defun flycheck-rust-manifest-directory ()
    (and buffer-file-name
         (first-dominating-file buffer-file-name "Cargo.toml")))

  (require 'flycheck)
  (push 'rustic-clippy flycheck-checkers)

  (setq rustic-clippy-arguments
        (concat "--all-targets "
                "--all-features "
                "-- "
                "-D warnings "
                "-D clippy::all "
                "-D clippy::mem_forget "
                "-C debug-assertions=off"))

  (defun rustic-cargo-clippy (&optional arg)
    (interactive "P")
    (rustic-cargo-clippy-run
     (cond (arg
            (setq rustic-clippy-arguments (read-from-minibuffer "Cargo clippy arguments: " rustic-clippy-arguments)))
           ((eq major-mode 'rustic-popup-mode)
            rustic-clippy-arguments)
           (t rustic-clippy-arguments))))

  (setq rustic-flycheck-clippy-params
        (concat "--message-format=json " rustic-clippy-arguments)))

(use-package savehist
  :unless noninteractive
  :config
  (savehist-mode 1))

(use-package saveplace
  :unless noninteractive
  :config
  (save-place-mode 1))

(use-package sbt-mode
  :mode "\\.sbt\\'")

(use-package scala-mode
  :mode "\\.scala\\'")

(use-package sdcv-mode
  :bind ("C-c W" . my-sdcv-search)
  :config
  (defvar sdcv-index nil)

  (defun my-sdcv-search ()
    (interactive)
    (flet ((read-string
            (prompt &optional initial-input history
                    default-value inherit-input-method)
            (ivy-read
             prompt
             (or sdcv-index
                 (with-temp-buffer
                   (insert-file-contents
                    "~/.local/share/dictionary/websters.index")
                   (goto-char (point-max))
                   (insert ")")
                   (goto-char (point-min))
                   (insert "(")
                   (goto-char (point-min))
                   (setq sdcv-index (read (current-buffer)))))
             :history history
             :initial-input initial-input
             :def default-value)))
      (call-interactively #'sdcv-search))))

(use-package selected
  :demand t
  :diminish selected-minor-mode
  :bind (:map selected-keymap
              ("[" . align-code)
              ("f" . fill-region)
              ("U" . unfill-region)
              ("d" . downcase-region)
              ("r" . reverse-region)
              ("S" . sort-lines))
  :config
  (selected-global-mode 1))

(use-package separedit
  :commands separedit)

(use-package server
  :unless (or noninteractive
              alternate-emacs)
  :no-require
  :config
  (unless (file-exists-p "/tmp/johnw-emacs")
    (make-directory "/tmp/johnw-emacs")
    (chmod "/tmp/johnw-emacs" 448))
  (setq server-socket-dir "/tmp/johnw-emacs")
  :hook (after-init . server-start))

(use-package sh-script
  :defer t
  :init
  (defvar sh-script-initialized nil)
  (defun initialize-sh-script ()
    (unless sh-script-initialized
      (setq sh-script-initialized t)
      (info-lookup-add-help :mode 'shell-script-mode
                            :regexp ".*"
                            :doc-spec '(("(bash)Index")))))
  (add-hook 'shell-mode-hook #'initialize-sh-script))

(use-package shackle
  :unless alternate-emacs
  :defer 5
  :commands shackle-mode
  :config
  (shackle-mode 1))

(use-package shell-toggle
  :bind ("C-, C-z" . shell-toggle))

(use-package shift-number
  :bind (("C-c +" . shift-number-up)
         ("C-c -" . shift-number-down)))

(use-package sky-color-clock
  :defer 5
  :commands sky-color-clock
  :config
  (require 'solar)
  (sky-color-clock-initialize calendar-latitude)
  ;; (sky-color-clock-initialize-openweathermap-client
  ;;  (with-temp-buffer
  ;;    (insert-file-contents-literally "~/.config/weather/apikey")
  ;;    (buffer-substring (point-min) (1- (point-max))))
  ;;  5408211 ;; West Sacramento, CA, USA
  ;;  )
  (setq display-time-string-forms '((sky-color-clock))))

(use-package slime
  :commands slime
  :init
  ;; (unless (memq major-mode
  ;;               '(emacs-lisp-mode inferior-emacs-lisp-mode ielm-mode))
  ;;   ("M-q" . slime-reindent-defun)
  ;;   ("M-l" . slime-selector))

  (setq inferior-lisp-program "sbcl"
        slime-contribs '(slime-fancy)))

(use-package smart-mode-line
  :config
  ;; See https://github.com/Malabarba/smart-mode-line/issues/217
  (setq mode-line-format (delq 'mode-line-position mode-line-format))
  (sml/setup)
  (sml/apply-theme 'light)
  (remove-hook 'display-time-hook 'sml/propertize-time-string))

(use-package smart-newline
  :diminish
  :commands smart-newline-mode)

(use-package smartparens-config
  :commands smartparens-mode)

(use-package smartscan
  :defer 5
  :bind (:map smartscan-map
              ("C->" . smartscan-symbol-go-forward)
              ("C-<" . smartscan-symbol-go-backward)))

(use-package smerge-mode
  :commands smerge-mode)

(use-package smex
  :defer 5
  :commands smex)

(use-package sort-words
  :commands sort-words)

(use-package sql-indent
  :commands sqlind-minor-mode)

(use-package stock-quote
  :disabled t
  :demand t
  :commands stock-quote
  :config
  (when (file-readable-p "/tmp/icp.txt")
    (defun stock-quote-from-file (&rest ticker)
      (with-temp-buffer
        (insert-file-contents-literally "/tmp/icp.txt")
        (string-to-number (buffer-substring (point-min) (1- (point-max))))))
    (setq stock-quote-data-functions '(stock-quote-from-file))
    (stock-quote-in-modeline "ICP"))
  ;; :init
  ;; (load "~/src/thinkorswim/thinkorswim-el/thinkorswim")
  ;; :config
  ;; (setq tos-client-id
  ;;       (lookup-password "developer.tdameritrade.com.client-id"
  ;;                        tos-user-id 80))
  )

(use-package string-edit
  :bind ("C-c C-'" . string-edit-at-point))

(use-package string-inflection
  :bind ("C-c `" . string-inflection-toggle))

(use-package super-save
  :diminish
  :commands super-save-mode
  :config
  (setq super-save-auto-save-when-idle t))

(use-package swift-mode
  :commands swift-mode)

(use-package swiper
  :after ivy
  :bind ("C-M-s" . swiper)
  :bind (:map swiper-map
              ("M-y" . yank)
              ("M-%" . swiper-query-replace)
              ("C-." . swiper-avy)
              ("M-c" . swiper-mc))
  :bind (:map isearch-mode-map
              ("C-o" . swiper-from-isearch)))

(use-package tagedit
  :commands tagedit-mode)

(use-package term
  :bind (:map term-mode-map
              ("C-c C-y" . term-paste)))

(use-package terraform-mode
  :mode "\.tf\\'")

(use-package texinfo
  :mode ("\\.texi\\'" . texinfo-mode)
  :config
  (defun my-texinfo-mode-hook ()
    (dolist (mapping '((?b . "emph")
                       (?c . "code")
                       (?s . "samp")
                       (?d . "dfn")
                       (?o . "option")
                       (?x . "pxref")))
      (local-set-key (vector (list 'alt (car mapping)))
                     `(lambda () (interactive)
                        (TeX-insert-macro ,(cdr mapping))))))

  (add-hook 'texinfo-mode-hook #'my-texinfo-mode-hook)

  (defun texinfo-outline-level ()
    ;; Calculate level of current texinfo outline heading.
    (require 'texinfo)
    (save-excursion
      (if (bobp)
          0
        (forward-char 1)
        (let* ((word (buffer-substring-no-properties
                      (point) (progn (forward-word 1) (point))))
               (entry (assoc word texinfo-section-list)))
          (if entry
              (nth 1 entry)
            5))))))

(use-package tidy
  :commands (tidy-buffer
             tidy-parse-config-file
             tidy-save-settings
             tidy-describe-options))

(use-package tla-mode
  :mode "\\.tla\\'"
  :config
  (add-hook 'tla-mode-hook
            #'(lambda ()
                (setq-local comment-start nil)
                (setq-local comment-end ""))))

(use-package tracking
  :defer t
  :config
  (define-key tracking-mode-map [(control ?c) space] #'tracking-next-buffer))

(use-package tramp
  :defer 5
  :config
  ;; jww (2018-02-20): Without this change, tramp ends up sending hundreds of
  ;; shell commands to the remote side to ask what the temporary directory is.
  (put 'temporary-file-directory 'standard-value '("/tmp"))
  (setq tramp-auto-save-directory "~/.cache/emacs/backups"
        tramp-persistency-file-name "~/.emacs.d/data/tramp"))

(use-package tramp-sh
  :defer t
  :config
  (add-to-list 'tramp-remote-path "/run/current-system/sw/bin"))

(use-package transpose-mark
  :commands (transpose-mark
             transpose-mark-line
             transpose-mark-region))

(use-package treemacs
  :commands treemacs)

(use-package tuareg
  :mode (("\\.ml[4ip]?\\'" . tuareg-mode)
         ("\\.eliomi?\\'"  . tuareg-mode)))

(use-package typo
  :commands typo-mode)

(use-package undo-propose
  :commands undo-propose)

(use-package unicode-fonts
  :config
  (unicode-fonts-setup)
  ;; (setq face-font-rescale-alist '((".*Scheher.*" . 1.8)))
  )

(use-package vagrant
  :commands (vagrant-up
             vagrant-ssh
             vagrant-halt
             vagrant-status)
  :config
  (vagrant-tramp-enable))

(use-package vagrant-tramp
  :after tramp
  :defer 5)

(use-package vdiff
  :commands (vdiff-files
             vdiff-files3
             vdiff-buffers
             vdiff-buffers3))

(use-package vimish-fold
  :bind (("C-c V f" . vimish-fold)
         ("C-c V d" . vimish-fold-delete)
         ("C-c V D" . vimish-fold-delete-all)))

(use-package visual-fill-column
  :commands visual-fill-column-mode)

(use-package visual-regexp
  :bind (("C-c r"   . vr/replace)
         ("C-c %"   . vr/query-replace)
         ("<C-m> /" . vr/mc-mark)))

(use-package vline
  :commands vline-mode)

(use-package w3m
  :commands (w3m-browse-url w3m-find-file))

(use-package wat-mode
  :mode "\\.was?t\\'")

(use-package web-mode
  :commands web-mode)

(use-package wgrep
  :defer 5)

(use-package which-func
  :hook (c-mode-common . which-function-mode))

(use-package which-key
  :defer 5
  :diminish
  :commands which-key-mode
  :config
  (which-key-mode))

(use-package whitespace
  :diminish (global-whitespace-mode
             whitespace-mode
             whitespace-newline-mode)
  :commands (whitespace-buffer
             whitespace-cleanup
             whitespace-mode
             whitespace-turn-off)
  :preface
  (defvar normalize-hook nil)

  (defun normalize-file ()
    (interactive)
    (save-excursion
      (goto-char (point-min))
      (whitespace-cleanup)
      (run-hook-with-args normalize-hook)
      (delete-trailing-whitespace)
      (goto-char (point-max))
      (delete-blank-lines)
      (set-buffer-file-coding-system 'unix)
      (goto-char (point-min))
      (while (re-search-forward "\r$" nil t)
        (replace-match ""))
      (set-buffer-file-coding-system 'utf-8)
      (let ((require-final-newline t))
        (save-buffer))))

  (defun maybe-turn-on-whitespace ()
    "depending on the file, maybe clean up whitespace."
    (when (and (not (or (memq major-mode '(markdown-mode))
                        (and buffer-file-name
                             (string-match "\\(\\.texi\\|COMMIT_EDITMSG\\)\\'"
                                           buffer-file-name))))
               (locate-dominating-file default-directory ".clean")
               (not (locate-dominating-file default-directory ".noclean")))
      (whitespace-mode 1)
      ;; For some reason, having these in settings.el gets ignored if
      ;; whitespace loads lazily.
      (setq whitespace-auto-cleanup t
            whitespace-line-column 80
            whitespace-rescan-timer-time nil
            whitespace-silent t
            whitespace-style '(face trailing lines space-before-tab empty))
      (add-hook 'write-contents-hooks
                #'(lambda () (ignore (whitespace-cleanup))) nil t)
      (whitespace-cleanup)))

  :init
  (add-hook 'find-file-hooks #'maybe-turn-on-whitespace t)

  :config
  (remove-hook 'find-file-hooks 'whitespace-buffer)
  (remove-hook 'kill-buffer-hook 'whitespace-buffer))

(use-package whitespace-cleanup-mode
  :defer 5
  :diminish
  :commands whitespace-cleanup-mode
  :config
  (global-whitespace-cleanup-mode 1))

(use-package window-purpose
  :commands purpose-mode)

(use-package winner
  :unless noninteractive
  :defer 5
  :bind (("M-N" . winner-redo)
         ("M-P" . winner-undo))
  :config
  (winner-mode 1))

(use-package word-count
  :bind ("C-c \"" . word-count-mode))

(use-package x86-lookup
  :bind ("C-h X" . x86-lookup))

(use-package xray
  :bind (("C-h x b" . xray-buffer)
         ("C-h x f" . xray-faces)
         ("C-h x F" . xray-features)
         ("C-h x R" . xray-frame)
         ("C-h x h" . xray-hooks)
         ("C-h x m" . xray-marker)
         ("C-h x o" . xray-overlay)
         ("C-h x p" . xray-position)
         ("C-h x S" . xray-screen)
         ("C-h x s" . xray-symbol)
         ("C-h x w" . xray-window)))

(use-package yaml-mode
  :mode "\\.ya?ml\\'")

(use-package yaoddmuse
  :bind (("C-c w f" . yaoddmuse-browse-page-default)
         ("C-c w e" . yaoddmuse-edit-default)
         ("C-c w p" . yaoddmuse-post-library-default)))

(use-package yasnippet
  :demand t
  :diminish yas-minor-mode
  :bind (("C-c y d" . yas-load-directory)
         ("C-c y i" . yas-insert-snippet)
         ("C-c y f" . yas-visit-snippet-file)
         ("C-c y n" . yas-new-snippet)
         ("C-c y t" . yas-tryout-snippet)
         ("C-c y l" . yas-describe-tables)
         ("C-c y g" . yas/global-mode)
         ("C-c y m" . yas/minor-mode)
         ("C-c y r" . yas-reload-all)
         ("C-c y x" . yas-expand))
  :bind (:map yas-keymap
              ("C-i" . yas-next-field-or-maybe-expand))
  :mode ("/\\.emacs\\.d/snippets/" . snippet-mode)
  :config
  (yas-load-directory (emacs-path "snippets"))
  (yas-global-mode 1))

(use-package z3-mode
  :mode (("\\.smt\\'" . z3-mode))
  :bind (:map z3-mode-map
              ("C-c C-c" . z3-execute-region)))

(use-package zoom
  :bind ("C-x +" . zoom)
  :preface
  (defun size-callback ()
    (cond ((> (frame-pixel-width) 1280) '(90 . 0.75))
          (t '(0.5 . 0.5)))))

(use-package ztree-diff
  :commands ztree-diff)

;;; Layout

(defconst display-name
  (pcase (display-pixel-width)
    (`3840 'dell-wide)
    (`4480 'imac)
    (`2560 'imac)
    (`1920 'macbook-pro-vga)
    (`1792 'macbook-pro-16)
    (`1680 'macbook-pro-15)
    ;; (`1680 'macbook-pro-13)
    ))

(defsubst bookerly-font (height)
  (format "-*-Bookerly-normal-normal-normal-*-%d-*-*-*-p-0-iso10646-1" height))

(defsubst dejavu-sans-mono-font (height)
  (format "-*-DejaVu Sans Mono-normal-normal-normal-*-%d-*-*-*-m-0-iso10646-1" height))

(defun emacs-min-font ()
  (pcase display-name
    ((guard alternate-emacs) (bookerly-font 18))
    (`imac (dejavu-sans-mono-font 18))
    (_     (dejavu-sans-mono-font 18))))

(defun emacs-min-font-height ()
  (aref (font-info (emacs-min-font)) 3))

(defun emacs-min-left ()
  (pcase display-name
    ((guard alternate-emacs)    0)
    (`dell-wide              1000)
    (`imac              (pcase (emacs-min-font-height)
                          (28  20)
                          (24 116)
                          (21 318)
                          (t    0)))
    (`macbook-pro-vga         700)
    (`macbook-pro-16          672)
    (`macbook-pro-15          464)
    (`macbook-pro-13          464)))

(defun emacs-min-height ()
  (pcase display-name
    ((guard alternate-emacs)   58)
    (`dell-wide                64)
    (`imac               (pcase (emacs-min-font-height)
                           (28 50)
                           (24 58)
                           (21 67)
                           (t  40)))
    (`macbook-pro-vga          55)
    (`macbook-pro-16           51)
    (`macbook-pro-15           47)
    (`macbook-pro-13           47)))

(defun emacs-min-width ()
  (pcase display-name
    ((guard alternate-emacs)   80)
    (`dell-wide               202)
    (`imac              (pcase (emacs-min-font-height)
                          (28 180)
                          (24 202)
                          (21 202)
                          (t  100)))
    (`macbook-pro-vga         100)
    (`macbook-pro-16          100)
    (`macbook-pro-15          100)
    (`macbook-pro-13          100)))

(defun emacs-min ()
  (interactive)
  (cl-flet ((set-param (p v) (set-frame-parameter (selected-frame) p v)))
    (set-param 'fullscreen nil)
    (set-param 'vertical-scroll-bars nil)
    (set-param 'horizontal-scroll-bars nil))
  (message "display-name:     %S" display-name)
  (message "Font name:        %s" (emacs-min-font))
  (message "Font height:      %s" (aref (font-info (emacs-min-font)) 3))
  (message "emacs-min-left:   %s" (emacs-min-left))
  (message "emacs-min-height: %s" (emacs-min-height))
  (message "emacs-min-width:  %s" (emacs-min-width))
  (and (emacs-min-left)
       (set-frame-position (selected-frame) (emacs-min-left) 0))
  (and (emacs-min-height)
       (set-frame-height (selected-frame) (emacs-min-height)))
  (and (emacs-min-width)
       (set-frame-width (selected-frame) (emacs-min-width)))
  (and (emacs-min-font)
       (set-frame-font (emacs-min-font)))
  (message "Emacs is ready"))

(defun emacs-max ()
  (interactive)
  (cl-flet ((set-param (p v) (set-frame-parameter (selected-frame) p v)))
    (set-param 'fullscreen 'fullboth)
    (set-param 'vertical-scroll-bars nil)
    (set-param 'horizontal-scroll-bars nil))
  (and (emacs-min-font)
       (set-frame-font (emacs-min-font))))

(defun emacs-toggle-size ()
  (interactive)
  (if (alist-get 'fullscreen (frame-parameters))
      (emacs-min)
    (emacs-max)))

(add-hook 'emacs-startup-hook #'emacs-min t)

(use-package color-theme
  :config
  (load "color-theme-library")
  (color-theme-midnight))

;;; Finalization

(let ((elapsed (float-time (time-subtract (current-time)
                                          emacs-start-time))))
  (message "Loading %s...done (%.3fs)" load-file-name elapsed))

(add-hook 'after-init-hook
          `(lambda ()
             (let ((elapsed
                    (float-time
                     (time-subtract (current-time) emacs-start-time))))
               (message "Loading %s...done (%.3fs) [after-init]"
                        ,load-file-name elapsed))) t)

(defun add-journal-entry (title)
  (interactive "sTitle: ")
  (let* ((moniker
          (replace-regexp-in-string
           "[,!]" ""
           (replace-regexp-in-string " " "-" (downcase title))))
         (most-recent
          (split-string
           (car (last (directory-files "~/doc/johnwiegley/posts"))) "-"))
         (year (nth 0 most-recent))
         (month (nth 1 most-recent))
         (day (nth 2 most-recent))
         (date (calendar-gregorian-from-absolute
                (+ 7 (calendar-absolute-from-gregorian
                      (list (string-to-number month)
                            (string-to-number day)
                            (string-to-number year))))))
         (path (expand-file-name (format "%02d-%02d-%02d-%s.md"
                                         (nth 2 date)
                                         (nth 0 date)
                                         (nth 1 date)
                                         moniker)
                                 "~/doc/johnwiegley/posts")))
    (switch-to-buffer (find-file path))
    (insert (format "---
title: %s
tags: journal
---

%s" title (current-kill 0)))))

(bind-key "C-c J" #'add-journal-entry)

(defun startup ()
  (interactive)
  (eshell-toggle nil)
  (switch-to-gnus)
  (switch-to-fetchmail)
  (jump-to-org-agenda)
  (org-resolve-clocks)
  (unless (eq display-name 'imac)
    (display-battery-mode 1))
  ;; (stock-quote "/ES")
  )

;;; init.el ends here
