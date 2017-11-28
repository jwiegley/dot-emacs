(defconst emacs-start-time (current-time))

(setq message-log-max 16384)

;;; Functions

(defsubst emacs-path (path)
  (expand-file-name path user-emacs-directory))

(defsubst add-load-path (path)
  (add-to-list 'load-path (emacs-path path)))

(defsubst hook-into-modes (func &rest modes)
  (dolist (mode-hook modes) (add-hook mode-hook func)))

(defsubst lookup-password (host user port)
  (require 'auth-source)
  (funcall (plist-get (car (auth-source-search :host host :user user
                                               :type 'netrc :port port))
                      :secret)))

(defun get-jobhours-string ()
  (with-current-buffer (get-buffer-create "*scratch*")
    (let ((str (shell-command-to-string "jobhours")))
      (require 'ansi-color)
      (ansi-color-apply (substring str 0 (1- (length str)))))))

(defun plist-delete (plist property)
  "Delete PROPERTY from PLIST"
  (let (p)
    (while plist
      (if (not (eq property (car plist)))
          (setq p (plist-put p (car plist) (nth 1 plist))))
      (setq plist (cddr plist)))
    p))

;;; Environment

(eval-and-compile
  (require 'cl)

  (defconst emacs-environment (getenv "NIX_MYENV_NAME"))

  (mapc #'add-load-path
        (append (directory-files (emacs-path "site-lisp") t
                                 "site-[A-Z0-9a-z-]+\\'")
                '("site-lisp" "lisp/use-package" "lisp" "")))

  (defun nix-read-environment (name)
    (with-temp-buffer
      (insert-file-contents-literally
       (with-temp-buffer
         (insert-file-contents-literally
          (executable-find (concat "load-env-" name)))
         (and (re-search-forward "^source \\(.+\\)$" nil t)
              (match-string 1))))
      (and (or (re-search-forward "^  nativeBuildInputs=\"\\(.+?\\)\"" nil t)
               (re-search-forward "^  buildInputs=\"\\(.+?\\)\"" nil t))
           (split-string (match-string 1)))))

  (when (executable-find "nix-env")
    (mapc #'(lambda (path)
              (let ((share (expand-file-name "share/emacs/site-lisp" path)))
                (if (file-directory-p share)
                    (add-to-list 'load-path share))))
          (nix-read-environment emacs-environment)))

  (require 'use-package)
  (setq use-package-verbose t))

(require 'bind-key)
(require 'seq)

;;; Settings

(defvar running-alternate-emacs nil)
(defvar running-development-emacs nil)

(defvar user-data-directory (emacs-path "data"))

(if (string= "emacs26" emacs-environment)
    (load (emacs-path "settings"))
  (let ((settings
         (with-temp-buffer
           (insert-file-contents (emacs-path "settings.el"))
           (read (current-buffer))))
        (suffix (cond ((string= "emacsHEAD" emacs-environment) "alt")
                      (t "other"))))
    (setq running-development-emacs (string= suffix "dev")
          running-alternate-emacs   (string= suffix "alt")
          user-data-directory
          (replace-regexp-in-string "/data" (format "/data-%s" suffix)
                                    user-data-directory))
    (dolist (setting settings)
      (let ((value (and (listp setting)
                        (nth 1 (nth 1 setting)))))
        (if (and (stringp value)
                 (string-match "/\\.emacs\\.d/data" value))
            (setcar (nthcdr 1 (nth 1 setting))
                    (replace-regexp-in-string
                     "/\\.emacs\\.d/data"
                     (format "/.emacs.d/data-%s" suffix)
                     value)))))
    (eval settings)))

(setq Info-directory-list
      (mapcar 'expand-file-name
              (list
               "~/.emacs.d/info"
               "~/Library/Info"
               (if (executable-find "nix-env")
                   (expand-file-name
                    "share/info"
                    (car (nix-read-environment emacs-environment)))
                 "~/share/info")
               "~/.nix-profile/share/info")))

(setq disabled-command-function nil)

(setplist 'flet (plist-delete (symbol-plist 'flet) 'byte-obsolete-info))

;;; Libraries

(use-package alert            :defer t :load-path "lisp/alert")
(use-package anaphora        :demand t :load-path "lib/anaphora")
(use-package apiwrap         :demand t :load-path "lib/apiwrap")
(use-package async            :defer t :load-path "lisp/emacs-async")
(use-package button-lock      :defer t :load-path "lib/button-lock")
(use-package crux            :demand t :load-path "lib/crux")
(use-package ctable           :defer t :load-path "lib/emacs-ctable")
(use-package dash            :demand t :load-path "lib/dash-el")
(use-package deferred         :defer t :load-path "lib/emacs-deferred")
(use-package diminish        :demand t :load-path "lib/diminish")
(use-package elisp-refs       :defer t :load-path "lib/elisp-refs")
(use-package emojify          :defer t :load-path "lib/emacs-emojify")
(use-package epc              :defer t :load-path "lib/emacs-epc")
(use-package epl              :defer t :load-path "lib/epl")
(use-package f                :defer t :load-path "lib/f-el")
(use-package fringe-helper-el :defer t :load-path "lib/fringe-helper-el")
(use-package fuzzy            :defer t :load-path "lib/fuzzy-el")
(use-package gh               :defer t :load-path "lib/gh-el")
(use-package ghub             :defer t :load-path "lib/ghub")
(use-package ghub+            :defer t :load-path "lib/ghub-plus")
(use-package ht               :defer t :load-path "lib/ht-el")
(use-package kv               :defer t :load-path "lib/kv")
(use-package let-alist        :defer t :load-path "lib/let-alist")
(use-package list-utils       :defer t :load-path "lib/list-utils")
(use-package logito           :defer t :load-path "lib/logito")
(use-package loop             :defer t :load-path "lib/loop")
(use-package m-buffer         :defer t :load-path "lib/m-buffer")
(use-package makey            :defer t :load-path "lib/makey")
(use-package marshal          :defer t :load-path "lib/marshal-el")
(use-package oauth2           :defer t :load-path "lib/oauth2")
(use-package parent-mode      :defer t :load-path "lib/parent-mode")
(use-package pcache           :defer t :load-path "lib/pcache")
(use-package pfuture          :defer t :load-path "lib/pfuture")
(use-package pkg-info         :defer t :load-path "lib/pkg-info")
(use-package popup            :defer t :load-path "lib/popup-el")
(use-package popwin           :defer t :load-path "site-lisp/popwin")
(use-package pos-tip          :defer t)
(use-package popup-pos-tip    :defer t)
(use-package request          :defer t :load-path "lib/emacs-request")
(use-package rich-minority    :defer t :load-path "lib/rich-minority")
(use-package s                :defer t :load-path "lib/s-el")
(use-package tablist          :defer t :load-path "lib/tablist")
(use-package uuidgen          :defer t :load-path "lib/uuidgen-el")
(use-package web              :defer t :load-path "lib/emacs-web")
(use-package web-server       :defer t :load-path "lib/emacs-web-server")
(use-package websocket        :defer t :load-path "lib/emacs-websocket")
(use-package with-editor      :defer t :load-path "lib/with-editor")
(use-package xml-rpc          :defer t)

;;; Keymaps

(mapc #'(lambda (entry)
          (define-prefix-command (cdr entry))
          (bind-key (car entry) (cdr entry)))
      '(("C-."   . my-ctrl-dot-map)
        ("C-. =" . my-ctrl-dot-equals-map)
        ("C-. f" . my-ctrl-dot-f-map)
        ("C-. g" . my-ctrl-dot-g-map)
        ("C-. h" . my-ctrl-dot-h-map)
        ("C-. v" . my-ctrl-dot-v-map)
        ("C-h e" . my-ctrl-h-e-map)
        ("C-c e" . my-ctrl-c-e-map)
        ("C-c m" . my-ctrl-c-m-map)
        ("C-c y" . my-ctrl-c-y-map)))

;;; Packages

(use-package abbrev
  :commands abbrev-mode
  :diminish abbrev-mode
  :init
  (hook-into-modes #'abbrev-mode
                   'text-mode-hook
                   'prog-mode-hook
                   'erc-mode-hook
                   'LaTeX-mode-hook)
  :config
  (if (file-exists-p abbrev-file-name)
      (quietly-read-abbrev-file))

  (add-hook 'expand-load-hook
            (lambda ()
              (add-hook 'expand-expand-hook 'indent-according-to-mode)
              (add-hook 'expand-jump-hook 'indent-according-to-mode))))

(use-package ace-link
  :load-path "site-lisp/ace-link"
  :after avy
  :config
  (ace-link-setup-default))

(use-package ace-window
  :load-path "site-lisp/ace-window"
  :bind* ("<C-return>" . ace-window))

(use-package agda-input
  :load-path
  (lambda ()
    (mapcar
     #'(lambda (dir)
         ;; The Emacs files for Agda are installed by Nix as part of the
         ;; haskellPackages.Agda package.
         (file-name-directory
          (substring (shell-command-to-string
                      (concat dir "/bin/agda-mode locate")) 0 -1)))
     (seq-filter
      (apply-partially #'string-match "-Agda-")
      (nix-read-environment (concat "ghc" (getenv "GHCVER"))))))
  :config
  (set-input-method "Agda"))

(use-package agda2-mode
  ;; This declaration depends on the load-path established by agda-input.
  :mode "\\.agda\\'"
  :defines agda2-mode-map
  :preface
  (defun agda2-insert-helper-function (&optional prefix)
    (interactive "P")
    (let ((func-def (with-current-buffer "*Agda information*"
                      (buffer-string))))
      (save-excursion
        (forward-paragraph)
        (let ((name (car (split-string func-def " "))))
          (insert "  where\n    " func-def "    " name " x = ?\n")))))

  :config
  (bind-key "C-c C-i" #'agda2-insert-helper-function agda2-mode-map)

  (defun char-mapping (key char)
    (bind-key key `(lambda () (interactive) (insert ,char))))

  (char-mapping "A-G" "Γ")
  (char-mapping "A-l" "λ x → ")
  (char-mapping "A-:" " ∷ ")
  (char-mapping "A-r" " → ")
  (char-mapping "A-~" " ≅ ")
  (char-mapping "A-=" " ≡ "))

(use-package aggressive-indent
  :load-path "site-lisp/aggressive-indent-mode"
  :diminish aggressive-indent-mode
  :commands aggressive-indent-mode
  :init
  (add-hook 'emacs-lisp-mode-hook #'aggressive-indent-mode))

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

(use-package ascii
  :bind ("C-c e A" . ascii-toggle)
  :commands ascii-on
  :functions ascii-off
  :preface
  (defun ascii-toggle ()
    (interactive)
    (if ascii-display
        (ascii-off)
      (ascii-on))))

(use-package auctex
  :load-path "site-lisp/auctex"
  :defines (latex-help-cmd-alist latex-help-file)
  :mode ("\\.tex\\'" . TeX-latex-mode)

  :init
  (setq reftex-plug-into-AUCTeX t)
  (setenv "PATH" (concat "/Library/TeX/texbin:" (getenv "PATH")))
  (add-to-list 'exec-path "/Library/TeX/texbin")

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
            #'TeX-revert-document-buffer)

  (use-package latex
    :defer t
    :config
    (require 'preview)
    (load (emacs-path "site-lisp/auctex/style/minted"))
    (add-hook 'LaTeX-mode-hook 'reftex-mode)
    (info-lookup-add-help :mode 'LaTeX-mode
                          :regexp ".*"
                          :parse-rule "\\\\?[a-zA-Z]+\\|\\\\[^a-zA-Z]"
                          :doc-spec '(("(latex2e)Concept Index" )
                                      ("(latex2e)Command Index")))))

(use-package auto-yasnippet
  :load-path "site-lisp/auto-yasnippet"
  :after yasnippet
  :bind (("C-c y a" . aya-create)
         ("C-c y e" . aya-expand)
         ("C-c y o" . aya-open-line)))

(use-package autorevert
  :commands auto-revert-mode
  :diminish auto-revert-mode
  :init
  (add-hook 'find-file-hook #'(lambda () (auto-revert-mode 1))))

(use-package avy
  :load-path "site-lisp/avy"
  :demand t
  :bind ("M-h" . avy-goto-char)
  :config
  (avy-setup-default))

(use-package backup-each-save
  :commands backup-each-save
  :preface
  (defun my-make-backup-file-name (file)
    (make-backup-file-name-1 (file-truename file)))

  (defun backup-each-save-filter (filename)
    (not (string-match
          (concat "\\(^/tmp\\|\\.emacs\\.d/data\\(-alt\\)?/"
                  "\\|\\.newsrc\\(\\.eld\\)?\\|"
                  "\\(archive/sent/\\|recentf\\`\\)\\)")
          filename)))

  (defun my-dont-backup-files-p (filename)
    (unless (string-match filename "\\(archive/sent/\\|recentf\\`\\)")
      (normal-backup-enable-predicate filename)))

  :init
  (add-hook 'after-save-hook 'backup-each-save)
  :config
  (setq backup-each-save-filter-function 'backup-each-save-filter
        backup-enable-predicate 'my-dont-backup-files-p))

(use-package beacon
  :load-path "site-lisp/beacon"
  :diminish beacon-mode
  :commands beacon-mode)

(use-package bookmark+
  :load-path "site-lisp/bookmark-plus"
  :after bookmark)

(use-package browse-at-remote
  :load-path "site-lisp/browse-at-remote"
  :bind ("C-. g g" . browse-at-remote))

(use-package browse-kill-ring
  :load-path "site-lisp/browse-kill-ring"
  :defer 5
  :commands browse-kill-ring)

(use-package browse-kill-ring+
  :after browse-kill-ring)

(use-package bytecomp-simplify
  :defer 15)

(use-package c-includes
  :commands c-includes)

(use-package cc-mode
  :mode (("\\.h\\(h?\\|xx\\|pp\\)\\'" . c++-mode)
         ("\\.m\\'" . c-mode)
         ("\\.mm\\'" . c++-mode))
  :preface
  (defun my-c-mode-common-hook ()
    (eldoc-mode 1)
    (hide-ifdef-mode 1)
    (which-function-mode 1)
    (company-mode 1)
    (bug-reference-prog-mode 1)

    (diminish 'hide-ifdef-mode)

    (bind-key "<return>" #'newline-and-indent c-mode-base-map)

    (unbind-key "M-j" c-mode-base-map)
    (bind-key "C-c C-i" #'c-includes-current-file c-mode-base-map)

    (set (make-local-variable 'parens-require-spaces) nil)
    (setq indicate-empty-lines t)
    (setq fill-column 72)

    (bind-key "M-q" #'c-fill-paragraph c-mode-base-map)

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

  :config
  (add-hook 'c-mode-common-hook 'my-c-mode-common-hook)

  (setq c-syntactic-indentation nil)

  (bind-keys :map c++-mode-map
             ("<" . self-insert-command)
             (">" . self-insert-command))

  (bind-keys :map c-mode-base-map
             ("#" . self-insert-command)
             ("{" . self-insert-command)
             ("}" . self-insert-command)
             ("/" . self-insert-command)
             ("*" . self-insert-command)
             (";" . self-insert-command)
             ("," . self-insert-command)
             (":" . self-insert-command)
             ("(" . self-insert-command)
             (")" . self-insert-command))

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
  :load-path "site-lisp/circe"
  :if running-alternate-emacs
  :defer t)

(use-package cl-info
  :disabled t)

(use-package cldoc
  :commands (cldoc-mode turn-on-cldoc-mode)
  :diminish cldoc-mode)

(use-package cmake-font-lock
  :load-path "site-lisp/cmake-font-lock"
  :commands cmake-font-lock-activate
  :init
  (add-hook 'cmake-mode-hook #'cmake-font-lock-activate))

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
  :load-path "site-lisp/command-log-mode"
  :commands (command-log-mode
             clm/open-command-log-buffer))

(use-package company
  :load-path "site-lisp/company-mode"
  :demand t
  :diminish company-mode
  :commands (company-mode global-company-mode)
  :config
  (global-company-mode 1)
  (add-hook 'eshell-mode-hook #'(lambda () (company-mode -1)))

  ;; From https://github.com/company-mode/company-mode/issues/87
  ;; See also https://github.com/company-mode/company-mode/issues/123
  (defadvice company-pseudo-tooltip-unless-just-one-frontend
      (around only-show-tooltip-when-invoked activate)
    (when (company-explicit-action-p)
      ad-do-it))

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

  (eval-after-load "yasnippet"
    '(progn
       (defun company-mode/backend-with-yas (backend)
         (if (and (listp backend) (member 'company-yasnippet backend))
             backend
           (append (if (consp backend) backend (list backend))
                   '(:with company-yasnippet))))
       (setq company-backends
             (mapcar #'company-mode/backend-with-yas company-backends)))))

(use-package company-auctex
  :load-path "site-lisp/company-auctex"
  :after (company latex))

(use-package company-coq
  :load-path "site-lisp/company-coq"
  :after coq
  :commands company-coq-mode
  :config
  (bind-key "C-M-h" #'company-coq-toggle-definition-overlay coq-mode-map)
  (unbind-key "M-<return>" company-coq-map))

(use-package company-ghc
  :load-path "site-lisp/company-ghc"
  :after (company ghc)
  :config
  (add-to-list 'company-backends 'company-ghc))

(use-package company-math
  :load-path "site-lisp/company-math"
  :defer t)

(use-package compile
  :bind (("C-c c" . compile)
         ("M-O"   . show-compilation))
  :preface
  (defun show-compilation ()
    (interactive)
    (let ((buf (--first (string-match "\\*compilation\\*" (buffer-name it))
                        (buffer-list))))
      (if buf
          (aif (--first (window-frame it)
                        (get-buffer-window-list buf nil t))
              (make-frame-visible (window-frame it))
            (display-buffer-pop-up-frame buf '((inhibit-switch-frame . t))))
        (call-interactively 'compile))))

  (defun compilation-ansi-color-process-output ()
    (ansi-color-process-output nil)
    (set (make-local-variable 'comint-last-output-start)
         (point-marker)))

  :config
  (add-hook 'compilation-filter-hook #'compilation-ansi-color-process-output))

(use-package copy-as-format
  :load-path "site-lisp/copy-as-format"
  :bind ("C-. M-w" . copy-as-format)
  :init
  (setq copy-as-format-default "github"))

(use-package counsel
  :after ivy
  :demand t
  :diminish counsel-mode
  :bind (("M-x"     . counsel-M-x)
         ("C-s"     . counsel-grep-or-swiper)
         ("C-h f"   . counsel-describe-function)
         ("C-h v"   . counsel-describe-variable))
  :commands counsel-minibuffer-history
  :init
  (define-key minibuffer-local-map (kbd "M-r")
    'counsel-minibuffer-history)
  :config
  (counsel-mode 1))

(use-package counsel-projectile
  :load-path "site-lisp/counsel-projectile"
  :after (counsel projectile)
  :config
  (counsel-projectile-on)
  (define-key projectile-mode-map [remap projectile-ag]
    #'counsel-projectile-rg))

(use-package crosshairs
  :bind ("M-o c" . crosshairs-mode))

(use-package css-mode
  :mode "\\.css\\'"
  :defines css-syntax-propertize-function)

(use-package csv-mode
  :load-path "site-lisp/csv-mode"
  :mode "\\.csv\\'")

(use-package cursor-chg
  :commands change-cursor-mode
  :config
  (change-cursor-mode 1)
  (toggle-cursor-type-when-idle 1))

(use-package dash-at-point
  :load-path "site-lisp/dash-at-point"
  :bind ("C-c D" . dash-at-point)
  :config
  (add-to-list 'dash-at-point-mode-alist
               '(haskell-mode . "haskell")))

(use-package debbugs-gnu
  :load-path "site-lisp/debbugs"
  :commands (debbugs-gnu debbugs-gnu-search))

(use-package dedicated
  :bind ("C-. D" . dedicated-mode))

(use-package deft
  :load-path "site-lisp/deft"
  :commands deft)

(use-package diff-hl
  :load-path "site-lisp/diff-hl"
  :commands (diff-hl-mode diff-hl-dired-mode)
  :config
  (add-hook 'magit-post-refresh-hook 'diff-hl-magit-post-refresh))

(use-package diff-hl-flydiff
  :load-path "site-lisp/diff-hl"
  :commands diff-hl-flydiff-mode)

(use-package diff-mode
  :commands diff-mode)

(use-package diffview
  :load-path "site-lisp/diffview-mode"
  :commands (diffview-current diffview-region diffview-message))

(use-package dired
  :bind ("C-c J" . dired-double-jump)
  :preface
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

  (defun dired-double-jump (first-dir second-dir)
    (interactive
     (list (read-directory-name "First directory: "
                                (expand-file-name "~")
                                nil nil "dl/")
           (read-directory-name "Second directory: "
                                (expand-file-name "~")
                                nil nil "Archives/")))
    (dired first-dir)
    (dired-other-window second-dir))

  (defun my-dired-switch-window ()
    (interactive)
    (if (eq major-mode 'sr-mode)
        (call-interactively #'sr-change-window)
      (call-interactively #'other-window)))

  (defun ora-dired-rsync (dest)
    (interactive
     (list
      (expand-file-name
       (read-file-name "Rsync to: " (dired-dwim-target-directory)))))
    (let ((files (dired-get-marked-files
                  nil current-prefix-arg))
          (tmtxt/rsync-command
           "rsync -arvz --progress "))
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
            #'(lambda ()
                (bind-keys :map dired-mode-map
                           ("e"     . ora-ediff-files)
                           ("l"     . dired-up-directory)
                           ("Y"     . ora-dired-rsync)
                           ("<tab>" . my-dired-switch-window)
                           ("M-!"   . async-shell-command))
                (unbind-key "M-G" dired-mode-map)))

  (defadvice dired-omit-startup (after diminish-dired-omit activate)
    "Make sure to remove \"Omit\" from the modeline."
    (diminish 'dired-omit-mode) dired-mode-map)

  (defadvice dired-next-line (around dired-next-line+ activate)
    "Replace current buffer if file is a directory."
    ad-do-it
    (while (and  (not  (eobp)) (not ad-return-value))
      (forward-line)
      (setq ad-return-value(dired-move-to-filename)))
    (when (eobp)
      (forward-line -1)
      (setq ad-return-value(dired-move-to-filename))))

  (defadvice dired-previous-line (around dired-previous-line+ activate)
    "Replace current buffer if file is a directory."
    ad-do-it
    (while (and  (not  (bobp)) (not ad-return-value))
      (forward-line -1)
      (setq ad-return-value(dired-move-to-filename)))
    (when (bobp)
      (call-interactively 'dired-next-line)))

  (defvar dired-omit-regexp-orig (symbol-function 'dired-omit-regexp))

  ;; Omit files that Git would ignore
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
                (omitted-files
                 (shell-command-to-string "git clean -d -x -n")))
            (if (= 0 (length omitted-files))
                regexp
              (concat
               regexp
               (if (> (length regexp) 0)
                   "\\|" "")
               "\\("
               (mapconcat
                #'(lambda (str)
                    (concat
                     "^"
                     (regexp-quote
                      (substring str 13
                                 (if (= ?/ (aref str (1- (length str))))
                                     (1- (length str))
                                   nil)))
                     "$"))
                (split-string omitted-files "\n" t)
                "\\|")
               "\\)")))
        (funcall dired-omit-regexp-orig)))))

(use-package dired+
  :after dired
  :config
  (unbind-key "M-s f" dired-mode-map)

  (defun dired-do-delete (&optional arg)
    "Delete all marked (or next ARG) files.
`dired-recursive-deletes' controls whether deletion of
non-empty directories is allowed."
    ;; This is more consistent with the file marking feature than
    ;; dired-do-flagged-delete.
    (interactive "P")
    (dired-internal-do-deletions
     (nreverse
      ;; this may move point if ARG is an integer
      (dired-map-over-marks (cons (dired-get-filename) (point))
			    arg))
     arg t)))

(use-package dired-hacks
  :disabled t
  :load-path "site-lisp/dired-hacks"
  :init
  (autoload #'dired-filter-mode "dired-filter" nil t))

(use-package dired-ranger
  :bind (:map dired-mode-map
              ("W" . dired-ranger-copy)
              ("X" . dired-ranger-move)
              ("Y" . dired-ranger-paste)))

(use-package dired-toggle
  :load-path "site-lisp/dired-toggle"
  :bind ("C-. d" . dired-toggle)
  :preface
  (defun my-dired-toggle-mode-hook ()
    (interactive)
    (visual-line-mode 1)
    (setq-local visual-line-fringe-indicators '(nil right-curly-arrow))
    (setq-local word-wrap nil))
  :config
  (add-hook 'dired-toggle-mode-hook #'my-dired-toggle-mode-hook))

(use-package dired-x
  :after dired)

(use-package docker
  :load-path "site-lisp/docker-el"
  :defer 15
  :diminish docker-mode
  :config
  (docker-global-mode)
  (require 'docker-images)
  (require 'docker-containers)
  (require 'docker-volumes)
  (require 'docker-networks))

(use-package docker-compose-mode
  :load-path "site-lisp/docker-compose-mode")

(use-package docker-tramp
  :load-path "site-lisp/docker-tramp")

(use-package dockerfile-mode
  :load-path "site-lisp/dockerfile-mode"
  :mode "Dockerfile")

(use-package dot-gnus
  :bind (("M-G"   . switch-to-gnus)
         ("C-x m" . compose-mail))
  :init
  (setq gnus-init-file (emacs-path "dot-gnus")
        gnus-home-directory "~/Messages/Gnus/"))

(use-package dot-org
  :load-path ("site-lisp/org-mode/lisp"
              "site-lisp/org-mode/contrib/lisp")
  :commands my-org-startup
  :bind (("M-C"   . jump-to-org-agenda)
         ("M-m"   . org-smart-capture)
         ("M-M"   . org-inline-note)
         ("C-c a" . org-agenda)
         ("C-c S" . org-store-link)
         ("C-c l" . org-insert-link))
  :defer 30
  :config
  (when (and (not running-alternate-emacs)
             (not running-development-emacs))
    (run-with-idle-timer 300 t 'jump-to-org-agenda)
    (my-org-startup)))

(use-package doxymacs
  :load-path "site-lisp/doxymacs/lisp"
  :commands (doxymacs-mode doxymacs-font-lock)
  :config
  (doxymacs-mode 1)
  (doxymacs-font-lock))

(use-package dumb-jump
  :load-path "site-lisp/dumb-jump"
  :commands dumb-jump-mode
  :init
  (hook-into-modes #'dumb-jump-mode
                   'coq-mode-hook
                   'haskell-mode-hook))

(use-package ebdb-com
  :load-path "site-lisp/ebdb"
  :commands ebdb)

(use-package edebug
  :demand t
  :preface
  (defvar modi/fns-in-edebug nil
    "List of functions for which `edebug' is instrumented.")

  (defconst modi/fns-regexp
    (concat "(\\s-*"
            "\\(defun\\|defmacro\\)\\s-+"
            "\\(?1:\\(\\w\\|\\s_\\)+\\)\\_>") ; word or symbol char
    "Regexp to find defun or defmacro definition.")

  (defun modi/toggle-edebug-defun ()
    (interactive)
    (let (fn)
      (save-excursion
        (search-backward-regexp modi/fns-regexp)
        (setq fn (match-string 1))
        (mark-sexp)
        (narrow-to-region (point) (mark))
        (if (member fn modi/fns-in-edebug)
            ;; If the function is already being edebugged, uninstrument it
            (progn
              (setq modi/fns-in-edebug (delete fn modi/fns-in-edebug))
              (eval-region (point) (mark))
              (setq-default eval-expression-print-length 12)
              (setq-default eval-expression-print-level  4)
              (message "Edebug disabled: %s" fn))
          ;; If the function is not being edebugged, instrument it
          (progn
            (add-to-list 'modi/fns-in-edebug fn)
            (setq-default eval-expression-print-length nil)
            (setq-default eval-expression-print-level  nil)
            (edebug-defun)
            (message "Edebug: %s" fn)))
        (widen)))))

(use-package ediff
  :config
  (bind-keys ("C-. = b" . ediff-buffers)
             ("C-. = B" . ediff-buffers3)
             ("C-. = c" . compare-windows)
             ("C-. = =" . ediff-files)
             ("C-. = f" . ediff-files)
             ("C-. = F" . ediff-files3)
             ("C-. = r" . ediff-revision)
             ("C-. = p" . ediff-patch-file)
             ("C-. = P" . ediff-patch-buffer)
             ("C-. = l" . ediff-regions-linewise)
             ("C-. = w" . ediff-regions-wordwise)))

(use-package ediff-keep
  :after ediff)

(use-package edit-env
  :commands edit-env)

(use-package edit-indirect
  :bind ("C-c C" . edit-indirect-region))

(use-package edit-rectangle
  :bind ("C-. r" . edit-rectangle))

(use-package edit-var
  :bind ("C-c e v" . edit-variable))

(use-package eldoc
  :diminish eldoc-mode
  :commands eldoc-mode
  :config
  (eldoc-add-command 'paredit-backward-delete
                     'paredit-close-round))

(use-package elint
  :commands 'elint-initialize
  :preface
  (defun elint-current-buffer ()
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

(use-package elisp-slime-nav
  :load-path "site-lisp/elisp-slime-nav"
  :diminish elisp-slime-nav-mode
  :commands elisp-slime-nav-mode)

(use-package emacs-counsel-gtags
  :disabled t
  :load-path "site-lisp/emacs-counsel-gtags"
  :after counsel)

(use-package erc
  :if running-alternate-emacs
  :defer t
  :commands (erc erc-tls)
  :defines (erc-timestamp-only-if-changed-flag
            erc-timestamp-format
            erc-fill-prefix
            erc-fill-column
            erc-insert-timestamp-function
            erc-modified-channels-alist)
  :preface
  (defun irc ()
    (interactive)
    (let ((titan-ip "127.0.0.1"))
      (if t
          (progn
            (erc :server titan-ip
                 :port 6697
                 :nick "johnw"
                 :password (lookup-password titan-ip "johnw/freenode" 6697))
            (erc-tls :server "plclub.irc.slack.com"
                     :port 6697
                     :nick "jwiegley"
                     :password (lookup-password "plclub.irc.slack.com" "jwiegley" 6697)))
        (erc-tls :server "irc.freenode.net"
                 :port 6697
                 :nick "johnw"
                 :password (lookup-password "irc.freenode.net" "johnw" 6697)))))

  (defun setup-irc-environment ()
    (setq erc-timestamp-only-if-changed-flag nil
          erc-timestamp-format "%H:%M "
          erc-fill-prefix "          "
          erc-fill-column 88
          erc-insert-timestamp-function 'erc-insert-timestamp-left
          ivy-use-virtual-buffers nil)

    (defun reset-erc-track-mode ()
      (interactive)
      (setq erc-modified-channels-alist nil)
      (erc-modified-channels-update)
      (erc-modified-channels-display)
      (force-mode-line-update))

    (bind-key "C-c r" #'reset-erc-track-mode))

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
  (add-hook 'erc-mode-hook 'setup-irc-environment)
  (add-to-list 'erc-mode-hook
               #'(lambda () (set (make-local-variable 'scroll-conservatively) 100)))

  (add-hook 'after-init-hook 'irc)

  :config
  (erc-track-minor-mode 1)
  (erc-track-mode 1)

  (defadvice erc-scroll-to-bottom (around my-erc-scroll-to-bottom activate)
    "Ignore errors when attempting to scroll to the bottom."
    (ignore-errors ad-do-it))

  (add-hook 'erc-insert-pre-hook
            (lambda (s)
              (when (erc-foolish-content s)
                (setq erc-insert-this nil)))))

(use-package erc-alert
  :after erc)

(use-package erc-highlight-nicknames
  :after erc)

(use-package erc-macros
  :after erc)

(use-package erc-patch
  :after erc)

(use-package erc-question
  :after erc)

(use-package erc-yank
  :load-path "lisp/erc-yank"
  :after erc
  :bind (:map erc-mode-map
              ("C-y" . erc-yank )))

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

    (add-hook 'eshell-expand-input-functions 'eshell-spawn-external-command)

    (use-package em-unix
      :defer t
      :config
      (unintern 'eshell/su nil)
      (unintern 'eshell/sudo nil)))

  :init
  (add-hook 'eshell-first-time-mode-hook 'eshell-initialize))

(use-package eshell-bookmark
  :load-path "site-lisp/eshell-bookmark"
  :after eshell
  :config
  (add-hook 'eshell-mode-hook 'eshell-bookmark-setup))

(use-package etags
  :bind ("M-T" . tags-search))

(use-package eval-expr
  :load-path "site-lisp/eval-expr"
  :bind ("M-:" . eval-expr)
  :preface
  (defun my-elisp-indent-or-complete (&optional arg)
    (interactive "p")
    (call-interactively 'lisp-indent-line)
    (unless (or (looking-back "^\\s-*")
                (bolp)
                (not (looking-back "[-A-Za-z0-9_*+/=<>!?]+")))
      (call-interactively 'lisp-complete-symbol)))
  :config
  (defun eval-expr-minibuffer-setup ()
    (set-syntax-table emacs-lisp-mode-syntax-table)
    (local-set-key (kbd "<tab>") #'my-elisp-indent-or-complete)
    (paredit-mode)))

(use-package evil
  :load-path "site-lisp/evil"
  :commands evil-mode)

(use-package eww
  :bind ("A-M-g" . eww))

(use-package expand-region
  :load-path "site-lisp/expand-region-el"
  :bind ("C-. w" . er/expand-region))

(use-package eyebrowse
  :load-path "site-lisp/eyebrowse"
  :init
  (custom-set-variables
   `(eyebrowse-keymap-prefix ,(kbd "C-\\")))
  :config
  (eyebrowse-mode)
  (bind-key "C-\\ C-\\" #'eyebrowse-last-window-config eyebrowse-mode-map))

(use-package fancy-narrow
  :load-path "site-lisp/fancy-narrow"
  :bind (("C-. n" . fancy-narrow-to-region)
         ("C-. N" . fancy-widen))
  :commands (fancy-narrow-to-region fancy-widen))

(use-package fence-edit
  :load-path "site-lisp/fence-edit"
  :commands fence-edit-code-at-point)

(use-package fetchmail-mode
  :commands fetchmail-mode)

(use-package flycheck
  :load-path "site-lisp/flycheck"
  :defer 5
  :config
  (defalias 'flycheck-show-error-at-point-soon
    'flycheck-show-error-at-point))

(use-package flycheck-haskell
  :load-path "site-lisp/flycheck-haskell"
  :after haskell-mode
  :config
  (flycheck-haskell-setup)
  (bind-keys :map haskell-mode-map
             ("M-n" . flycheck-next-error)
             ("M-p" . flycheck-previous-error)))

(use-package flycheck-hdevtools
  :disabled t
  :load-path "site-lisp/flycheck-hdevtools"
  :after flycheck)

(use-package flyspell
  :bind (("C-c i b" . flyspell-buffer)
         ("C-c i f" . flyspell-mode))
  :config
  (unbind-key "C-." flyspell-mode-map))

(use-package font-lock-studio
  :load-path "site-lisp/font-lock-studio"
  :commands (font-lock-studio
             font-lock-studio-region))

(use-package free-keys
  :load-path "site-lisp/free-keys"
  :commands free-keys)

(use-package ggtags
  :disabled t
  :load-path "site-lisp/ggtags"
  :commands ggtags-mode
  :diminish ggtags-mode)

(use-package ghc
  ;; Disabled right now until https://github.com/DanielG/ghc-mod/issues/905 is
  ;; fixed, since the cabal helper is not being built.
  :disabled t
  :load-path
  (lambda ()
    (mapcar
     #'(lambda (conf)
         (with-temp-buffer
           (insert-file-contents-literally conf)
           (re-search-forward "^data-dir: \\(.+\\)" nil)
           (let ((data-dir (match-string 1)))
             (when (file-directory-p data-dir)
               (expand-file-name "elisp" data-dir)))))
     (cl-mapcan
      #'(lambda (ghc)
          (directory-files (expand-file-name "package.conf.d" ghc)
                           t "\\.conf$"))
      (cl-mapcan
       #'(lambda (lib) (directory-files lib t "^ghc-"))
       (cl-mapcan
        #'(lambda (path) (directory-files path t "^lib$"))
        (seq-filter
         (apply-partially #'string-match "-ghc-mod-")
         (nix-read-environment (concat "ghc" (getenv "GHCVER")))))))))
  :after haskell-mode
  :commands ghc-init
  :init
  (add-hook 'haskell-mode-hook #'(lambda () (ghc-init))))

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

(use-package git-link
  :load-path "site-lisp/git-link"
  :bind ("C-. G" . git-link)
  :commands (git-link git-link-commit git-link-homepage))

(use-package git-modes
  :load-path "site-lisp/git-modes"
  :init
  (use-package gitattributes-mode)
  (use-package gitconfig-mode)
  (use-package gitignore-mode))

(use-package git-timemachine
  :load-path "site-lisp/git-timemachine"
  :commands git-timemachine)

(use-package git-undo
  :load-path "lisp/git-undo-el"
  :bind ("C-. u" . git-undo))

(use-package github-pullrequest
  :load-path "site-lisp/github-pullrequest"
  :commands (github-pullrequest-new
             github-pullrequest-checkout))

(use-package gitpatch
  :load-path "site-lisp/gitpatch"
  :commands gitpatch-mail)

(use-package graphviz-dot-mode
  :mode "\\.dot\\'")

(use-package grep
  :bind (("M-s d" . find-grep-dired)
         ("M-s n" . find-name-dired)
         ("M-s f" . find-grep)
         ("M-s G" . grep)))

(use-package gud
  :commands gud-gdb
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
        (call-interactively 'gud-gdb))))
  :config
  (bind-keys ("<f9>"    . gud-cont)
             ("<f10>"   . gud-next)
             ("<f11>"   . gud-step)
             ("S-<f11>" . gud-finish)))

(use-package haskell-edit
  :load-path "lisp/haskell-config"
  :after haskell-mode
  :bind (:map haskell-mode-map
              ("C-c M-q" . haskell-edit-reformat)))

(use-package haskell-mode-autoloads
  :load-path "site-lisp/haskell-mode"
  :mode (("\\.hs\\(c\\|-boot\\)?\\'" . haskell-mode)
         ("\\.lhs\\'" . literate-haskell-mode)
         ("\\.cabal\\'" . haskell-cabal-mode))
  :preface
  (defvar interactive-haskell-mode-map)

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
    (unless (and hoogle-server-process
                 (process-live-p hoogle-server-process))
      (message "Starting local Hoogle server on port 8687...")
      (with-current-buffer (get-buffer-create " *hoogle-web*")
        (cd temporary-file-directory)
        (setq hoogle-server-process
              (start-process "hoogle-web" (current-buffer) "hoogle"
                             "server" "--local" "--port=8687")))
      (message "Starting local Hoogle server on port 8687...done"))
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
      ("`isProperSubsetOf`" . ?⊂)
      ("undefined"          . ?⊥)))

  :config
  (require 'haskell-mode)
  (require 'haskell-font-lock)

  (unbind-key "M-s" haskell-mode-map)
  (unbind-key "M-t" haskell-mode-map)

  (bind-keys :map haskell-mode-map
             ("C-c C-h" . my-haskell-hoogle)
             ("C-c C-," . haskell-navigate-imports)
             ("C-c C-." . haskell-mode-format-imports)
             ("C-c C-u" . (lambda () (interactive) (insert "undefined"))))

  (defun my-haskell-mode-hook ()
    (haskell-indentation-mode)
    (interactive-haskell-mode)
    (unbind-key "C-c c" interactive-haskell-mode-map)
    (flycheck-mode 1)
    (company-mode 1)
    (setq-local prettify-symbols-alist haskell-prettify-symbols-alist)
    (prettify-symbols-mode 1)
    (bug-reference-prog-mode 1))
  (add-hook 'haskell-mode-hook 'my-haskell-mode-hook)

  (eval-after-load 'align
    '(nconc
      align-rules-list
      (mapcar (lambda (x) `(,(car x)
                       (regexp . ,(cdr x))
                       (modes quote (haskell-mode literate-haskell-mode))))
              '((haskell-types       . "\\(\\s-+\\)\\(::\\|∷\\)\\s-+")
                (haskell-assignment  . "\\(\\s-+\\)=\\s-+")
                (haskell-arrows      . "\\(\\s-+\\)\\(->\\|→\\)\\s-+")
                (haskell-left-arrows . "\\(\\s-+\\)\\(<-\\|←\\)\\s-+"))))))

(use-package helm-config
  :load-path "site-lisp/helm"
  :if (not running-alternate-emacs)
  :demand t
  :bind ("C-c h" . helm-command-prefix)
  :config
  (use-package helm
    :config
    (helm-autoresize-mode 1))
  (use-package helm-multi-match)
  (bind-keys :map helm-map
             ("<tab>" . helm-execute-persistent-action)
             ("C-i"   . helm-execute-persistent-action)
             ("C-z"   . helm-select-action)
             ("A-v"   . helm-previous-page)))

(use-package helm-descbinds
  :load-path "site-lisp/helm-descbinds"
  :after helm
  :bind ("C-h b" . helm-descbinds)
  :init
  (fset 'describe-bindings 'helm-descbinds))

(use-package helm-describe-modes
  :load-path "site-lisp/helm-describe-modes"
  :after helm
  :bind ("C-h m" . helm-describe-modes))

(use-package helm-navi
  :load-path "site-lisp/helm-navi"
  :after (helm navi)
  :commands helm-navi)

(use-package helpful
  :load-path "site-lisp/helpful"
  :commands (helpful-function
             helpful-command
             helpful-macro
             helpful-callable
             helpful-variable
             helpful-at-point))

(use-package hi-lock
  :bind (("M-o l" . highlight-lines-matching-regexp)
         ("M-o r" . highlight-regexp)
         ("M-o w" . highlight-phrase)))

(use-package highlight
  :commands (hlt-highlight-region
             hlt-unhighlight-region)
  :init
  (bind-keys ("C-. h h" . hlt-highlight-region)
             ("C-. h u" . hlt-unhighlight-region)))

(use-package highlight-cl
  :init
  (autoload #'highlight-cl-add-font-lock-keywords "highlight-cl")
  (hook-into-modes #'highlight-cl-add-font-lock-keywords
                   'emacs-lisp-mode-hook))

(use-package highlight-numbers
  :load-path "site-lisp/highlight-numbers"
  :commands highlight-numbers-mode
  :init
  (hook-into-modes #'highlight-numbers-mode 'prog-mode-hook))

(use-package hilit-chg
  :bind ("M-o C" . highlight-changes-mode))

(use-package hippie-exp
  :bind ("C-. M-/" . hippie-expand))

(use-package hl-line
  :commands hl-line-mode
  :bind ("M-o h" . hl-line-mode))

(use-package hl-line+
  :after hl-line)

(use-package hydra
  :load-path "site-lisp/hydra"
  :demand t
  :config
  (defhydra hydra-zoom (global-map "<f2>")
    "zoom"
    ("g" text-scale-increase "in")
    ("l" text-scale-decrease "out")))

(use-package hyperbole
  :load-path "site-lisp/hyperbole"
  :defer 10
  :bind* (("M-."   . hkey-either)
          ("M-RET" . hkey-operate))
  :config
  (defact visit-haskell-definition ()
    "Go to the definition of a symbol in Haskell."
    (interactive)
    (condition-case err
        (call-interactively #'haskell-mode-jump-to-def-or-tag)
      (error
       (call-interactively #'dumb-jump-go))))

  (defib haskell-definition-link ()
    "Go to the definition of a symbol in Haskell."
    (and (eq major-mode 'haskell-mode)
         (hact #'visit-haskell-definition)))

  (defib gnus-article-urls-link ()
    "Visit the URLs in a Gnus article."
    (and (eq major-mode 'gnus-summary-mode)
         (hact #'gnus-article-browse-urls))))

(use-package ibuffer
  :bind ("C-x C-b" . ibuffer)
  :init
  (add-hook 'ibuffer-mode-hook
            #'(lambda ()
                (ibuffer-switch-to-saved-filter-groups "default"))))

(use-package ielm
  :commands ielm
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
        (call-interactively #'paredit-newline))))

  (add-hook 'ielm-mode-hook
            #'(lambda () (bind-key "<return>" #'my-ielm-return ielm-map)) t))

(use-package iflipb
  :load-path "site-lisp/iflipb"
  :bind ("<S-return>" . my-iflipb-next-buffer)
  :commands (iflipb-next-buffer iflipb-previous-buffer)
  :preface
  (defvar my-iflipb-auto-off-timeout-sec 2)
  (defvar my-iflipb-auto-off-timer-canceler-internal nil)
  (defvar my-iflipb-ing-internal nil)

  (defun my-iflipb-auto-off ()
    (message nil)
    (setq my-iflipb-auto-off-timer-canceler-internal nil
          my-iflipb-ing-internal nil))

  (defun my-iflipb-next-buffer (arg)
    (interactive "P")
    (iflipb-next-buffer arg)
    (if my-iflipb-auto-off-timer-canceler-internal
        (cancel-timer my-iflipb-auto-off-timer-canceler-internal))
    (run-with-idle-timer my-iflipb-auto-off-timeout-sec 0 'my-iflipb-auto-off)
    (setq my-iflipb-ing-internal t))

  (defun my-iflipb-previous-buffer ()
    (interactive)
    (iflipb-previous-buffer)
    (if my-iflipb-auto-off-timer-canceler-internal
        (cancel-timer my-iflipb-auto-off-timer-canceler-internal))
    (run-with-idle-timer my-iflipb-auto-off-timeout-sec 0 'my-iflipb-auto-off)
    (setq my-iflipb-ing-internal t))

  :config
  (setq iflipb-always-ignore-buffers
        "\\`\\( \\|diary\\|ipa\\|\\.newsrc-dribble\\'\\)"
        iflipb-wrap-around t)

  (defun iflipb-first-iflipb-buffer-switch-command ()
    (not (and (or (eq last-command 'my-iflipb-next-buffer)
                  (eq last-command 'my-iflipb-previous-buffer))
              my-iflipb-ing-internal))))

(use-package image-file
  :config
  (auto-image-file-mode 1))

(use-package indent
  :commands indent-according-to-mode)

(use-package indent-shift
  :load-path "site-lisp/indent-shift"
  :bind (("C-c <" . indent-shift-left)
         ("C-c >" . indent-shift-right)))

(use-package info
  :bind ("C-h C-i" . info-lookup-symbol)
  :init
  (remove-hook 'menu-bar-update-hook 'mac-setup-help-topics)
  :config
  (defadvice Info-exit (after remove-info-window activate)
    "When info mode is quit, remove the window."
    (if (> (length (window-list)) 1)
        (delete-window))))

(use-package info-look
  :commands info-lookup-add-help)

(use-package info-lookmore
  :load-path "site-lisp/info-lookmore"
  :config
  (info-lookmore-elisp-cl)
  (info-lookmore-elisp-userlast)
  (info-lookmore-elisp-gnus)
  (info-lookmore-apropos-elisp))

(use-package initsplit
  :load-path "lisp/initsplit"
  :after cus-edit)

(use-package inventory
  :commands (inventory sort-package-declarations))

(use-package isearch
  :no-require t
  :bind (("C-M-r" . isearch-backward-other-window)
         ("C-M-s" . isearch-forward-other-window))
  :preface
  (defun isearch-backward-other-window ()
    (interactive)
    (split-window-vertically)
    (call-interactively 'isearch-backward))

  (defun isearch-forward-other-window ()
    (interactive)
    (split-window-vertically)
    (call-interactively 'isearch-forward))

  :config
  (bind-keys :map isearch-mode-map
             ("C-c" . isearch-toggle-case-fold)
             ("C-t" . isearch-toggle-regexp)
             ("C-^" . isearch-edit-string)
             ("C-i" . isearch-complete)))

(use-package ispell
  :bind (("C-c i c" . ispell-comments-and-strings)
         ("C-c i d" . ispell-change-dictionary)
         ("C-c i k" . ispell-kill-ispell)
         ("C-c i m" . ispell-message)
         ("C-c i r" . ispell-region)))

(use-package ivy
  :load-path "site-lisp/swiper"
  :demand t
  :diminish ivy-mode
  :bind (("C-x b" . ivy-switch-buffer)
         ("C-x B" . ivy-switch-buffer-other-window)
         ("M-H"   . ivy-resume))
  :commands (ivy-mode ivy-read ivy-completing-read)
  :init
  (defun my-ivy-completing-read (&rest args)
    (let ((ivy-sort-functions-alist '((t . nil))))
      (apply 'ivy-completing-read args)))

  :config
  (setq ivy-initial-inputs-alist nil
        ivy-re-builders-alist '((t . ivy--regex-ignore-order)))

  (ivy-mode 1)

  (ivy-set-occur 'ivy-switch-buffer 'ivy-switch-buffer-occur)

  (bind-keys :map ivy-minibuffer-map
             ("C-r" . ivy-previous-line-or-history)
             ("M-r" . ivy-reverse-i-search)))

(use-package ivy-hydra
  :after (ivy hydra)
  :demand t)

(use-package ivy-rich
  :load-path "site-lisp/ivy-rich"
  :demand t
  :after ivy
  :config
  (ivy-set-display-transformer 'ivy-switch-buffer
                               'ivy-rich-switch-buffer-transformer)
  (setq ivy-virtual-abbreviate 'full
        ivy-rich-switch-buffer-align-virtual-buffer t)
  (setq ivy-rich-path-style 'abbrev))

(use-package js2-mode
  :load-path "site-lisp/js2-mode"
  :mode "\\.js\\'"
  :config
  (setq flycheck-disabled-checkers
        (append flycheck-disabled-checkers
                '(javascript-jshint)))

  (flycheck-add-mode 'javascript-eslint 'js2-mode)
  (flycheck-mode 1)

  (bind-keys :map js2-mode-map
             ("M-n" . flycheck-next-error)
             ("M-p" . flycheck-previous-error)))

(use-package json-mode
  :load-path "site-lisp/json-mode"
  :mode "\\.json\\'")

(use-package json-reformat
  :load-path "site-lisp/json-reformat"
  :after json-mode)

(use-package json-snatcher
  :load-path "site-lisp/json-snatcher"
  :after json-mode)

(use-package kotl-mode
  :load-path "site-lisp/hyperbole/kotl"
  :mode "\\.kotl\\'")

(use-package ledger-mode
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
        (forward-line)))))

(use-package lentic-mode
  :load-path "site-lisp/lentic"
  :diminish lentic-mode
  :commands global-lentic-mode)

(use-package lisp-mode
  :defer t
  :preface
  (defface esk-paren-face
    '((((class color) (background dark))
       (:foreground "grey50"))
      (((class color) (background light))
       (:foreground "grey55")))
    "Face used to dim parentheses."
    :group 'starter-kit-faces)

  (defun my-lisp-mode-hook ()
    (paredit-mode 1)
    (redshank-mode 1)
    (auto-fill-mode 1)
    (elisp-slime-nav-mode 1)

    (bind-key "<return>" #'paredit-newline lisp-mode-map)
    (bind-key "<return>" #'paredit-newline emacs-lisp-mode-map)

    (add-hook 'after-save-hook 'check-parens nil t)

    (unless (memq major-mode
                  '(emacs-lisp-mode inferior-emacs-lisp-mode ielm-mode))
      (turn-on-cldoc-mode)
      (bind-key "M-q" #'slime-reindent-defun lisp-mode-map)
      (bind-key "M-l" #'slime-selector lisp-mode-map)))

  ;; Change lambda to an actual lambda symbol
  :init
  (mapc #'(lambda (major-mode)
            (font-lock-add-keywords
             major-mode
             '(("(\\(lambda\\)\\>"
                (0 (ignore
                    (compose-region (match-beginning 1)
                                    (match-end 1) ?λ))))
               ;; For the moment I'm using rainbow-delimiters
               ;; ("(\\|)" . 'esk-paren-face)
               ("(\\(ert-deftest\\)\\>[         '(]*\\(setf[    ]+\\sw+\\|\\sw+\\)?"
                (1 font-lock-keyword-face)
                (2 font-lock-function-name-face
                   nil t)))))
        '(emacs-lisp-mode
          inferior-emacs-lisp-mode
          ielm-mode
          lisp-mode
          inferior-lisp-mode
          lisp-interaction-mode
          slime-repl-mode))

  (hook-into-modes #'my-lisp-mode-hook
                   'emacs-lisp-mode-hook
                   'inferior-emacs-lisp-mode-hook
                   'ielm-mode-hook
                   'lisp-mode-hook
                   'inferior-lisp-mode-hook
                   'lisp-interaction-mode-hook
                   'slime-repl-mode-hook))

(use-package llvm-mode
  :mode "\\.ll\\'")

(use-package lsp-mode
  ;; jww (2017-11-26): Need to install LSP for Haskell
  :disabled t
  :load-path "site-lisp/lsp-mode")

(use-package lua-mode
  :load-path "site-lisp/lua-mode"
  :mode "\\.lua\\'"
  :interpreter "lua")

(use-package lusty-explorer
  :load-path "site-lisp/lusty-emacs"
  :demand t
  :bind (("C-x C-f" . my-lusty-file-explorer)
         ("C-x C-w" . my-write-file))
  :preface
  (defun lusty-read-directory ()
    "Launch the file/directory mode of LustyExplorer."
    (interactive)
    (require 'lusty-explorer)
    (let ((lusty--active-mode :file-explorer))
      (lusty--define-mode-map)
      (let* ((lusty--ignored-extensions-regex
              (concat "\\(?:" (regexp-opt completion-ignored-extensions)
                      "\\)$"))
             (minibuffer-local-filename-completion-map lusty-mode-map)
             (lusty-only-directories t))
        (lusty--run 'read-directory-name default-directory ""))))

  (defun lusty-read-file-name
      (prompt &optional dir default-filename mustmatch initial predicate)
    "Launch the file/directory mode of LustyExplorer."
    (interactive)
    (require 'lusty-explorer)
    (let ((lusty--active-mode :file-explorer)
          (ivy-mode-prev (and (boundp 'ivy-mode) ivy-mode)))
      (if (fboundp 'ivy-mode)
          (ivy-mode -1))
      (unwind-protect
          (progn
            (lusty--define-mode-map)
            (let* ((lusty--ignored-extensions-regex
                    (concat "\\(?:" (regexp-opt completion-ignored-extensions)
                            "\\)$"))
                   (minibuffer-local-filename-completion-map lusty-mode-map)
                   (lusty-only-directories nil))
              (lusty--run 'read-file-name
                          dir default-filename mustmatch initial predicate)))
        (if (fboundp 'ivy-mode)
            (ivy-mode (if ivy-mode-prev 1 -1))))))

  (defun my-lusty-file-explorer ()
    "Launch the file/directory mode of LustyExplorer."
    (interactive)
    (require 'lusty-explorer)
    (let ((lusty--active-mode :file-explorer)
          (ivy-mode-prev (and (boundp 'ivy-mode) ivy-mode)))
      (if (fboundp 'ivy-mode)
          (ivy-mode -1))
      (unwind-protect
          (progn
            (lusty--define-mode-map)
            (let* ((lusty--ignored-extensions-regex
                    (concat "\\(?:" (regexp-opt
                                     completion-ignored-extensions) "\\)$"))
                   (minibuffer-local-filename-completion-map lusty-mode-map)
                   (file
                    ;; read-file-name is silly in that if the result is equal
                    ;; to the dir argument, it gets converted to the
                    ;; default-filename argument.  Set it explicitly to "" so
                    ;; if lusty-launch-dired is called in the directory we
                    ;; start at, the result is that directory instead of the
                    ;; name of the current buffer.
                    (lusty--run 'read-file-name default-directory "")))
              (when file
                (switch-to-buffer
                 (find-file-noselect
                  (expand-file-name file))))))
        (if (fboundp 'ivy-mode)
            (ivy-mode (if ivy-mode-prev 1 -1))))))

  :config
  (defun my-lusty-setup-hook ()
    (bind-key "SPC" #'lusty-select-match lusty-mode-map)
    (bind-key "C-d" #'exit-minibuffer lusty-mode-map))

  (add-hook 'lusty-setup-hook 'my-lusty-setup-hook)

  (defun lusty-open-this ()
    "Open the given file/directory/buffer, creating it if not already present."
    (interactive)
    (when lusty--active-mode
      (ecase lusty--active-mode
        (:file-explorer
         (let* ((path (minibuffer-contents-no-properties))
                (last-char (aref path (1- (length path)))))
           (lusty-select-match)
           (lusty-select-current-name)))
        (:buffer-explorer (lusty-select-match)))))

  (defun my-write-file (filename &optional confirm)
    (interactive
     (list (if buffer-file-name
	       (lusty-read-file-name "Write file: "
			             nil nil nil nil)
	     (lusty-read-file-name "Write file: " default-directory
			           (expand-file-name
			            (file-name-nondirectory (buffer-name))
			            default-directory)
			           nil nil))
	   (not current-prefix-arg)))
    (write-file filename confirm))

  (defvar lusty-only-directories nil)

  (defun lusty-file-explorer-matches (path)
    (let* ((dir (lusty-normalize-dir (file-name-directory path)))
           (file-portion (file-name-nondirectory path))
           (files
            (and dir
                 ;; NOTE: directory-files is quicker but
                 ;;       doesn't append slash for directories.
                 ;;(directory-files dir nil nil t)
                 (file-name-all-completions "" dir)))
           (filtered (lusty-filter-files
                      file-portion
                      (if lusty-only-directories
                          (loop for f in files
                                when (= ?/ (aref f (1- (length f))))
                                collect f)
                        files))))
      (if (or (string= file-portion "")
              (string= file-portion "."))
          (sort filtered 'string<)
        (lusty-sort-by-fuzzy-score filtered file-portion)))))

(use-package macrostep
  :load-path "site-lisp/macrostep"
  :bind ("C-c e m" . macrostep-expand))

(use-package magit
  :load-path ("site-lisp/magit/lisp"
              "lib/with-editor")
  :bind (("C-x g" . magit-status)
         ("C-x G" . magit-status-with-prefix))
  :preface
  (defun magit-monitor (&optional no-display)
    "Start git-monitor in the current directory."
    (interactive)
    (when (string-match "\\*magit: \\(.+\\)" (buffer-name))
      (let ((name (format "*git-monitor: %s*"
                          (match-string 1 (buffer-name)))))
        (or (get-buffer name)
            (let ((buf (get-buffer-create name)))
              (ignore-errors
                (start-process "*git-monitor*" buf "git-monitor"
                               "-d" (expand-file-name default-directory)))
              buf)))))

  (defun magit-status-with-prefix ()
    (interactive)
    (let ((current-prefix-arg '(4)))
      (call-interactively 'magit-status)))

  (defun lusty-magit-status (dir &optional switch-function)
    (interactive (list (if current-prefix-arg
                           (lusty-read-directory)
                         (or (magit-get-top-dir)
                             (lusty-read-directory)))))
    (magit-status-internal dir switch-function))

  (defun eshell/git (&rest args)
    (cond
     ((or (null args)
          (and (string= (car args) "status") (null (cdr args))))
      (magit-status-internal default-directory))
     ((and (string= (car args) "log") (null (cdr args)))
      (magit-log "HEAD"))
     (t (throw 'eshell-replace-command
               (eshell-parse-command
                "*git"
                (eshell-stringify-list (eshell-flatten-list args)))))))

  :init
  (add-hook 'magit-mode-hook 'hl-line-mode)

  :config
  (setenv "GIT_PAGER" "")

  (use-package magit-commit
    :config
    (remove-hook 'server-switch-hook 'magit-commit-diff)
    (use-package git-commit))

  (use-package magit-files
    :config
    (global-magit-file-mode))

  (unbind-key "M-h" magit-mode-map)
  (unbind-key "M-s" magit-mode-map)
  (unbind-key "M-m" magit-mode-map)
  (unbind-key "M-w" magit-mode-map)
  (unbind-key "<C-return>" magit-file-section-map)

  ;; (bind-key "M-H" #'magit-show-level-2-all magit-mode-map)
  ;; (bind-key "M-S" #'magit-show-level-4-all magit-mode-map)
  (bind-key "U" #'magit-unstage-all magit-mode-map)

  (add-hook 'magit-log-edit-mode-hook
            #'(lambda ()
                (set-fill-column 72)
                (flyspell-mode 1)))

  (add-hook 'magit-status-mode-hook #'(lambda () (magit-monitor t)))

  (remove-hook 'server-switch-hook 'magit-commit-diff))

(use-package magit-imerge
  :disabled t
  :load-path "site-lisp/magit-imerge"
  :after magit)

(use-package magithub
  :disabled t
  :load-path "site-lisp/magithub"
  :after magit
  :config
  (magithub-feature-autoinject t))

(use-package malyon
  :load-path "site-lisp/malyon"
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
  :load-path "site-lisp/markdown-mode"
  :mode (("\\`README\\.md\\'" . gfm-mode)
         ("\\.md\\'"          . markdown-mode)
         ("\\.markdown\\'"    . markdown-mode))
  :init (setq markdown-command "multimarkdown"))

(use-package markdown-preview-mode
  :load-path "site-lisp/markdown-preview-mode"
  :after markdown-mode
  :config
  (setq markdown-preview-stylesheets
        (list (concat "https://github.com/dmarcotte/github-markdown-preview/"
                      "blob/master/data/css/github.css"))))

(use-package math-symbol-lists
  :load-path "site-lisp/math-symbol-lists"
  :defer t)

(use-package mediawiki
  :load-path "site-lisp/mediawiki"
  :commands mediawiki-open)

(use-package memory-usage
  :commands memory-usage)

(use-package mic-paren
  :defer 5
  :config
  (paren-activate))

(use-package midnight
  :defer 10)

(use-package minimap
  :load-path "site-lisp/minimap"
  :commands minimap-mode)

(use-package moccur-edit
  :after color-moccur)

(use-package mule
  :no-require t
  :defines x-select-request-type
  :config
  (prefer-coding-system 'utf-8)
  (set-terminal-coding-system 'utf-8)
  (setq x-select-request-type '(UTF8_STRING COMPOUND_TEXT TEXT STRING)))

(use-package multi-term
  :load-path "site-lisp/multi-term"
  :bind (("C-. t" . multi-term-next)
         ("C-. T" . multi-term))
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
  :load-path "site-lisp/multifiles-el"
  :bind ("C-c m f" . mf/mirror-region-in-multifile))

(use-package multiple-cursors
  :load-path "site-lisp/multiple-cursors"
  :after phi-search
  :bind (("C-. c"   . mc/edit-lines)
         ("C-'"     . mc/edit-lines)
         ("C->"     . mc/mark-next-like-this)
         ("C-<"     . mc/mark-previous-like-this)
         ("C-c C-<" . mc/mark-all-like-this)

         ("C-c m n" . mc/insert-numbers)
         ("C-c m l" . mc/insert-letters)
         ("C-c m s" . mc/sort-regions)
         ("C-c m R" . mc/reverse-regions)
         ("C-c m r" . set-rectangular-region-anchor)))

(use-package my-compile
  :after compile)

(use-package navi
  :load-path "site-lisp/navi"
  :after outshine)

(use-package nf-procmail-mode
  :commands nf-procmail-mode)

(use-package nix-buffer
  :load-path "site-lisp/nix-buffer"
  :commands nix-buffer)

(use-package nix-mode
  :load-path "site-lisp/nix-mode"
  :mode "\\.nix\\'")

(use-package nroff-mode
  :commands nroff-mode
  :config
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
            #'(lambda () (add-hook 'after-save-hook 'update-nroff-timestamp nil t))))

(use-package nxml-mode
  :commands nxml-mode
  :init
  (defalias 'xml-mode 'nxml-mode)
  :config
  (defun my-nxml-mode-hook ()
    (bind-key "<return>" #'newline-and-indent nxml-mode-map))

  (add-hook 'nxml-mode-hook 'my-nxml-mode-hook)

  (defun tidy-xml-buffer ()
    (interactive)
    (save-excursion
      (call-process-region (point-min) (point-max) "tidy" t t nil
                           "-xml" "-i" "-wrap" "0" "-omit" "-q" "-utf8")))

  (bind-key "C-c M-h" #'tidy-xml-buffer nxml-mode-map)

  (require 'hideshow)
  (require 'sgml-mode)

  (add-to-list 'hs-special-modes-alist
               '(nxml-mode
                 "<!--\\|<[^/>]*[^/]>"
                 "-->\\|</[^/>]*[^/]>"

                 "<!--"
                 sgml-skip-tag-forward
                 nil))

  (add-hook 'nxml-mode-hook 'hs-minor-mode)

  ;; optional key bindings, easier than hs defaults
  (bind-key "C-c h" #'hs-toggle-hiding nxml-mode-map))

(use-package outline
  :commands outline-minor-mode
  :diminish outline-minor-mode
  :init
  (hook-into-modes #'outline-minor-mode
                   'emacs-lisp-mode-hook
                   'LaTeX-mode-hook))

(use-package outorg
  :load-path "site-lisp/outorg"
  :after outshine)

(use-package outshine
  :load-path "site-lisp/outshine"
  :after outline
  :init
  (add-hook 'outline-minor-mode-hook 'outshine-hook-function))

(use-package pandoc-mode
  :load-path "site-lisp/pandoc-mode"
  :commands pandoc-mode
  :init
  (add-hook 'markdown-mode-hook 'pandoc-mode)
  :config
  (add-hook 'pandoc-mode-hook 'pandoc-load-default-settings))

(use-package paredit
  :load-path "site-lisp/paredit"
  :commands paredit-mode
  :diminish paredit-mode
  :config
  (add-hook 'paredit-mode-hook
            #'(lambda ()
                (unbind-key "M-r" paredit-mode-map)
                (unbind-key "M-s" paredit-mode-map)))
  (bind-keys :map paredit-mode-map
             (")"     . paredit-close-round-and-newline)
             ("M-)"   . paredit-close-round)
             ("M-k"   . paredit-raise-sexp)
             ("M-I"   . paredit-splice-sexp)
             ("C-M-l" . paredit-recentre-on-sexp)

             ("C-. D" . paredit-forward-down)
             ("C-. B" . paredit-splice-sexp-killing-backward)
             ("C-. C" . paredit-convolute-sexp)
             ("C-. F" . paredit-splice-sexp-killing-forward)
             ("C-. a" . paredit-add-to-next-list)
             ("C-. A" . paredit-add-to-previous-list)
             ("C-. j" . paredit-join-with-next-list)
             ("C-. J" . paredit-join-with-previous-list)))

(use-package paredit-ext
  :after paredit)

(use-package pcre2el
  :load-path "site-lisp/pcre2el"
  :commands (rxt-mode rxt-global-mode))

(use-package pdf-tools
  :load-path "site-lisp/pdf-tools"
  :defer 15
  :mode "\\.pdf\\'"
  :config (pdf-tools-install))

(use-package per-window-point
  :commands pwp-mode
  :defer 5
  :config
  (pwp-mode 1))

(use-package persistent-scratch
  :if (and window-system
           (not running-alternate-emacs)
           (not running-development-emacs)
           (not noninteractive)))

(use-package personal
  :after (crux counsel)
  :config
  (define-key key-translation-map (kbd "A-TAB") (kbd "C-TAB"))

  (bind-keys* ("<C-return>" . other-window))

  (bind-keys ("C-z" . delete-other-windows)

             ("M-!"  . async-shell-command)
             ("M-'"  . insert-pair)
             ("M-\"" . insert-pair)
             ("M-`"  . other-frame)
             ("M-j"  . delete-indentation-forward)
             ("M-J"  . delete-indentation)
             ("M-W"  . mark-word)
             ("M-L"  . mark-line)
             ("M-S"  . mark-sentence)
             ("M-X"  . mark-sexp)
             ("M-D"  . mark-defun)

             ("M-g c" . goto-char)
             ("M-g l" . goto-line)

             ("<C-M-backspace>" . backward-kill-sexp)

             ("C-x d"   . delete-whitespace-rectangle)
             ("C-x F"   . set-fill-column)
             ("C-x t"   . toggle-truncate-lines)
             ("C-x v H" . vc-region-history)
             ("C-x K"   . delete-current-buffer-file)

             ("C-x C-d" . duplicate-line)
             ("C-x C-e" . pp-eval-last-sexp)
             ("C-x C-n" . next-line)
             ("C-x C-v" . find-alternate-file-with-sudo)

             ("C-x M-q" . refill-paragraph)

             ("C-c SPC" . just-one-space)
             ("C-c 0"   . recursive-edit-preserving-window-config-pop)
             ("C-c 1"   . recursive-edit-preserving-window-config)
             ("C-c g"   . goto-line)
             ("C-c f"   . flush-lines)
             ("C-c k"   . keep-lines)
             ("C-c n"   . insert-user-timestamp)
             ("C-c o"   . customize-option)
             ("C-c O"   . customize-group)
             ("C-c F"   . customize-face)
             ("C-c q"   . fill-region)
             ("C-c r"   . replace-regexp)
             ("C-c s"   . replace-string)
             ("C-c u"   . rename-uniquely)
             ("C-c v"   . ffap)
             ("C-c V"   . view-clipboard)
             ("C-c z"   . clean-buffer-list)
             ("C-c )"   . close-all-parentheses)
             ("C-c ="   . count-matches)
             ("C-c ;"   . comment-or-uncomment-region)

             ("C-c C-z" . delete-to-end-of-buffer)
             ("C-c C-0" . copy-current-buffer-name)

             ("C-c M-q" . unfill-paragraph))

  (bind-keys ("C-h e e" . view-echo-area-messages)
             ("C-h e f" . find-function)
             ("C-h e k" . find-function-on-key)
             ("C-h e l" . find-library)
             ("C-h e P" . check-papers)
             ("C-h e s" . scratch)
             ("C-h e v" . find-variable)
             ("C-h e V" . apropos-value))

  (bind-keys ("C-c e E" . elint-current-buffer)
             ("C-c e b" . do-eval-buffer)
             ("C-c e c" . cancel-debug-on-entry)
             ("C-c e d" . debug-on-entry)
             ("C-c e e" . toggle-debug-on-error)
             ("C-c e f" . emacs-lisp-byte-compile-and-load)
             ("C-c e i" . crux-find-user-init-file)
             ("C-c e j" . emacs-lisp-mode)
             ("C-c e l" . counsel-find-library)
             ("C-c e r" . do-eval-region)
             ("C-c e s" . scratch)
             ("C-c e u" . counsel-unicode-char)
             ("C-c e z" . byte-recompile-directory))

  (bind-keys ("C-c m k" . kmacro-keymap)
             ("C-c m m" . emacs-toggle-size)))

(use-package phi-search
  :load-path "site-lisp/phi-search"
  ;; When multiple-cursors is loaded, if this is loaded also then C-s and C-r
  ;; will be bound to phi-search and phi-search-backward, which work with mc.
  :after multiple-cursors)

(use-package po-mode
  :mode "\\.\\(po\\'\\|po\\.\\)")

(use-package popup-ruler
  :bind ("C-. C-r" . popup-ruler))

(use-package powerline
  :disabled t
  :load-path "site-lisp/powerline")

(use-package pp-c-l
  :commands pretty-control-l-mode
  :init
  (add-hook 'prog-mode-hook 'pretty-control-l-mode))

(use-package prodigy
  :load-path "site-lisp/prodigy"
  :commands prodigy)

(use-package projectile
  :load-path "site-lisp/projectile"
  :diminish projectile-mode
  :commands projectile-global-mode
  :defer 5
  :bind-keymap ("C-c p" . projectile-command-map)
  :config
  (projectile-global-mode))

(use-package proof-site
  :load-path ("site-lisp/ProofGeneral/generic"
              "site-lisp/ProofGeneral/lib"
              "site-lisp/ProofGeneral/coq")
  :mode ("\\.v\\'" . coq-mode)

  :preface
  (eval-when-compile
    (defvar proof-auto-raise-buffers)
    (defvar proof-three-window-enable)
    (defvar proof-shrink-windows-tofit)

    (declare-function proof-get-window-for-buffer "proof-utils")
    (declare-function proof-resize-window-tofit "proof-utils")
    (declare-function window-bottom-p "proof-compat"))

  :config
  (use-package coq
    :no-require t
    :defer t
    :defines coq-mode-map
    :functions (proof-layout-windows coq-SearchConstant)
    :config
    (add-hook
     'coq-mode-hook
     (lambda ()
       (set-input-method "Agda")
       (holes-mode -1)
       (company-coq-mode 1)
       (set (make-local-variable 'fill-nobreak-predicate)
            (lambda ()
              (pcase (get-text-property (point) 'face)
                ('font-lock-comment-face nil)
                ((pred (lambda (x)
                         (and (listp x)
                              (memq 'font-lock-comment-face x)))) nil)
                (_ t))))))

    (defalias 'coq-Search #'coq-SearchConstant)
    (defalias 'coq-SearchPattern #'coq-SearchIsos)

    (bind-keys :map coq-mode-map
               ("M-RET"       . proof-goto-point)
               ("RET"         . newline-and-indent)
               ("C-c C-p"     . (lambda ()
                                  (interactive)
                                  (proof-layout-windows)
                                  (proof-prf)))
               ("C-c C-a C-s" . coq-Search)
               ("C-c C-a C-o" . coq-SearchPattern)
               ("C-c C-a C-a" . coq-SearchAbout)
               ("C-c C-a C-r" . coq-SearchRewrite))

    (unbind-key "C-c h" coq-mode-map))

  (use-package pg-user
    :defer t
    :config
    (defadvice proof-retract-buffer
        (around my-proof-retract-buffer activate)
      (condition-case err ad-do-it
        (error (shell-command "killall coqtop"))))))

(use-package prover
  :after coq)

(use-package ps-print
  :defer t
  :config
  (defun ps-spool-to-pdf (beg end &rest ignore)
    (interactive "r")
    (let ((temp-file (concat (make-temp-name "ps2pdf") ".pdf")))
      (call-process-region beg end (executable-find "ps2pdf")
                           nil nil nil "-" temp-file)
      (call-process (executable-find "open") nil nil nil temp-file)))

  (setq ps-print-region-function 'ps-spool-to-pdf))

(use-package python-mode
  :load-path "site-lisp/python-mode"
  :mode "\\.py\\'"
  :interpreter "python"
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

    (setq indicate-empty-lines t)
    (set (make-local-variable 'parens-require-spaces) nil)
    (setq indent-tabs-mode nil)

    (bind-key "C-c C-z" #'python-shell python-mode-map)
    (unbind-key "C-c c" python-mode-map))

  (add-hook 'python-mode-hook 'my-python-mode-hook))

(use-package rainbow-delimiters
  :load-path "site-lisp/rainbow-delimiters"
  :commands rainbow-delimiters-mode
  :init
  (add-hook 'prog-mode-hook #'rainbow-delimiters-mode))

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
  :init
  (add-hook 'dired-mode-hook 'recentf-add-dired-directory)
  :config
  (recentf-mode 1))

(use-package redshank
  :load-path "site-lisp/redshank"
  :diminish redshank-mode
  :commands redshank-mode)

(use-package regex-tool
  :load-path "lisp/regex-tool"
  :commands regex-tool)

(use-package restclient
  :load-path "site-lisp/restclient"
  :mode ("\\.rest\\'" . restclient-mode))

(use-package ruby-mode
  :load-path "site-lisp/ruby-mode"
  :mode "\\.rb\\'"
  :interpreter "ruby"
  :functions inf-ruby-keys
  :config
  (defun my-ruby-smart-return ()
    (interactive)
    (when (memq (char-after) '(?\| ?\" ?\'))
      (forward-char))
    (call-interactively 'newline-and-indent))

  (defun my-ruby-mode-hook ()
    (require 'inf-ruby)
    (inf-ruby-keys)
    (bind-key "<return>" #'my-ruby-smart-return ruby-mode-map))

  (add-hook 'ruby-mode-hook 'my-ruby-mode-hook))

(use-package selected
  :load-path "site-lisp/selected"
  :defer 5
  :diminish selected-minor-mode
  :config
  (selected-global-mode 1)
  (bind-keys :map selected-keymap
             ("[" . align-regexp)
             ("f" . fill-region)
             ("U" . unfill-region)
             ("d" . downcase-region)
             ("r" . reverse-region)
             ("s" . sort-lines)
             ("u" . upcase-region)))

(use-package session
  :load-path "site-lisp/session"
  :if (not noninteractive)
  :preface
  (defun remove-session-use-package-from-settings ()
    (when (string= (file-name-nondirectory (buffer-file-name)) "settings.el")
      (save-excursion
        (goto-char (point-min))
        (when (re-search-forward "^ '(session-use-package " nil t)
          (delete-region (line-beginning-position)
                         (1+ (line-end-position)))))))

  ;; expanded folded secitons as required
  (defun le::maybe-reveal ()
    (when (and (or (memq major-mode  '(org-mode outline-mode))
                   (and (boundp 'outline-minor-mode)
                        outline-minor-mode))
               (outline-invisible-p))
      (if (eq major-mode 'org-mode)
          (org-reveal)
        (show-subtree))))

  (defvar server-process nil)

  (defun save-information ()
    (with-temp-message "Saving Emacs information..."
      (recentf-cleanup)

      (loop for func in kill-emacs-hook
            unless (memq func '(exit-gnus-on-exit server-force-stop))
            do (funcall func))

      (unless (or noninteractive
                  running-alternate-emacs
                  running-development-emacs
                  (and server-process
                       (eq 'listen (process-status server-process))))
        (server-start))))

  :config
  (add-hook 'before-save-hook 'remove-session-use-package-from-settings)
  (add-hook 'session-after-jump-to-last-change-hook 'le::maybe-reveal)
  (run-with-idle-timer 60 t 'save-information)
  (add-hook 'after-init-hook 'session-initialize t))

(use-package sh-script
  :defer t
  :init
  (defvar sh-script-initialized nil)
  (defun initialize-sh-script ()
    (unless sh-script-initialized
      (setq sh-script-initialized t)
      (info-lookup-add-help :mode 'shell-script-mode
                            :regexp ".*"
                            :doc-spec
                            '(("(bash)Index")))))

  (add-hook 'shell-mode-hook 'initialize-sh-script))

(use-package sh-toggle
  :bind ("C-. C-z" . shell-toggle))

(use-package shackle
  :load-path "site-lisp/shackle"
  :demand t
  :config
  (shackle-mode 1))

(use-package shift-number
  :load-path "site-lisp/shift-number"
  :bind (("C-. +" . shift-number-up)
         ("C-. -" . shift-number-down)))

(use-package slime
  :load-path "site-lisp/slime"
  :commands slime
  :init
  (setq inferior-lisp-program "/Users/johnw/.nix-profile/bin/sbcl"
        slime-contribs '(slime-fancy)))

(use-package smart-mode-line
  :load-path "site-lisp/smart-mode-line"
  :defer 5
  :config
  (sml/setup)
  (sml/apply-theme 'light))

(use-package smart-mode-line-light-powerline-theme
  :disabled t
  :after (powerline smart-mode-line)
  :config
  (sml/apply-theme 'light-powerline))

(use-package smartparens-config
  :load-path "site-lisp/smartparens"
  :commands smartparens-mode)

(use-package smedl-mode
  :load-path "~/bae/xhtml-deliverable/xhtml/mon/smedl/emacs"
  :mode "\\.\\(a4\\)?smedl\\'")

(use-package smerge-mode
  :commands smerge-mode)

(use-package smex
  :load-path "site-lisp/smex"
  :defer 5
  :commands smex)

(use-package sort-words
  :load-path "site-lisp/sort-words"
  :commands sort-words)

(use-package stopwatch
  :bind ("<f8>" . stopwatch))

(use-package sunrise-commander
  :load-path "site-lisp/sunrise-commander"
  :bind (("C-c j" . my-activate-sunrise)
         ("C-c C-j" . sunrise-cd))
  :commands sunrise
  :defines sr-tabs-mode-map
  :preface
  (defun my-activate-sunrise ()
    (interactive)
    (let ((sunrise-exists
           (loop for buf in (buffer-list)
                 when (string-match " (Sunrise)$" (buffer-name buf))
                 return buf)))
      (if sunrise-exists
          (call-interactively 'sunrise)
        (sunrise "~/dl/" "~/Archives/"))))

  :config
  (require 'sunrise-x-modeline)
  (require 'sunrise-x-tree)
  (require 'sunrise-x-tabs)

  (bind-keys :map sr-mode-map
             ("/"     . sr-sticky-isearch-forward)
             ("q"     . sr-history-prev)
             ("z"     . sr-quit)
             ("C-x t" . sr-toggle-truncate-lines)
             ("<backspace>" . sr-scroll-quick-view-down))

  (unbind-key "C-e" sr-mode-map)
  (unbind-key "C-p" sr-tabs-mode-map)
  (unbind-key "C-n" sr-tabs-mode-map)
  (unbind-key "M-<backspace>" sr-term-line-minor-mode-map)

  (bind-key "M-[" #'sr-tabs-prev sr-tabs-mode-map)
  (bind-key "M-]" #'sr-tabs-next sr-tabs-mode-map)

  (defun sr-browse-file (&optional file)
    "Display the selected file with the default appication."
    (interactive)
    (setq file (or file (dired-get-filename)))
    (save-selected-window
      (sr-select-viewer-window)
      (let ((buff (current-buffer))
            (fname (if (file-directory-p file)
                       file
                     (file-name-nondirectory file)))
            (app (cond
                  ((eq system-type 'darwin)       "open %s")
                  ((eq system-type 'windows-nt)   "open %s")
                  (t                              "xdg-open %s"))))
        (start-process-shell-command "open" nil (format app file))
        (unless (eq buff (current-buffer))
          (sr-scrollable-viewer (current-buffer)))
        (message "Opening \"%s\" ..." fname))))

  (defun sr-goto-dir (dir)
    "Change the current directory in the active pane to the given one."
    (interactive (list (progn
                         (require 'lusty-explorer)
                         (lusty-read-directory))))
    (if sr-goto-dir-function
        (funcall sr-goto-dir-function dir)
      (unless (and (eq major-mode 'sr-mode)
                   (sr-equal-dirs dir default-directory))
        (if (and sr-avfs-root
                 (null (posix-string-match "#" dir)))
            (setq dir (replace-regexp-in-string
                       (expand-file-name sr-avfs-root) "" dir)))
        (sr-save-aspect
         (sr-within dir (sr-alternate-buffer (dired dir))))
        (sr-history-push default-directory)
        (sr-beginning-of-buffer)))))

(use-package swiper
  :load-path "site-lisp/ivy/swiper"
  :demand t
  :after ivy
  :bind (("C-. C-s" . swiper)
         ("C-. C-r" . swiper))
  :commands swiper-from-isearch
  :init
  (bind-key "C-." #'swiper-from-isearch isearch-mode-map)
  :config
  (bind-keys :map swiper-map
             ("M-y" . yank)
             ("M-%" . swiper-query-replace)
             ("M-h" . swiper-avy)
             ("M-c" . swiper-mc)))

(use-package tablegen-mode
  :mode "\\.td\\'")

(use-package texinfo
  :defines texinfo-section-list
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

  (add-hook 'texinfo-mode-hook 'my-texinfo-mode-hook)

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

(use-package tramp-sh
  :defer t
  :config
  (add-to-list 'tramp-remote-path "/run/current-system/sw/bin"))

(use-package transpose-mark
  :load-path "site-lisp/transpose-mark"
  :commands (transpose-mark
             transpose-mark-line
             transpose-mark-region))

(use-package treemacs
  :load-path "site-lisp/treemacs"
  :commands treemacs)

(use-package tuareg
  :load-path "site-lisp/tuareg"
  :mode (("\\.ml[4ip]?\\'" . tuareg-mode)
         ("\\.eliomi?\\'"  . tuareg-mode)))

(use-package undo-tree
  :load-path "site-lisp/undo-tree"
  :demand t
  :bind (("C-M-/" . undo-tree-redo))
  :config
  (global-undo-tree-mode))

(use-package vdiff
  :load-path "site-lisp/emacs-vdiff"
  :commands (vdiff-files
             vdiff-files3
             vdiff-buffers
             vdiff-buffers3))

(use-package vimish-fold
  :load-path "site-lisp/vimish-fold"
  :commands (vimish-fold
             vimish-fold-delete
             vimish-fold-delete-all)
  :init
  (bind-keys ("C-. f f" . vimish-fold)
             ("C-. f d" . vimish-fold-delete)
             ("C-. f D" . vimish-fold-delete-all)))

(use-package visual-regexp
  :load-path "site-lisp/visual-regexp"
  :commands (vr/replace
             vr/query-replace)
  :bind (("C-c r" . vr/replace)
         ("C-c %" . vr/query-replace)
         ("C-c C->" . vr/mc-mark))
  :init
  (bind-keys ("C-. v r" . vr/replace)
             ("C-. v %" . vr/query-replace)))

(use-package visual-regexp-steroids
  :disabled t
  :load-path "site-lisp/visual-regexp-steroids"
  :after visual-regexp)

(use-package vline
  :commands vline-mode)

(use-package w3m
  :load-path "site-lisp/emacs-w3m"
  :commands w3m)

(use-package web-mode
  :load-path "site-lisp/web-mode"
  :commands web-mode)

(use-package wgrep
  :load-path "site-lisp/wgrep"
  :defer 5)

(use-package which-key
  :load-path "site-lisp/which-key"
  :demand t
  :diminish which-key-mode
  :config
  (which-key-mode))

(use-package whitespace
  :diminish (global-whitespace-mode
             whitespace-mode
             whitespace-newline-mode)
  :commands (whitespace-buffer
             whitespace-cleanup
             whitespace-mode)
  :defines (whitespace-auto-cleanup
            whitespace-rescan-timer-time
            whitespace-silent)
  :preface
  (defun normalize-file ()
    (interactive)
    (save-excursion
      (goto-char (point-min))
      (whitespace-cleanup)
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
    "Depending on the file, maybe clean up whitespace."
    (when (and (locate-dominating-file default-directory ".clean")
               (not (locate-dominating-file default-directory ".noclean")))
      (add-hook 'write-contents-hooks
                #'(lambda () (ignore (whitespace-cleanup))) nil t)
      (whitespace-cleanup)))

  :init
  (add-hook 'find-file-hooks 'maybe-turn-on-whitespace t)

  :config
  (remove-hook 'find-file-hooks 'whitespace-buffer)
  (remove-hook 'kill-buffer-hook 'whitespace-buffer)

  ;; For some reason, having these in settings.el gets ignored if whitespace
  ;; loads lazily.
  (setq whitespace-auto-cleanup t
        whitespace-line-column 110
        whitespace-rescan-timer-time nil
        whitespace-silent t
        whitespace-style '(face trailing lines space-before-tab empty)))

(use-package winner
  :if (not noninteractive)
  :defer 5
  :bind (("M-N" . winner-redo)
         ("M-P" . winner-undo))
  :config
  (winner-mode 1))

(use-package word-count
  :load-path "site-lisp/word-count-mode"
  :bind ("C-. W" . word-count-mode))

(use-package ws-butler
  :load-path "site-lisp/ws-butler"
  :diminish ws-butler-mode
  :config
  (add-hook 'prog-mode-hook 'ws-butler-mode))

(use-package xray
  :commands (xray-buffer
             xray-faces
             xray-features
             xray-frame
             xray-hooks
             xray-marker
             xray-overlay
             xray-position
             xray-screen
             xray-symbol
             xray-window))

(use-package yaml-mode
  :load-path "site-lisp/yaml-mode"
  :mode "\\.ya?ml\\'")

(use-package yaoddmuse
  :bind (("C-c w f" . yaoddmuse-browse-page-default)
         ("C-c w e" . yaoddmuse-edit-default)
         ("C-c w p" . yaoddmuse-post-library-default)))

(use-package yari
  :load-path "site-lisp/yari-with-buttons"
  :commands yari)

(use-package yasnippet
  :load-path "site-lisp/yasnippet"
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
         ("C-c y a" . yas-reload-all)
         ("C-c y x" . yas-expand))
  :mode ("/\\.emacs\\.d/snippets/" . snippet-mode)
  :config
  (yas-load-directory "~/.emacs.d/snippets/")
  (yas-global-mode 1)
  (bind-key "C-i" #'yas-next-field-or-maybe-expand yas-keymap))

(use-package yasnippet-snippets
  :load-path "site-lisp/yasnippet-snippets"
  :after yasnippet
  :demand t
  :init
  (setq yas-installed-snippets-dir
        "~/.emacs.d/site-lisp/yasnippet-snippets/snippets/"))

(use-package z3-mode
  :load-path "site-lisp/z3-mode"
  :mode "\\.rs\\'"
  :commands z3-mode)

(use-package zencoding-mode
  :load-path "site-lisp/zencoding-mode"
  :commands zencoding-mode
  :init
  (add-hook 'nxml-mode-hook 'zencoding-mode)
  (add-hook 'html-mode-hook 'zencoding-mode)
  (add-hook 'html-mode-hook
            #'(lambda ()
                (bind-key "<return>" #'newline-and-indent html-mode-map)))

  :config
  (defvar zencoding-mode-keymap (make-sparse-keymap))
  (bind-key "C-c C-c" #'zencoding-expand-line zencoding-mode-keymap))

(use-package zoom
  :load-path "site-lisp/zoom"
  :bind ("C-x +" . zoom)
  :config
  (defun size-callback ()
    (cond ((> (frame-pixel-width) 1280) '(90 . 0.75))
          (t                            '(0.5 . 0.5))))

  (custom-set-variables
   '(zoom-size 'size-callback)))

(use-package ztree-diff
  :load-path "site-lisp/ztree"
  :commands ztree-diff)

;;; Finalization

(when window-system
  (let ((elapsed (float-time (time-subtract (current-time)
                                            emacs-start-time))))
    (message "Loading %s...done (%.3fs)" load-file-name elapsed))

  (add-hook 'after-init-hook
            `(lambda ()
               (let ((elapsed
                      (float-time
                       (time-subtract (current-time) emacs-start-time))))
                 (message "Loading %s...done (%.3fs) [after-init]"
                          ,load-file-name elapsed))) t))

;;; init.el ends here
