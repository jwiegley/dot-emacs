(defconst emacs-start-time (current-time))
(unless noninteractive
  (message "Loading %s..." load-file-name))

(setq message-log-max 16384)

(eval-and-compile
  (mapc
   #'(lambda (path)
       (push (expand-file-name path user-emacs-directory) load-path))
   '("site-lisp" "override" "lisp" "lisp/use-package" ""))

  (defsubst nix-lisp-path (part)
    (expand-file-name part "~/.nix-profile/share/emacs/site-lisp"))

  (defun agda-site-lisp ()
    (let ((agda
           (nth 1 (split-string
                   (shell-command-to-string "load-env-agda which agda")
                   "\n"))))
      (and agda
           (expand-file-name
            "../share/x86_64-osx-ghc-7.8.4/Agda-2.4.2.3/emacs-mode"
            (file-name-directory agda))))))

(eval-and-compile
  (defvar use-package-verbose t)
  ;; (defvar use-package-expand-minimally t)
  (eval-after-load 'advice
    `(setq ad-redefinition-action 'accept))
  (require 'cl)
  (require 'use-package))

(require 'bind-key)
(require 'diminish nil t)

;;; Utility macros and functions

;; support textexpander (jww (2015-03-24): check if it's running)
(bind-key "A-v" 'scroll-down)
(bind-key "M-v" 'yank)

(defsubst hook-into-modes (func &rest modes)
  (dolist (mode-hook modes) (add-hook mode-hook func)))

;;; Load customization settings

(defvar running-alternate-emacs nil)
(defvar user-data-directory (expand-file-name "data" user-emacs-directory))

(if (not (string-match (concat "Emacs\\([A-Za-z]+\\).app/Contents/MacOS/")
                       invocation-directory))
    (load (expand-file-name "settings" user-emacs-directory))
  (let ((settings (with-temp-buffer
                    (insert-file-contents
                     (expand-file-name "settings.el" user-emacs-directory))
                    (goto-char (point-min))
                    (read (current-buffer))))
        (suffix (downcase (match-string 1 invocation-directory))))
    (setq running-alternate-emacs t
          user-data-directory
          (replace-regexp-in-string "/data/" (format "/data-%s/" suffix)
                                    user-data-directory))
    (let* ((regexp "/\\.emacs\\.d/data/")
           (replace (format "/.emacs.d/data-%s/" suffix)))
      (dolist (setting settings)
        (let ((value (and (listp setting)
                          (nth 1 (nth 1 setting)))))
          (if (and (stringp value)
                   (string-match regexp value))
              (setcar (nthcdr 1 (nth 1 setting))
                      (replace-regexp-in-string regexp replace value)))))
      (eval settings))))

;;; Enable disabled commands

(put 'downcase-region  'disabled nil)   ; Let downcasing work
(put 'erase-buffer     'disabled nil)
(put 'eval-expression  'disabled nil)   ; Let ESC-ESC work
(put 'narrow-to-page   'disabled nil)   ; Let narrowing work
(put 'narrow-to-region 'disabled nil)   ; Let narrowing work
(put 'set-goal-column  'disabled nil)
(put 'upcase-region    'disabled nil)   ; Let upcasing work

;;; Configure libraries

(eval-and-compile
  (push (expand-file-name "lib" user-emacs-directory) load-path))

(use-package anaphora       :defer t :load-path "lib/anaphora")
(use-package button-lock    :defer t :load-path "lib/button-lock")
(use-package dash           :defer t :load-path "lib/dash-el")
(use-package ctable         :defer t :load-path "lib/emacs-ctable")
(use-package deferred       :defer t :load-path "lib/emacs-deferred")
(use-package epc            :defer t :load-path "lib/emacs-epc")
(use-package web            :defer t :load-path "lib/emacs-web")
(use-package epl            :defer t :load-path "lib/epl")
(use-package f              :defer t :load-path "lib/f-el")
(use-package fame           :defer t)
(use-package fuzzy          :defer t)
(use-package gh             :defer t :load-path "lib/gh-el")
(use-package ht             :defer t :load-path "lib/ht-el")
(use-package let-alist      :defer t)
(use-package logito         :defer t :load-path "lib/logito")
(use-package makey          :defer t :load-path "lib/makey")
(use-package pcache         :defer t :load-path "lib/pcache")
(use-package pkg-info       :defer t :load-path "lib/pkg-info")
(use-package popup          :defer t :load-path "lib/popup-el")
(use-package popwin         :defer t :load-path "lib/popwin-el")
(use-package pos-tip        :defer t :load-path "lib/pos-tip")
(use-package s              :defer t :load-path "lib/s-el")
(use-package working        :defer t)
(use-package xml-rpc        :defer t)

;;; Keybindings

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; jww (2015-03-24): Move all of these into declarations                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Main keymaps for personal bindings are:
;;
;;   C-x <letter>  primary map (has many defaults too)
;;   C-c <letter>  secondary map (not just for mode-specific)
;;   C-. <letter>  tertiary map
;;
;;   M-g <letter>  goto map
;;   M-s <letter>  search map
;;   M-o <letter>  markup map (even if only temporarily)
;;
;;   C-<capital letter>
;;   M-<capital letter>
;;
;;   A-<anything>
;;   M-A-<anything>
;;
;; Single-letter bindings still available:
;;   C- ,'";:?<>|!#$%^&*`~ <tab>
;;   M- ?#

;;; global-map

(autoload 'org-cycle "org" nil t)
(autoload 'hippie-expand "hippie-exp" nil t)
(autoload 'indent-according-to-mode "indent" nil t)

(defun smart-tab (&optional arg)
  (interactive "P")
  (cond
   ((looking-back "^[-+* \t]*")
    (if (eq major-mode 'org-mode)
        (org-cycle arg)
      (indent-according-to-mode)))
   (t
    ;; Hippie also expands yasnippets, due to `yas-hippie-try-expand' in
    ;; `hippie-expand-try-functions-list'.
    (hippie-expand arg))))

(define-key key-translation-map (kbd "A-TAB") (kbd "C-TAB"))

;;; C-

(defvar ctl-period-map)
(define-prefix-command 'ctl-period-map)
(bind-key "C-." 'ctl-period-map)

(bind-key* "<C-return>" 'other-window)

(defun collapse-or-expand ()
  (interactive)
  (if (> (length (window-list)) 1)
      (delete-other-windows)
    (bury-buffer)))

(bind-key "C-z" 'delete-other-windows)

;;; M-

(defadvice async-shell-command (before uniqify-running-shell-command activate)
  (let ((buf (get-buffer "*Async Shell Command*")))
    (if buf
        (let ((proc (get-buffer-process buf)))
          (if (and proc (eq 'run (process-status proc)))
              (with-current-buffer buf
                (rename-uniquely)))))))

(bind-key "M-!" 'async-shell-command)
(bind-key "M-'" 'insert-pair)
(bind-key "M-\"" 'insert-pair)

(defun align-code (beg end &optional arg)
  (interactive "rP")
  (if (null arg)
      (align beg end)
    (let ((end-mark (copy-marker end)))
      (indent-region beg end-mark nil)
      (align beg end-mark))))

(bind-key "M-[" 'align-code)
(bind-key "M-`" 'other-frame)

(bind-key "M-j" 'delete-indentation-forward)
(bind-key "M-J" 'delete-indentation)

(bind-key "M-W" 'mark-word)

(defun mark-line (&optional arg)
  (interactive "p")
  (beginning-of-line)
  (let ((here (point)))
    (dotimes (i arg)
      (end-of-line))
    (set-mark (point))
    (goto-char here)))

(bind-key "M-L" 'mark-line)

(defun mark-sentence (&optional arg)
  (interactive "P")
  (backward-sentence)
  (mark-end-of-sentence arg))

(bind-key "M-S" 'mark-sentence)
(bind-key "M-X" 'mark-sexp)
(bind-key "M-D" 'mark-defun)

(bind-key "M-g c" 'goto-char)
(bind-key "M-g l" 'goto-line)

(defun delete-indentation-forward ()
  (interactive)
  (delete-indentation t))

;;; M-C-

(bind-key "<C-M-backspace>" 'backward-kill-sexp)

;;; ctl-x-map

;;; C-x

(bind-key "C-x d" 'delete-whitespace-rectangle)
(bind-key "C-x F" 'set-fill-column)
(bind-key "C-x t" 'toggle-truncate-lines)

(defun delete-current-buffer-file ()
  "Delete the current buffer and the file connected with it"
  (interactive)
  (let ((filename (buffer-file-name))
        (buffer (current-buffer))
        (name (buffer-name)))
    (if (not (and filename (file-exists-p filename)))
        (kill-buffer buffer)
      (when (yes-or-no-p "Are you sure, want to remove this file? ")
        (delete-file filename)
        (kill-buffer buffer)
        (message "File '%s' successfully removed" filename)))))

(bind-key "C-x K" 'delete-current-buffer-file)

;;; C-x C-

(defun duplicate-line ()
  "Duplicate the line containing point."
  (interactive)
  (save-excursion
    (let (line-text)
      (goto-char (line-beginning-position))
      (let ((beg (point)))
        (goto-char (line-end-position))
        (setq line-text (buffer-substring beg (point))))
      (if (eobp)
          (insert ?\n)
        (forward-line))
      (open-line 1)
      (insert line-text))))

(bind-key "C-x C-d" 'duplicate-line)
(bind-key "C-x C-e" 'pp-eval-last-sexp)
(bind-key "C-x C-n" 'next-line)

(defun find-alternate-file-with-sudo ()
  (interactive)
  (find-alternate-file (concat "/sudo::" (buffer-file-name))))

(bind-key "C-x C-v" 'find-alternate-file-with-sudo)

;;; C-x M-

(bind-key "C-x M-n" 'set-goal-column)

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
      (funcall fun nil))
    (goto-char (+ end 2))))

(bind-key "C-x M-q" 'refill-paragraph)

;;; mode-specific-map

;;; C-c

(bind-key "C-c <tab>" 'ff-find-other-file)
(bind-key "C-c SPC" 'just-one-space)

(defmacro recursive-edit-preserving-window-config (body)
  "*Return a command that enters a recursive edit after executing BODY.
Upon exiting the recursive edit (with\\[exit-recursive-edit] (exit)
or \\[abort-recursive-edit] (abort)), restore window configuration
in current frame.
Inspired by Erik Naggum's `recursive-edit-with-single-window'."
  `(lambda ()
     "See the documentation for `recursive-edit-preserving-window-config'."
     (interactive)
     (save-window-excursion
       ,body
       (recursive-edit))))

(bind-key "C-c 0"
  (recursive-edit-preserving-window-config (delete-window)))
(bind-key "C-c 1"
  (recursive-edit-preserving-window-config
   (if (one-window-p 'ignore-minibuffer)
       (error "Current window is the only window in its frame")
     (delete-other-windows))))

(defun delete-current-line (&optional arg)
  (interactive "p")
  (let ((here (point)))
    (beginning-of-line)
    (kill-line arg)
    (goto-char here)))

(bind-key "C-c d" 'delete-current-line)

(defun do-eval-buffer ()
  (interactive)
  (call-interactively 'eval-buffer)
  (message "Buffer has been evaluated"))

(defun do-eval-region ()
  (interactive)
  (call-interactively 'eval-region)
  (message "Region has been evaluated"))

(bind-keys :prefix-map my-lisp-devel-map
           :prefix "C-c e"
           ("E" . elint-current-buffer)
           ("b" . do-eval-buffer)
           ("c" . cancel-debug-on-entry)
           ("d" . debug-on-entry)
           ("e" . toggle-debug-on-error)
           ("f" . emacs-lisp-byte-compile-and-load)
           ("j" . emacs-lisp-mode)
           ("l" . find-library)
           ("r" . do-eval-region)
           ("s" . scratch)
           ("z" . byte-recompile-directory))

(bind-key "C-c f" 'flush-lines)

(defun goto-line-with-feedback ()
  "Show line numbers temporarily, while prompting for the line number input"
  (interactive)
  (unwind-protect
      (progn
        (linum-mode 1)
        (goto-char (point-min))
        (forward-line (read-number "Goto line: ")))
    (linum-mode -1)))

(bind-key "C-c g" 'goto-line)
(global-set-key [remap goto-line] 'goto-line-with-feedback)

(bind-key "C-c k" 'keep-lines)

(eval-when-compile
  (defvar emacs-min-height)
  (defvar emacs-min-width))

(defvar display-name
  (let ((width (display-pixel-width)))
    (cond ((>= width 2560) 'retina-imac)
          ((= width 1440) 'retina-macbook-pro))))

(defvar emacs-min-top 23)
(defvar emacs-min-left
  (cond ((eq display-name 'retina-imac) 975)
        (t 521)))
(defvar emacs-min-height
  (cond ((eq display-name 'retina-imac) 55)
        (t 44)))
(defvar emacs-min-width 100)

(if running-alternate-emacs
    (setq emacs-min-top 22
          emacs-min-left 5
          emacs-min-height 57
          emacs-min-width 90))

(defvar emacs-min-font
  (cond
   ((eq display-name 'retina-imac)
    (if running-alternate-emacs
        "-*-Myriad Pro-normal-normal-normal-*-20-*-*-*-p-0-iso10646-1"
      "-*-Source Code Pro-normal-normal-normal-*-20-*-*-*-m-0-iso10646-1"))
   ((string= system-name "ubuntu")
    "-*-Source Code Pro-normal-normal-normal-*-20-*-*-*-m-0-iso10646-1")
   (t
    (if running-alternate-emacs
        "-*-Myriad Pro-normal-normal-normal-*-17-*-*-*-p-0-iso10646-1"
      "-*-Source Code Pro-normal-normal-normal-*-15-*-*-*-m-0-iso10646-1"))))

(let ((frame-alist
       (list (cons 'top    emacs-min-top)
             (cons 'left   emacs-min-left)
             (cons 'height emacs-min-height)
             (cons 'width  emacs-min-width)
             (cons 'font   emacs-min-font))))
  (setq initial-frame-alist frame-alist))

(defun emacs-min ()
  (interactive)

  (set-frame-parameter (selected-frame) 'fullscreen nil)
  (set-frame-parameter (selected-frame) 'vertical-scroll-bars nil)
  (set-frame-parameter (selected-frame) 'horizontal-scroll-bars nil)

  (set-frame-parameter (selected-frame) 'top emacs-min-top)
  (set-frame-parameter (selected-frame) 'left emacs-min-left)
  (set-frame-parameter (selected-frame) 'height emacs-min-height)
  (set-frame-parameter (selected-frame) 'width emacs-min-width)

  (set-frame-font emacs-min-font))

(if window-system
    (add-hook 'after-init-hook 'emacs-min))

(defun emacs-max ()
  (interactive)
  (set-frame-parameter (selected-frame) 'fullscreen 'fullboth)
  (set-frame-parameter (selected-frame) 'vertical-scroll-bars nil)
  (set-frame-parameter (selected-frame) 'horizontal-scroll-bars nil))

(defun emacs-toggle-size ()
  (interactive)
  (if (> (cdr (assq 'width (frame-parameters))) 100)
      (emacs-min)
    (emacs-max)))

(bind-key "C-c m" 'emacs-toggle-size)

(defcustom user-initials nil
  "*Initials of this user."
  :set
  #'(lambda (symbol value)
      (if (fboundp 'font-lock-add-keywords)
          (mapc
           #'(lambda (mode)
               (font-lock-add-keywords
                mode (list (list (concat "\\<\\(" value " [^:\n]+\\):")
                                 1 font-lock-warning-face t))))
           '(c-mode c++-mode emacs-lisp-mode lisp-mode
                    python-mode perl-mode java-mode groovy-mode
                    haskell-mode literate-haskell-mode)))
      (set symbol value))
  :type 'string
  :group 'mail)

(defun insert-user-timestamp ()
  "Insert a quick timestamp using the value of `user-initials'."
  (interactive)
  (insert (format "%s (%s): " user-initials
                  (format-time-string "%Y-%m-%d" (current-time)))))

(bind-key "C-c n" 'insert-user-timestamp)
(bind-key "C-c o" 'customize-option)
(bind-key "C-c O" 'customize-group)
(bind-key "C-c F" 'customize-face)

(bind-key "C-c q" 'fill-region)
(bind-key "C-c r" 'replace-regexp)
(bind-key "C-c s" 'replace-string)
(bind-key "C-c u" 'rename-uniquely)

(bind-key "C-c v" 'ffap)

(defun view-clipboard ()
  (interactive)
  (delete-other-windows)
  (switch-to-buffer "*Clipboard*")
  (let ((inhibit-read-only t))
    (erase-buffer)
    (clipboard-yank)
    (goto-char (point-min))))

(bind-key "C-c V" 'view-clipboard)
(bind-key "C-c z" 'clean-buffer-list)

(bind-key "C-c [" 'align-regexp)
(bind-key "C-c =" 'count-matches)
(bind-key "C-c ;" 'comment-or-uncomment-region)

;;; C-c C-

(defun delete-to-end-of-buffer ()
  (interactive)
  (kill-region (point) (point-max)))

(bind-key "C-c C-z" 'delete-to-end-of-buffer)

;;; C-c M-

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

(bind-key "C-c M-q" 'unfill-paragraph)

(defun unfill-region (beg end)
  (interactive "r")
  (setq end (copy-marker end))
  (save-excursion
    (goto-char beg)
    (while (< (point) end)
      (unfill-paragraph 1)
      (forward-paragraph))))

;;; ctl-period-map

;;; C-.

(bind-key "C-. m" 'kmacro-keymap)

(bind-key "C-. C-i" 'indent-rigidly)

;;; help-map

(defvar lisp-find-map)
(define-prefix-command 'lisp-find-map)

(bind-key "C-h e" 'lisp-find-map)

;;; C-h e

(bind-key "C-h e c" 'finder-commentary)
(bind-key "C-h e e" 'view-echo-area-messages)
(bind-key "C-h e f" 'find-function)
(bind-key "C-h e F" 'find-face-definition)

(defun my-switch-in-other-buffer (buf)
  (when buf
    (split-window-vertically)
    (switch-to-buffer-other-window buf)))

(defun my-describe-symbol  (symbol &optional mode)
  (interactive
   (info-lookup-interactive-arguments 'symbol current-prefix-arg))
  (let (info-buf find-buf desc-buf cust-buf)
    (save-window-excursion
      (ignore-errors
        (info-lookup-symbol symbol mode)
        (setq info-buf (get-buffer "*info*")))
      (let ((sym (intern-soft symbol)))
        (when sym
          (if (functionp sym)
              (progn
                (find-function sym)
                (setq find-buf (current-buffer))
                (describe-function sym)
                (setq desc-buf (get-buffer "*Help*")))
            (find-variable sym)
            (setq find-buf (current-buffer))
            (describe-variable sym)
            (setq desc-buf (get-buffer "*Help*"))
            ;;(customize-variable sym)
            ;;(setq cust-buf (current-buffer))
            ))))

    (delete-other-windows)

    (switch-to-buffer find-buf)
    (my-switch-in-other-buffer desc-buf)
    (my-switch-in-other-buffer info-buf)
    ;;(switch-in-other-buffer cust-buf)
    (balance-windows)))

(bind-key "C-h e d" 'my-describe-symbol)
(bind-key "C-h e i" 'info-apropos)
(bind-key "C-h e k" 'find-function-on-key)
(bind-key "C-h e l" 'find-library)

(defvar lisp-modes '(emacs-lisp-mode
                     inferior-emacs-lisp-mode
                     ielm-mode
                     lisp-mode
                     inferior-lisp-mode
                     lisp-interaction-mode
                     slime-repl-mode))

(defvar lisp-mode-hooks
  (mapcar (function
           (lambda (mode)
             (intern
              (concat (symbol-name mode) "-hook"))))
          lisp-modes))

(defun scratch ()
  (interactive)
  (let ((current-mode major-mode))
    (switch-to-buffer-other-window (get-buffer-create "*scratch*"))
    (goto-char (point-min))
    (when (looking-at ";")
      (forward-line 4)
      (delete-region (point-min) (point)))
    (goto-char (point-max))
    (if (memq current-mode lisp-modes)
        (funcall current-mode))))

(bind-key "C-h e s" 'scratch)
(bind-key "C-h e v" 'find-variable)
(bind-key "C-h e V" 'apropos-value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; jww (2015-03-24): Move all of the above into declarations                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Packages

(use-package ggtags
  :load-path "site-lisp/ggtags"
  :commands ggtags-mode
  :diminish ggtags-mode)

(use-package cc-mode
  :load-path "override/cc-mode"
  :mode (("\\.h\\(h?\\|xx\\|pp\\)\\'" . c++-mode)
         ("\\.m\\'"                   . c-mode)
         ("\\.mm\\'"                  . c++-mode))
  :preface
  (defun my-paste-as-check ()
    (interactive)
    (save-excursion
      (insert "/*\n")
      (let ((beg (point)) end)
        (yank)
        (setq end (point-marker))
        (goto-char beg)
        (while (< (point) end)
          (forward-char 2)
          (insert "CHECK: ")
          (forward-line 1)))
      (insert "*/\n")))

  ;; (defun my-c-indent-or-complete ()
  ;;   (interactive)
  ;;   (let ((class (syntax-class (syntax-after (1- (point))))))
  ;;     (if (or (bolp) (and (/= 2 class)
  ;;                         (/= 3 class)))
  ;;         (call-interactively 'indent-according-to-mode)
  ;;       (call-interactively 'auto-complete))))

  (defvar printf-index 0)

  (defun insert-counting-printf (arg)
    (interactive "P")
    (if arg
        (setq printf-index 0))
    (if t
        (insert (format "std::cerr << \"step %d..\" << std::endl;\n"
                        (setq printf-index (1+ printf-index))))
      (insert (format "printf(\"step %d..\\n\");\n"
                      (setq printf-index (1+ printf-index)))))
    (forward-line -1)
    (indent-according-to-mode)
    (forward-line))

  (defun my-c-mode-common-hook ()
    (abbrev-mode 1)
    (ggtags-mode 1)
    (eldoc-mode 1)
    (hs-minor-mode 1)
    (hide-ifdef-mode 1)
    ;; (whitespace-mode 1)
    (which-function-mode 1)
    (company-mode 1)
    (bug-reference-prog-mode 1)

    (diminish 'hs-minor-mode)
    (diminish 'hide-ifdef-mode)

    ;; (bind-key "C-c p" 'insert-counting-printf c-mode-base-map)

    ;;(doxymacs-mode 1)
    ;;(doxymacs-font-lock)

    (bind-key "<return>" 'newline-and-indent c-mode-base-map)

    (unbind-key "M-j" c-mode-base-map)
    (bind-key "C-c C-i" 'c-includes-current-file c-mode-base-map)
    (bind-key "C-c C-y" 'my-paste-as-check c-mode-base-map)

    (set (make-local-variable 'parens-require-spaces) nil)
    (setq indicate-empty-lines t)
    (setq fill-column 72)

    (bind-key "M-q" 'c-fill-paragraph c-mode-base-map)

    (let ((bufname (buffer-file-name)))
      (when bufname
        (cond
         ((string-match "/ledger/" bufname)
          (c-set-style "ledger"))
         ((string-match "/ansi/" bufname)
          (c-set-style "ti")
          (substitute-key-definition 'fill-paragraph 'ti-refill-comment
                                     c-mode-base-map global-map)
          (bind-key "M-q" 'ti-refill-comment c-mode-base-map))
         ((string-match "/edg/" bufname)
          (c-set-style "edg"))
         (t
          (c-set-style "clang")))))

    (font-lock-add-keywords 'c++-mode '(("\\<\\(assert\\|DEBUG\\)("
                                         1 font-lock-warning-face t))))

  :config
  (add-hook 'c-mode-common-hook 'my-c-mode-common-hook)

  (setq c-syntactic-indentation nil)

  (bind-key "#" 'self-insert-command c-mode-base-map)
  (bind-key "{" 'self-insert-command c-mode-base-map)
  (bind-key "}" 'self-insert-command c-mode-base-map)
  (bind-key "/" 'self-insert-command c-mode-base-map)
  (bind-key "*" 'self-insert-command c-mode-base-map)
  (bind-key ";" 'self-insert-command c-mode-base-map)
  (bind-key "," 'self-insert-command c-mode-base-map)
  (bind-key ":" 'self-insert-command c-mode-base-map)
  (bind-key "(" 'self-insert-command c-mode-base-map)
  (bind-key ")" 'self-insert-command c-mode-base-map)
  (bind-key "<" 'self-insert-command c++-mode-map)
  (bind-key ">" 'self-insert-command c++-mode-map)

  (add-to-list 'c-style-alist
               '("ti"
                 (indent-tabs-mode . nil)
                 (c-basic-offset . 3)
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
                     (arglist-intro . c-lineup-arglist-intro-after-paren)
                     (arglist-close . c-lineup-arglist)
                     (inline-open . 0)
                     (brace-list-open . 0)
                     (topmost-intro-cont
                      . (first c-lineup-topmost-intro-cont
                               c-lineup-gnu-DEFUN-intro-cont))))
                 (c-special-indent-hook . c-gnu-impose-minimum)
                 (c-block-comment-prefix . "")))

  (add-to-list 'c-style-alist
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

  (add-to-list 'c-style-alist
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

  (add-to-list 'c-style-alist
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
                 (c-block-comment-prefix . "")))

  (defun opencl ()
    (interactive)
    (find-file "~/src/ansi/opencl.c")
    (find-file-noselect "~/Contracts/TI/bugslayer/cl_0603/cl_0603.c")
    (find-file-noselect "~/Contracts/TI/bugslayer")
    (magit-status "~/src/ansi")
    (gud-gdb "gdb --fullname ~/Contracts/TI/bin/c60/acpia6x"))

  (defun ti-refill-comment ()
    (interactive)
    (let ((here (point)))
      (goto-char (line-beginning-position))
      (let ((begin (point)) end
            (marker ?-) (marker-re "\\(-----\\|\\*\\*\\*\\*\\*\\)")
            (leader-width 0))
        (unless (looking-at "[ \t]*/\\*[-* ]")
          (search-backward "/*")
          (goto-char (line-beginning-position)))
        (unless (looking-at "[ \t]*/\\*[-* ]")
          (error "Not in a comment"))
        (while (and (looking-at "\\([ \t]*\\)/\\* ")
                    (setq leader-width (length (match-string 1)))
                    (not (looking-at (concat "[ \t]*/\\*" marker-re))))
          (forward-line -1)
          (setq begin (point)))
        (when (looking-at (concat "[^\n]+?" marker-re "\\*/[ \t]*$"))
          (setq marker (if (string= (match-string 1) "-----") ?- ?*))
          (forward-line))
        (while (and (looking-at "[^\n]+?\\*/[ \t]*$")
                    (not (looking-at (concat "[^\n]+?" marker-re
                                             "\\*/[ \t]*$"))))
          (forward-line))
        (when (looking-at (concat "[^\n]+?" marker-re "\\*/[ \t]*$"))
          (forward-line))
        (setq end (point))
        (let ((comment (buffer-substring-no-properties begin end)))
          (with-temp-buffer
            (insert comment)
            (goto-char (point-min))
            (flush-lines (concat "^[ \t]*/\\*" marker-re "[-*]+\\*/[ \t]*$"))
            (goto-char (point-min))
            (while (re-search-forward "^[ \t]*/\\* ?" nil t)
              (goto-char (match-beginning 0))
              (delete-region (match-beginning 0) (match-end 0)))
            (goto-char (point-min))
            (while (re-search-forward "[ \t]*\\*/[ \t]*$" nil t)
              (goto-char (match-beginning 0))
              (delete-region (match-beginning 0) (match-end 0)))
            (goto-char (point-min)) (delete-trailing-whitespace)
            (goto-char (point-min)) (flush-lines "^$")
            (set-fill-column (- 80      ; width of the text
                                6       ; width of "/*  */"
                                leader-width))
            (goto-char (point-min)) (fill-paragraph nil)
            (goto-char (point-min))
            (while (not (eobp))
              (insert (make-string leader-width ? ) "/* ")
              (goto-char (line-end-position))
              (insert (make-string (- 80 3 (current-column)) ? ) " */")
              (forward-line))
            (goto-char (point-min))
            (insert (make-string leader-width ? )
                    "/*" (make-string (- 80 4 leader-width) marker) "*/\n")
            (goto-char (point-max))
            (insert (make-string leader-width ? )
                    "/*" (make-string (- 80 4 leader-width) marker) "*/\n")
            (setq comment (buffer-string)))
          (goto-char begin)
          (delete-region begin end)
          (insert comment)))
      (goto-char here))))

(use-package abbrev
  :disabled t
  :commands abbrev-mode
  :diminish abbrev-mode
  :init
  (hook-into-modes #'abbrev-mode 'text-mode-hook)

  :config
  (if (file-exists-p abbrev-file-name)
      (quietly-read-abbrev-file))

  (add-hook 'expand-load-hook
            (lambda ()
              (add-hook 'expand-expand-hook 'indent-according-to-mode)
              (add-hook 'expand-jump-hook 'indent-according-to-mode))))

(use-package ace-jump-mode
  :load-path "site-lisp/ace-jump-mode"
  :bind ("M-h" . ace-jump-mode)
  :config
  (setq ace-jump-mode-submode-list
        '(ace-jump-char-mode
          ace-jump-word-mode
          ace-jump-line-mode)))

(use-package ace-isearch
  :load-path "site-lisp/ace-isearch"
  :disabled t
  :config
  (global-ace-isearch-mode 1))

(use-package ag
  :load-path "site-lisp/ag-el"
  :commands (ag ag-regexp)
  :init
  (use-package helm-ag
    :load-path "site-lisp/emacs-helm-ag"
    :commands helm-ag))

(use-package agda2-mode
  :mode "\\.agda\\'"
  :load-path (lambda () (list (agda-site-lisp)))
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
  (use-package agda-input)
  (bind-key "C-c C-i" 'agda2-insert-helper-function agda2-mode-map)

  (defun char-mapping (key char)
    (bind-key key `(lambda () (interactive) (insert ,char))))

  (char-mapping "A-G" "Γ")
  (char-mapping "A-l" "λ x → ")
  (char-mapping "A-:" " ∷ ")
  (char-mapping "A-r" " → ")
  (char-mapping "A-~" " ≅ ")
  (char-mapping "A-=" " ≡ "))

(use-package alert
  :load-path "lisp/alert"
  :commands alert)

(use-package allout
  :disabled t
  :diminish allout-mode
  :commands allout-mode
  :config
  (defvar allout-unprefixed-keybindings nil)

  (defun my-allout-mode-hook ()
    (dolist (mapping '((?b . allout-hide-bodies)
                       (?c . allout-hide-current-entry)
                       (?l . allout-hide-current-leaves)
                       (?i . allout-show-current-branches)
                       (?e . allout-show-entry)
                       (?o . allout-show-to-offshoot)))
      (eval `(bind-key ,(concat (format-kbd-macro allout-command-prefix)
                                " " (char-to-string (car mapping)))
                       (quote ,(cdr mapping))
                       allout-mode-map)))

    (if (memq major-mode lisp-modes)
        (unbind-key "C-k" allout-mode-map)))

  (add-hook 'allout-mode-hook 'my-allout-mode-hook))

(use-package archive-region
  :disabled t
  :bind ("C-w" . kill-region-or-archive-region))

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

(use-package tex-site
  :load-path "~/.nix-profile/share/emacs/site-lisp/elpa/auctex-11.87.7/"
  :defines (latex-help-cmd-alist latex-help-file)
  :mode ("\\.tex\\'" . TeX-latex-mode)
  :init
  (load "auctex-autoloads")

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

  (use-package latex-mode
    :defer t
    :config
    (use-package preview)
    (use-package ac-math)

    (defun ac-latex-mode-setup ()
      (nconc ac-sources
             '(ac-source-math-unicode ac-source-math-latex
                                      ac-source-latex-commands)))

    (add-to-list 'ac-modes 'latex-mode)
    (add-hook 'latex-mode-hook 'ac-latex-mode-setup)

    (info-lookup-add-help :mode 'latex-mode
                          :regexp ".*"
                          :parse-rule "\\\\?[a-zA-Z]+\\|\\\\[^a-zA-Z]"
                          :doc-spec '(("(latex2e)Concept Index" )
                                      ("(latex2e)Command Index")))))

(use-package auto-complete-config
  :disabled t
  :load-path "site-lisp/auto-complete"
  :diminish auto-complete-mode
  :init
  (use-package pos-tip)
  (ac-config-default)

  :config
  (ac-set-trigger-key "<backtab>")
  (setq ac-use-menu-map t)

  (bind-key "A-M-?" 'ac-last-help)
  (unbind-key "C-s" ac-completing-map))

(use-package autopair
  :disabled t
  :load-path "site-lisp/autopair"
  :commands autopair-mode
  :diminish autopair-mode
  :init
  (hook-into-modes #'autopair-mode
                   'c-mode-common-hook
                   'text-mode-hook
                   'ruby-mode-hook
                   'python-mode-hook
                   'sh-mode-hook))

(use-package autorevert
  :commands auto-revert-mode
  :diminish auto-revert-mode
  :init
  (add-hook 'find-file-hook #'(lambda () (auto-revert-mode 1))))

(use-package backup-each-save
  :commands backup-each-save
  :preface
  (defun show-backups ()
    (interactive)
    (require 'find-dired)
    (let* ((file (make-backup-file-name (buffer-file-name)))
           (dir (file-name-directory file))
           (args (concat "-iname '" (file-name-nondirectory file)
                         ".~*~'"))
           (dired-buffers dired-buffers)
           (find-ls-option '("-print0 | xargs -0 ls -lta" . "-lta")))
      ;; Check that it's really a directory.
      (or (file-directory-p dir)
          (error "Backup directory does not exist: %s" dir))
      (with-current-buffer (get-buffer-create "*Backups*")
        (let ((find (get-buffer-process (current-buffer))))
          (when find
            (if (or (not (eq (process-status find) 'run))
                    (yes-or-no-p "A `find' process is running; kill it? "))
                (condition-case nil
                    (progn
                      (interrupt-process find)
                      (sit-for 1)
                      (delete-process find))
                  (error nil))
              (error "Cannot have two processes in `%s' at once"
                     (buffer-name)))))

        (widen)
        (kill-all-local-variables)
        (setq buffer-read-only nil)
        (erase-buffer)
        (setq default-directory dir
              args (concat
                    find-program " . "
                    (if (string= args "")
                        ""
                      (concat
                       (shell-quote-argument "(")
                       " " args " "
                       (shell-quote-argument ")")
                       " "))
                    (if (string-match "\\`\\(.*\\) {} \\(\\\\;\\|+\\)\\'"
                                      (car find-ls-option))
                        (format "%s %s %s"
                                (match-string 1 (car find-ls-option))
                                (shell-quote-argument "{}")
                                find-exec-terminator)
                      (car find-ls-option))))
        ;; Start the find process.
        (message "Looking for backup files...")
        (shell-command (concat args "&") (current-buffer))
        ;; The next statement will bomb in classic dired (no optional arg
        ;; allowed)
        (dired-mode dir (cdr find-ls-option))
        (let ((map (make-sparse-keymap)))
          (set-keymap-parent map (current-local-map))
          (define-key map "\C-c\C-k" 'kill-find)
          (use-local-map map))
        (make-local-variable 'dired-sort-inhibit)
        (setq dired-sort-inhibit t)
        (set (make-local-variable 'revert-buffer-function)
             `(lambda (ignore-auto noconfirm)
                (find-dired ,dir ,find-args)))
        ;; Set subdir-alist so that Tree Dired will work:
        (if (fboundp 'dired-simple-subdir-alist)
            ;; will work even with nested dired format (dired-nstd.el,v 1.15
            ;; and later)
            (dired-simple-subdir-alist)
          ;; else we have an ancient tree dired (or classic dired, where
          ;; this does no harm)
          (set (make-local-variable 'dired-subdir-alist)
               (list (cons default-directory (point-min-marker)))))
        (set (make-local-variable 'dired-subdir-switches)
             find-ls-subdir-switches)
        (setq buffer-read-only nil)
        ;; Subdir headlerline must come first because the first marker in
        ;; subdir-alist points there.
        (insert "  " dir ":\n")
        ;; Make second line a ``find'' line in analogy to the ``total'' or
        ;; ``wildcard'' line.
        (insert "  " args "\n")
        (setq buffer-read-only t)
        (let ((proc (get-buffer-process (current-buffer))))
          (set-process-filter proc (function find-dired-filter))
          (set-process-sentinel proc (function find-dired-sentinel))
          ;; Initialize the process marker; it is used by the filter.
          (move-marker (process-mark proc) 1 (current-buffer)))
        (setq mode-line-process '(":%s")))))

  (bind-key "C-x ~" 'show-backups)

  :init
  (defun my-make-backup-file-name (file)
    (make-backup-file-name-1 (file-truename file)))

  (add-hook 'after-save-hook 'backup-each-save)

  :config
  (defun backup-each-save-filter (filename)
    (not (string-match
          (concat "\\(^/tmp\\|\\.emacs\\.d/data\\(-alt\\)?/"
                  "\\|\\.newsrc\\(\\.eld\\)?\\|"
                  "\\(archive/sent/\\|recentf\\`\\)\\)")
          filename)))

  (setq backup-each-save-filter-function 'backup-each-save-filter)

  (defun my-dont-backup-files-p (filename)
    (unless (string-match filename "\\(archive/sent/\\|recentf\\`\\)")
      (normal-backup-enable-predicate filename)))

  (setq backup-enable-predicate 'my-dont-backup-files-p))

(use-package bbdb-com
  :load-path "override/bbdb/lisp"
  :commands bbdb-create
  :bind ("M-B" . bbdb))

(use-package bm
  :disabled t
  :load-path "site-lisp/bm"
  :init
  (defvar ctl-period-breadcrumb-map)
  (define-prefix-command 'ctl-period-breadcrumb-map)
  (bind-key "C-. c" 'ctl-period-breadcrumb-map)

  :bind (("C-. c b" . bm-last-in-previous-buffer)
         ("C-. c f" . bm-first-in-next-buffer)
         ("C-. c g" . bm-previous)
         ("C-. c l" . bm-show-all)
         ("C-. c c" . bm-toggle)
         ("C-. c m" . bm-toggle)
         ("C-. c n" . bm-next)
         ("C-. c p" . bm-previous)))

(use-package bookmark
  :load-path "site-lisp/bookmark-plus"
  :defer 10
  :config
  (use-package bookmark+))

(use-package browse-kill-ring+
  :defer 10
  :commands browse-kill-ring)

(use-package cmake-mode
  :mode (("CMakeLists\\.txt\\'" . cmake-mode)
         ("\\.cmake\\'"         . cmake-mode)))

(use-package color-moccur
  :commands (isearch-moccur isearch-all)
  :bind ("M-s O" . moccur)
  :init
  (bind-key "M-o" 'isearch-moccur isearch-mode-map)
  (bind-key "M-O" 'isearch-moccur-all isearch-mode-map)
  :config
  (use-package moccur-edit))

(use-package company
  :load-path "site-lisp/company-mode"
  :diminish company-mode
  :commands company-mode
  :config
  ;; From https://github.com/company-mode/company-mode/issues/87
  ;; See also https://github.com/company-mode/company-mode/issues/123
  (defadvice company-pseudo-tooltip-unless-just-one-frontend
      (around only-show-tooltip-when-invoked activate)
    (when (company-explicit-action-p)
      ad-do-it))

  (use-package helm-company
    :load-path "site-lisp/helm-company"
    :disabled t))

(use-package compile
  :bind (("C-c c" . compile)
         ("M-O"   . show-compilation))
  :preface
  (defun show-compilation ()
    (interactive)
    (let ((compile-buf
           (catch 'found
             (dolist (buf (buffer-list))
               (if (string-match "\\*compilation\\*" (buffer-name buf))
                   (throw 'found buf))))))
      (if compile-buf
          (switch-to-buffer-other-window compile-buf)
        (call-interactively 'compile))))

  (defun compilation-ansi-color-process-output ()
    (ansi-color-process-output nil)
    (set (make-local-variable 'comint-last-output-start)
         (point-marker)))

  :config
  (add-hook 'compilation-filter-hook #'compilation-ansi-color-process-output))

(use-package copy-code
  :disabled t
  :bind ("A-M-W" . copy-code-as-rtf))

(use-package crosshairs
  :bind ("M-o c" . crosshairs-mode))

(use-package css-mode
  :mode "\\.css\\'")

(use-package cursor-chg
  :defer 10
  :commands change-cursor-mode
  :config
  (change-cursor-mode 1)
  (toggle-cursor-type-when-idle 1))

(use-package debbugs-gnu
  :disabled t
  :load-path "site-lisp/debbugs"
  :commands (debbugs-gnu debbugs-gnu-search))

(use-package dedicated
  :bind ("C-. D" . dedicated-mode))

(use-package diff-mode
  :commands diff-mode
  :config
  (use-package diff-mode-))

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

  :config
  (use-package dired-x)
  (use-package dired+
    :config
    (unbind-key "M-s f" dired-mode-map))

  (bind-key "l" 'dired-up-directory dired-mode-map)

  (defun my-dired-switch-window ()
    (interactive)
    (if (eq major-mode 'sr-mode)
        (call-interactively #'sr-change-window)
      (call-interactively #'other-window)))

  (bind-key "<tab>" 'my-dired-switch-window dired-mode-map)

  (bind-key "M-!" 'async-shell-command dired-mode-map)
  (unbind-key "M-G" dired-mode-map)

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

(use-package doxymacs
  :disabled t
  :load-path "site-lisp/doxymacs/lisp/")

(use-package eclimd
  :load-path "site-lisp/emacs-eclim"
  :commands start-eclimd
  :config
  (use-package eclim
    :defer t
    :config
    (global-eclim-mode)
    (use-package company-emacs-eclim
      :requires company
      :config
      (company-emacs-eclim-setup))))

(use-package edebug
  :defer t
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
  :init
  (defvar ctl-period-equals-map)
  (define-prefix-command 'ctl-period-equals-map)
  (bind-key "C-. =" 'ctl-period-equals-map)

  :bind (("C-. = b" . ediff-buffers)
         ("C-. = B" . ediff-buffers3)
         ("C-. = c" . compare-windows)
         ("C-. = =" . ediff-files)
         ("C-. = f" . ediff-files)
         ("C-. = F" . ediff-files3)
         ("C-. = r" . ediff-revision)
         ("C-. = p" . ediff-patch-file)
         ("C-. = P" . ediff-patch-buffer)
         ("C-. = l" . ediff-regions-linewise)
         ("C-. = w" . ediff-regions-wordwise))

  :config
  (use-package ediff-keep))

(use-package edit-server
  :disabled t
  :if (and window-system
           (not running-alternate-emacs)
           (not noninteractive))
  :load-path "site-lisp/emacs_chrome/servers/"
  :init
  (add-hook 'after-init-hook 'server-start t)
  (add-hook 'after-init-hook 'edit-server-start t))

(use-package edit-var
  :bind ("C-c e v" . edit-variable))

(use-package emms-setup
  :disabled t
  :load-path "site-lisp/emms/lisp"
  :defines (emms-info-functions emms-player-simple-process-name)
  :commands (emms-standard emms-devel)
  :bind ("C-. M" . my-emms)
  :preface
  (defvar emms-initialized nil)
  (declare-function emms-smart-browse "emms-browser")

  (defun my-emms ()
    (interactive)
    (unless emms-initialized
      (emms-standard)
      (emms-default-players)
      (require 'emms-info-libtag)
      (setq emms-info-functions '(emms-info-libtag)
            emms-initialized t))
    (call-interactively #'emms-smart-browse))

  :config
  (bind-key "S-<f7>" 'emms-previous)
  (bind-key "S-<f8>" 'emms-pause)
  (bind-key "S-<f9>" 'emms-next)
  (bind-key "S-<f10>" 'emms-stop)

  (defun emms-player-mplayer-volume-up ()
    "Depends on mplayer’s -slave mode."
    (interactive)
    (process-send-string emms-player-simple-process-name "volume 1\n"))

  (defun emms-player-mplayer-volume-down ()
    "Depends on mplayer’s -slave mode."
    (interactive)
    (process-send-string emms-player-simple-process-name "volume -1\n"))

  (bind-key "C-. C--" 'emms-player-mplayer-volume-down)
  (bind-key "C-. C-=" 'emms-player-mplayer-volume-up))

(use-package gist
  :load-path "site-lisp/gist"
  :bind ("C-c G" . gist-region-or-buffer))

(use-package erc
  :defer t
  :defines (erc-timestamp-only-if-changed-flag
            erc-timestamp-format
            erc-fill-prefix
            erc-fill-column
            erc-insert-timestamp-function
            erc-modified-channels-alist)
  :preface
  (defun lookup-password (host user port)
    (require 'auth-source)
    (funcall (plist-get
              (car (auth-source-search
                    :host host
                    :user user
                    :type 'netrc
                    :port port))
              :secret)))

  (defun slowping (host)
    (= 0 (call-process "ping" nil nil nil "-c1" "-W5000" "-q" host)))

  (defun irc ()
    (interactive)
    (require 'erc)
    (if (slowping "192.168.9.133")
        (progn
          (erc :server "192.168.9.133"
               :port 6697
               :nick "johnw"
               :password (lookup-password "192.168.9.133"
                                          "johnw/freenode" 6697))
          (erc :server "192.168.9.133"
               :port 6697
               :nick "johnw"
               :password (lookup-password "192.168.9.133"
                                          "johnw/bitlbee" 6697)))

      (erc-tls :server "irc.freenode.net"
               :port 6697
               :nick "johnw"
               :password (lookup-password "irc.freenode.net" "johnw" 6667))))

  (defun setup-irc-environment ()
    (setq erc-timestamp-only-if-changed-flag nil
          erc-timestamp-format "%H:%M "
          erc-fill-prefix "          "
          erc-fill-column 88
          erc-insert-timestamp-function 'erc-insert-timestamp-left)

    (use-package agda-input
      :config
      (set-input-method "Agda"))

    (defun reset-erc-track-mode ()
      (interactive)
      (setq erc-modified-channels-alist nil)
      (erc-modified-channels-update)
      (erc-modified-channels-display)
      (force-mode-line-update))

    (bind-key "C-c r" 'reset-erc-track-mode))

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
  (add-to-list
   'erc-mode-hook
   #'(lambda () (set (make-local-variable 'scroll-conservatively) 100)))

  (if running-alternate-emacs
      (add-hook 'after-init-hook 'irc))

  :config
  (erc-track-minor-mode 1)
  (erc-track-mode 1)

  (use-package erc-alert)
  (use-package erc-highlight-nicknames)
  (use-package erc-patch)
  (use-package erc-macros)

  (use-package erc-yank
    :load-path "lisp/erc-yank"
    :config
    (bind-key "C-y" 'erc-yank erc-mode-map))

  (use-package wtf
    :commands wtf-is)

  (add-hook 'erc-insert-pre-hook
            (lambda (s)
              (when (erc-foolish-content s)
                (setq erc-insert-this nil)))))

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

    (defun ss (server)
      (interactive "sServer: ")
      (call-process "spawn" nil nil nil "ss" server))

    (use-package em-unix
      :defer t
      :config
      (unintern 'eshell/su nil)
      (unintern 'eshell/sudo nil)))

  :init
  (add-hook 'eshell-first-time-mode-hook 'eshell-initialize)

  (use-package esh-toggle
    :bind ("C-x C-z" . eshell-toggle)))

(use-package ess-site
  :disabled t
  :load-path "site-lisp/ess/lisp/"
  :commands R)

(use-package etags
  :bind ("M-T" . tags-search))

(use-package eval-expr
  :load-path "site-lisp/eval-expr"
  :bind ("M-:" . eval-expr)
  :config
  (setq eval-expr-print-function 'pp
        eval-expr-print-level 20
        eval-expr-print-length 100)

  (defun eval-expr-minibuffer-setup ()
    (set-syntax-table emacs-lisp-mode-syntax-table)
    (paredit-mode)))

(use-package eww
  :bind ("A-M-g" . eww)
  :config
  (use-package eww-lnum
    :load-path "site-lisp/eww-lnum"
    :config
    (bind-key "f" 'eww-lnum-follow eww-mode-map)
    (bind-key "F" 'eww-lnum-universal eww-mode-map)))

(use-package fetchmail-mode
  :commands fetchmail-mode)

(use-package flycheck
  :load-path "site-lisp/flycheck"
  :defer 5
  :config
  (defalias 'flycheck-show-error-at-point-soon 'flycheck-show-error-at-point)
  ;; :init
  ;; (progn
  ;;   (flycheck-define-checker clang++-ledger
  ;;     "Clang++ checker for Ledger"
  ;;     :command
  ;;     '("clang++" "-Wall" "-fsyntax-only"
  ;;       "-I/Users/johnw/Products/ledger/debug" "-I../lib"
  ;;       "-I../lib/utfcpp/source"
  ;;       "-I/System/Library/Frameworks/Python.framework/Versions/2.7/include/python2.7"
  ;;       "-include" "system.hh" "-c" source-inplace)
  ;;     :error-patterns
  ;;     '(("^\\(?1:.*\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\): warning:\\s-*\\(?4:.*\\)"
  ;;        warning)
  ;;       ("^\\(?1:.*\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\): error:\\s-*\\(?4:.*\\)"
  ;;        error))
  ;;     :modes 'c++-mode
  ;;     :predicate '(string-match "/ledger/" (buffer-file-name)))

  ;;   (push 'clang++-ledger flycheck-checkers))
  )

(use-package flyspell
  :bind (("C-c i b" . flyspell-buffer)
         ("C-c i f" . flyspell-mode))
  :init
  (use-package ispell
    :bind (("C-c i c" . ispell-comments-and-strings)
           ("C-c i d" . ispell-change-dictionary)
           ("C-c i k" . ispell-kill-ispell)
           ("C-c i m" . ispell-message)
           ("C-c i r" . ispell-region)))
  :config
  (unbind-key "C-." flyspell-mode-map))

(use-package git-messenger
  :load-path "site-lisp/emacs-git-messenger"
  :bind ("C-x v m" . git-messenger:popup-message))

(use-package git-wip-mode
  :load-path "site-lisp/git-wip/emacs/"
  :diminish git-wip-mode
  :commands git-wip-mode
  :init (add-hook 'find-file-hook #'(lambda () (git-wip-mode 1))))

(use-package dot-gnus
  :load-path "override/gnus"
  :bind (("M-G"   . switch-to-gnus)
         ("C-x m" . compose-mail))
  :init
  (setq gnus-init-file (expand-file-name "dot-gnus" user-emacs-directory)
        gnus-home-directory "~/Messages/Gnus/"))

(use-package grep
  :bind (("M-s d" . find-grep-dired)
         ("M-s F" . find-grep)
         ("M-s G" . grep)
         ("M-s p" . find-grep-in-project))
  :preface
  (defun find-grep-in-project (command-args)
    (interactive
     (let ((default (thing-at-point 'symbol)))
       (list (read-shell-command "Run find (like this): "
                                 (cons (concat "git --no-pager grep -n "
                                               default)
                                       (+ 24 (length default)))
                                 'grep-find-history))))
    (if command-args
        (let ((null-device nil))        ; see grep
          (grep command-args))))

  :config
  (add-hook 'grep-mode-hook #'(lambda () (use-package grep-ed)))

  (grep-apply-setting 'grep-command "egrep -nH -e ")
  (if nil
      (progn
        (setq-default grep-first-column 1)
        (grep-apply-setting
         'grep-find-command
         '("ag --noheading --nocolor --smart-case --nogroup --column -- "
           . 61)))
    (grep-apply-setting
     'grep-find-command
     '("find . -type f -print0 | xargs -P4 -0 egrep -nH " . 49))))

(use-package gud
  :disabled t
  :commands gud-gdb
  :bind ("C-. g" . show-debugger)
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
  (progn
    (bind-key "<f9>" 'gud-cont)
    (bind-key "<f10>" 'gud-next)
    (bind-key "<f11>" 'gud-step)
    (bind-key "S-<f11>" 'gud-finish)))

(use-package guide-key
  :load-path "site-lisp/guide-key"
  :diminish guide-key-mode
  :commands guide-key-mode
  :defer 10
  :config
  (setq guide-key/guide-key-sequence
        '("C-."
          "C-h e"
          "C-x 4"
          "C-x 5"
          "C-x r"
          "M-o"
          "M-s"))
  (guide-key-mode 1))

(use-package haskell-config
  :load-path ("lisp/haskell-config"
              "site-lisp/haskell-mode")
  :mode ("\\.l?hs\\'" . haskell-mode)
  :preface
  (defun snippet (name)
    (interactive "sName: ")
    (find-file (expand-file-name (concat name ".hs") "~/src/notes"))
    (haskell-mode)
    (goto-char (point-min))
    (when (eobp)
      (insert "hdr")
      (yas-expand))))

(use-package helm-grep
  :commands helm-do-grep-1
  :bind (("M-s f" . my-helm-do-grep-r)
         ("M-s g" . my-helm-do-grep))
  :preface
  (defun my-helm-do-grep ()
    (interactive)
    (helm-do-grep-1 (list default-directory)))

  (defun my-helm-do-grep-r ()
    (interactive)
    (helm-do-grep-1 (list default-directory) t)))

(use-package helm-swoop
  :load-path "site-lisp/helm-swoop"
  :bind (("M-s o" . helm-swoop)
         ("M-s /" . helm-multi-swoop))
  :config
  (use-package helm-match-plugin
    :config
    (helm-match-plugin-mode 1)))

(use-package helm-descbinds
  :load-path "site-lisp/helm-descbinds"
  :bind ("C-h b" . helm-descbinds)
  :init
  (fset 'describe-bindings 'helm-descbinds)
  :config
  (require 'helm-config))

(use-package helm-config
  :if (not running-alternate-emacs)
  :demand t
  :load-path "site-lisp/helm"
  :bind (("C-c h"   . helm-command-prefix)
         ("C-h a"   . helm-apropos)
         ("C-h e a" . my-helm-apropos)
         ("C-x f"   . helm-multi-files)
         ("M-s b"   . helm-occur)
         ("M-s n"   . my-helm-find)
         ("M-H"     . helm-resume))

  :preface
  (defun my-helm-find ()
    (interactive)
    (helm-find nil))

  :config
  (use-package helm-commands)
  (use-package helm-files)
  (use-package helm-buffers)
  (use-package helm-mode
    :diminish helm-mode
    :init
    (helm-mode 1))

  (use-package helm-ls-git
    :load-path "site-lisp/helm-ls-git")

  (use-package helm-match-plugin
    :config
    (helm-match-plugin-mode 1))

  (helm-autoresize-mode 1)

  (bind-key "<tab>" 'helm-execute-persistent-action helm-map)
  (bind-key "C-i" 'helm-execute-persistent-action helm-map)
  (bind-key "C-z" 'helm-select-action helm-map)
  (bind-key "A-v" 'helm-previous-page helm-map)

  (when (executable-find "curl")
    (setq helm-google-suggest-use-curl-p t)))

(use-package hi-lock
  :bind (("M-o l" . highlight-lines-matching-regexp)
         ("M-o r" . highlight-regexp)
         ("M-o w" . highlight-phrase)))

(use-package hilit-chg
  :bind ("M-o C" . highlight-changes-mode))

(use-package hippie-exp
  :bind (("M-/" . dabbrev-expand)
         ("M-?" . hippie-expand))
  :preface
  (autoload 'yas-expand "yasnippet" nil t)

  (defun my-yas-hippie-try-expand (first-time)
    (if (not first-time)
        (let ((yas-fallback-behavior 'return-nil))
          (yas-expand))
      (undo 1)
      nil))

  (defun my-hippie-expand-completions (&optional hippie-expand-function)
    "Return the full list of possible completions generated by `hippie-expand'.
   The optional argument can be generated with `make-hippie-expand-function'."
    (let ((this-command 'my-hippie-expand-completions)
          (last-command last-command)
          (buffer-modified (buffer-modified-p))
          (hippie-expand-function (or hippie-expand-function 'hippie-expand)))
      (flet ((ding))        ; avoid the (ding) when hippie-expand exhausts its
                                        ; options.
        (while (progn
                 (funcall hippie-expand-function nil)
                 (setq last-command 'my-hippie-expand-completions)
                 (not (equal he-num -1)))))
      ;; Evaluating the completions modifies the buffer, however we will finish
      ;; up in the same state that we began.
      (set-buffer-modified-p buffer-modified)
      ;; Provide the options in the order in which they are normally generated.
      (delete he-search-string (reverse he-tried-table))))

  (defmacro my-ido-hippie-expand-with (hippie-expand-function)
    "Generate an interactively-callable function that offers ido-based
  completion using the specified hippie-expand function."
    `(call-interactively
      (lambda (&optional selection)
        (interactive
         (let ((options (my-hippie-expand-completions ,hippie-expand-function)))
           (if options
               (list
                ;; (ido-completing-read "Completions: " options)
                (completing-read "Completions: " options)
                ))))
        (if selection
            (he-substitute-string selection t)
          (message "No expansion found")))))

  (defun my-ido-hippie-expand ()
    "Offer ido-based completion for the word at point."
    (interactive)
    (my-ido-hippie-expand-with 'hippie-expand))

  (defun my-try-expand-company (old)
    (require 'company)
    (unless company-candidates
      (company-auto-begin))
    (if (not old)
        (progn
          (he-init-string (he-lisp-symbol-beg) (point))
          (if (not (he-string-member he-search-string he-tried-table))
              (setq he-tried-table (cons he-search-string he-tried-table)))
          (setq he-expand-list
                (and (not (equal he-search-string ""))
                     company-candidates))))
    (while (and he-expand-list
                (he-string-member (car he-expand-list) he-tried-table))
      (setq he-expand-list (cdr he-expand-list)))
    (if (null he-expand-list)
        (progn
          (if old (he-reset-string))
          ())
      (progn
	(he-substitute-string (car he-expand-list))
	(setq he-expand-list (cdr he-expand-list))
	t)))

  (defun he-tag-beg ()
    (save-excursion
      (backward-word 1)
      (point)))

  (defun tags-complete-tag (string predicate what)
    (save-excursion
      ;; If we need to ask for the tag table, allow that.
      (if (eq what t)
          (all-completions string (tags-completion-table) predicate)
        (try-completion string (tags-completion-table) predicate))))

  (defun try-expand-tag (old)
    (when tags-table-list
      (unless old
        (he-init-string (he-tag-beg) (point))
        (setq he-expand-list
              (sort (all-completions he-search-string 'tags-complete-tag)
                    'string-lessp)))
      (while (and he-expand-list
                  (he-string-member (car he-expand-list) he-tried-table))
        (setq he-expand-list (cdr he-expand-list)))
      (if (null he-expand-list)
          (progn
            (when old (he-reset-string))
            ())
        (he-substitute-string (car he-expand-list))
        (setq he-expand-list (cdr he-expand-list))
        t)))

  (defun my-dabbrev-substring-search (pattern &optional reverse limit)
    (let ((result ())
          (regpat (cond ((not hippie-expand-dabbrev-as-symbol)
                         (concat (regexp-quote pattern) "\\sw+"))
                        ((eq (char-syntax (aref pattern 0)) ?_)
                         (concat (regexp-quote pattern) "\\(\\sw\\|\\s_\\)+"))
                        (t
                         (concat (regexp-quote pattern)
                                 "\\(\\sw\\|\\s_\\)+")))))
      (while (and (not result)
                  (if reverse
                      (re-search-backward regpat limit t)
                    (re-search-forward regpat limit t)))
        (setq result (buffer-substring-no-properties
                      (save-excursion
                        (goto-char (match-beginning 0))
                        (skip-syntax-backward "w_")
                        (point))
                      (match-end 0)))
        (if (he-string-member result he-tried-table t)
            (setq result nil)))     ; ignore if bad prefix or already in table
      result))

  (defun try-my-dabbrev-substring (old)
    (let ((old-fun (symbol-function 'he-dabbrev-search)))
      (fset 'he-dabbrev-search (symbol-function 'my-dabbrev-substring-search))
      (unwind-protect
          (try-expand-dabbrev old)
        (fset 'he-dabbrev-search old-fun))))

  (defun try-expand-flexible-abbrev (old)
    "Try to complete word using flexible matching.

  Flexible matching works by taking the search string and then
  interspersing it with a regexp for any character. So, if you try
  to do a flexible match for `foo' it will match the word
  `findOtherOtter' but also `fixTheBoringOrange' and
  `ifthisisboringstopreadingnow'.

  The argument OLD has to be nil the first call of this function, and t
  for subsequent calls (for further possible completions of the same
  string).  It returns t if a new completion is found, nil otherwise."
    (if (not old)
        (progn
          (he-init-string (he-lisp-symbol-beg) (point))
          (if (not (he-string-member he-search-string he-tried-table))
              (setq he-tried-table (cons he-search-string he-tried-table)))
          (setq he-expand-list
                (and (not (equal he-search-string ""))
                     (he-flexible-abbrev-collect he-search-string)))))
    (while (and he-expand-list
                (he-string-member (car he-expand-list) he-tried-table))
      (setq he-expand-list (cdr he-expand-list)))
    (if (null he-expand-list)
        (progn
          (if old (he-reset-string))
          ())
      (progn
	(he-substitute-string (car he-expand-list))
	(setq he-expand-list (cdr he-expand-list))
	t)))

  (defun he-flexible-abbrev-collect (str)
    "Find and collect all words that flex-matches STR.
  See docstring for `try-expand-flexible-abbrev' for information
  about what flexible matching means in this context."
    (let ((collection nil)
          (regexp (he-flexible-abbrev-create-regexp str)))
      (save-excursion
        (goto-char (point-min))
        (while (search-forward-regexp regexp nil t)
          ;; Is there a better or quicker way than using `thing-at-point'
          ;; here?
          (setq collection (cons (thing-at-point 'word) collection))))
      collection))

  (defun he-flexible-abbrev-create-regexp (str)
    "Generate regexp for flexible matching of STR.
  See docstring for `try-expand-flexible-abbrev' for information
  about what flexible matching means in this context."
    (concat "\\b" (mapconcat (lambda (x) (concat "\\w*" (list x))) str "")
            "\\w*" "\\b"))

  (defun my-try-expand-dabbrev-visible (old)
    (save-excursion (try-expand-dabbrev-visible old)))

  :config
  (setq hippie-expand-try-functions-list
        '(my-yas-hippie-try-expand
          my-try-expand-company
          try-my-dabbrev-substring
          my-try-expand-dabbrev-visible
          try-expand-dabbrev
          try-expand-dabbrev-all-buffers
          try-expand-dabbrev-from-kill
          try-expand-tag
          try-expand-flexible-abbrev
          try-complete-file-name-partially
          try-complete-file-name
          try-expand-all-abbrevs
          try-expand-list
          try-expand-line
          try-expand-line-all-buffers
          try-complete-lisp-symbol-partially
          try-complete-lisp-symbol))

  (bind-key "M-i" 'my-ido-hippie-expand)

  (defadvice he-substitute-string (after he-paredit-fix)
    "remove extra paren when expanding line in paredit"
    (if (and paredit-mode (equal (substring str -1) ")"))
        (progn (backward-delete-char 1) (forward-char)))))

(use-package hl-line
  :commands hl-line-mode
  :bind (("M-o h" . hl-line-mode))
  :config
  (use-package hl-line+))

(use-package ibuffer
  :bind ("C-x C-b" . ibuffer)
  :init
  (add-hook 'ibuffer-mode-hook
            #'(lambda ()
                (ibuffer-switch-to-saved-filter-groups "default"))))

(use-package ido
  :demand t
  :defines (ido-cur-item
            ido-require-match
            ido-selected
            ido-final-text
            ido-show-confirm-message)
  :bind (("C-x b" . ido-switch-buffer)
         ("C-x B" . ido-switch-buffer-other-window))
  :preface
  (eval-when-compile
    (defvar ido-require-match)
    (defvar ido-cur-item)
    (defvar ido-show-confirm-message)
    (defvar ido-selected)
    (defvar ido-final-text))

  (defun ido-smart-select-text ()
    "Select the current completed item.  Do NOT descend into directories."
    (interactive)
    (when (and (or (not ido-require-match)
                   (if (memq ido-require-match
                             '(confirm confirm-after-completion))
                       (if (or (eq ido-cur-item 'dir)
                               (eq last-command this-command))
                           t
                         (setq ido-show-confirm-message t)
                         nil))
                   (ido-existing-item-p))
               (not ido-incomplete-regexp))
      (when ido-current-directory
        (setq ido-exit 'takeprompt)
        (unless (and ido-text (= 0 (length ido-text)))
          (let ((match (ido-name (car ido-matches))))
            (throw 'ido
                   (setq ido-selected
                         (if match
                             (replace-regexp-in-string "/\\'" "" match)
                           ido-text)
                         ido-text ido-selected
                         ido-final-text ido-text)))))
      (exit-minibuffer)))

  :config
  (ido-mode 'buffer)

  (use-package ido-hacks
    :demand t
    :load-path "site-lisp/ido-hacks"
    :bind ("M-x" . my-ido-hacks-execute-extended-command)
    :config
    (ido-hacks-mode 1)

    (defvar ido-hacks-completing-read (symbol-function 'completing-read))
    (fset 'completing-read ido-hacks-orgin-completing-read-function)
    (defun my-ido-hacks-execute-extended-command (&optional arg)
      (interactive "P")
      (flet ((completing-read
              (prompt collection &optional predicate require-match
                      initial-input hist def inherit-input-method)
              (funcall ido-hacks-completing-read
                       prompt collection predicate require-match
                       initial-input hist def inherit-input-method)))
        (ido-hacks-execute-extended-command arg))))

  (use-package flx-ido
    :disabled t
    :load-path "site-lisp/flx"
    :config
    (flx-ido-mode 1))

  (add-hook 'ido-minibuffer-setup-hook
            #'(lambda ()
                (bind-key "<return>" 'ido-smart-select-text
                          ido-file-completion-map))))

(use-package idris-mode
  :disabled t
  :mode ("\\.idr\\'" . idris-mode)
  :config
  (defadvice idris-load-file (around my-idris-load-file activate)
    (let ((wind (selected-window)))
      ad-do-it
      (select-window wind))))

(use-package ielm
  :bind ("C-c :" . ielm)
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
            (function
             (lambda ()
               (bind-key "<return>" 'my-ielm-return ielm-map)))
            t))

(use-package iflipb
  :load-path "site-lisp/iflipb"
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
  :disabled t
  :config
  (auto-image-file-mode 1))

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

(use-package indirect
  :bind ("C-c C" . indirect-region))

(use-package cus-edit
  :load-path "lisp/initsplit"
  :defer 5
  :config
  (use-package initsplit))

(use-package ipa
  :load-path "site-lisp/ipa-el"
  :commands (ipa-insert ipa-load-annotations-into-buffer)
  :init
  (add-hook 'find-file-hook 'ipa-load-annotations-into-buffer))

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
  (bind-key "C-c" 'isearch-toggle-case-fold isearch-mode-map)
  (bind-key "C-t" 'isearch-toggle-regexp isearch-mode-map)
  (bind-key "C-^" 'isearch-edit-string isearch-mode-map)
  (bind-key "C-i" 'isearch-complete isearch-mode-map))

(use-package js2-mode
  :load-path "site-lisp/js2-mode"
  :mode "\\.js\\'")

(use-package json-mode
  :load-path ("site-lisp/json-mode"
              "site-lisp/json-reformat"
              "site-lisp/json-snatcher")
  :mode "\\.json\\'")

(use-package ledger-mode
  :load-path "~/src/ledger/lisp"
  :commands ledger-mode
  :bind ("C-c L" . my-ledger-start-entry)
  :preface
  (defun my-ledger-start-entry (&optional arg)
    (interactive "p")
    (find-file-other-window "~/Documents/Accounts/ledger.dat")
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

  (defvar slime-mode nil)
  (defvar lisp-mode-initialized nil)

  (defun my-lisp-mode-hook ()
    (unless lisp-mode-initialized
      (setq lisp-mode-initialized t)

      (use-package redshank
        :diminish redshank-mode)

      (use-package elisp-slime-nav
        :load-path "site-lisp/elisp-slime-nav"
        :diminish elisp-slime-nav-mode)

      (use-package edebug)

      (use-package eldoc
        :diminish eldoc-mode
        :commands eldoc-mode
        :config
        (use-package eldoc-extension
          :disabled t
          :defer t
          :init
          (add-hook 'emacs-lisp-mode-hook
                    #'(lambda () (require 'eldoc-extension)) t))
        (eldoc-add-command 'paredit-backward-delete
                           'paredit-close-round))

      (use-package cldoc
        :commands (cldoc-mode turn-on-cldoc-mode)
        :diminish cldoc-mode)

      (use-package ert
        :bind ("C-c e t" . ert-run-tests-interactively))

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

      (use-package highlight-cl
        :init
        (mapc (function
               (lambda (mode-hook)
                 (add-hook mode-hook
                           'highlight-cl-add-font-lock-keywords)))
              lisp-mode-hooks))

      (defun my-elisp-indent-or-complete (&optional arg)
        (interactive "p")
        (call-interactively 'lisp-indent-line)
        (unless (or (looking-back "^\\s-*")
                    (bolp)
                    (not (looking-back "[-A-Za-z0-9_*+/=<>!?]+")))
          (call-interactively 'lisp-complete-symbol)))

      (defun my-lisp-indent-or-complete (&optional arg)
        (interactive "p")
        (if (or (looking-back "^\\s-*") (bolp))
            (call-interactively 'lisp-indent-line)
          (call-interactively 'slime-indent-and-complete-symbol)))

      (defun my-byte-recompile-file ()
        (save-excursion
          (byte-recompile-file buffer-file-name)))

      (use-package info-lookmore
        :load-path "site-lisp/info-lookmore"
        :config
        (info-lookmore-elisp-cl)
        (info-lookmore-elisp-userlast)
        (info-lookmore-elisp-gnus)
        (info-lookmore-apropos-elisp))

      (use-package testcover
        :commands testcover-this-defun)

      (mapc (lambda (mode)
              (info-lookup-add-help
               :mode mode
               :regexp "[^][()'\" \t\n]+"
               :ignore-case t
               :doc-spec '(("(ansicl)Symbol Index" nil nil nil))))
            lisp-modes))

    (auto-fill-mode 1)
    (paredit-mode 1)
    (redshank-mode 1)
    (elisp-slime-nav-mode 1)

    (local-set-key (kbd "<return>") 'paredit-newline)

    (add-hook 'after-save-hook 'check-parens nil t)

    (unless (memq major-mode
                  '(emacs-lisp-mode inferior-emacs-lisp-mode ielm-mode))
      (turn-on-cldoc-mode)
      (bind-key "M-q" 'slime-reindent-defun lisp-mode-map)
      (bind-key "M-l" 'slime-selector lisp-mode-map)))

  ;; Change lambda to an actual lambda symbol
  :init
  (mapc
   (lambda (major-mode)
     (font-lock-add-keywords
      major-mode
      '(("(\\(lambda\\)\\>"
         (0 (ignore
             (compose-region (match-beginning 1)
                             (match-end 1) ?λ))))
        ("(\\|)" . 'esk-paren-face)
        ("(\\(ert-deftest\\)\\>[         '(]*\\(setf[    ]+\\sw+\\|\\sw+\\)?"
         (1 font-lock-keyword-face)
         (2 font-lock-function-name-face
            nil t)))))
   lisp-modes)

  (apply #'hook-into-modes 'my-lisp-mode-hook lisp-mode-hooks))

(use-package llvm-mode
  :mode "\\.ll\\'")

(use-package lua-mode
  :load-path "site-lisp/lua-mode"
  :mode "\\.lua\\'"
  :interpreter ("lua" . lua-mode))

(use-package lusty-explorer
  :demand t
  :load-path "site-lisp/lusty-emacs"
  :bind ("C-x C-f" . my-lusty-file-explorer)
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

  (defun lusty-read-file-name ()
    "Launch the file/directory mode of LustyExplorer."
    (interactive)
    (require 'lusty-explorer)
    (let ((lusty--active-mode :file-explorer))
      (lusty--define-mode-map)
      (let* ((lusty--ignored-extensions-regex
              (concat "\\(?:" (regexp-opt completion-ignored-extensions)
                      "\\)$"))
             (minibuffer-local-filename-completion-map lusty-mode-map)
             (lusty-only-directories nil))
        (lusty--run 'read-file-name default-directory ""))))

  (defun my-lusty-file-explorer ()
    "Launch the file/directory mode of LustyExplorer."
    (interactive)
    (require 'lusty-explorer)
    (let ((lusty--active-mode :file-explorer)
          (helm-mode-prev (and (boundp 'helm-mode) helm-mode)))
      (if (fboundp 'helm-mode)
          (helm-mode -1))
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
        (if (fboundp 'helm-mode)
            (helm-mode (if helm-mode-prev 1 -1))))))

  :config
  (defun my-lusty-setup-hook ()
    (bind-key "SPC" 'lusty-select-match lusty-mode-map)
    (bind-key "C-d" 'exit-minibuffer lusty-mode-map))

  (add-hook 'lusty-setup-hook 'my-lusty-setup-hook)

  (defun lusty-open-this ()
    "Open the given file/directory/buffer, creating it if not
    already present."
    (interactive)
    (when lusty--active-mode
      (ecase lusty--active-mode
        (:file-explorer
         (let* ((path (minibuffer-contents-no-properties))
                (last-char (aref path (1- (length path)))))
           (lusty-select-match)
           (lusty-select-current-name)))
        (:buffer-explorer (lusty-select-match)))))

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
  :load-path "site-lisp/magit"
  :bind (("C-x g" . magit-status)
         ("C-x G" . magit-status-with-prefix))
  :preface
  (defun magit-monitor (&optional no-display)
    "Start git-monitor in the current directory."
    (interactive)
    (when (string-match "\\*magit: \\(.+?\\)\\*" (buffer-name))
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

  (use-package magit-backup
    :commands magit-backup-mode
    :config
    (magit-backup-mode -1))

  (use-package magit-commit
    :config
    (remove-hook 'server-switch-hook 'magit-commit-diff))

  (unbind-key "M-h" magit-mode-map)
  (unbind-key "M-s" magit-mode-map)
  (unbind-key "M-m" magit-mode-map)

  ;; (bind-key "M-H" #'magit-show-level-2-all magit-mode-map)
  ;; (bind-key "M-S" #'magit-show-level-4-all magit-mode-map)
  (bind-key "U" #'magit-unstage-all magit-mode-map)

  (add-hook 'magit-log-edit-mode-hook
            #'(lambda ()
                (set-fill-column 72)
                (flyspell-mode)))

  (add-hook 'magit-status-mode-hook #'(lambda () (magit-monitor t))))

(use-package markdown-mode
  :load-path "site-lisp/markdown-mode"
  :mode (("\\`README\\.md\\'" . gfm-mode)
         ("\\.md\\'"          . markdown-mode)
         ("\\.markdown\\'"    . markdown-mode)))

(use-package midnight
  :defer 10)

(use-package mudel
  :disabled t
  :commands mudel
  :bind ("C-c M" . mud)
  :init
  (defun mud ()
    (interactive)
    (mudel "4dimensions" "4dimensions.org" 6000)))

(use-package mule
  :no-require t
  :defines x-select-request-type
  :config
  (prefer-coding-system 'utf-8)
  (set-terminal-coding-system 'utf-8)
  (setq x-select-request-type '(UTF8_STRING COMPOUND_TEXT TEXT STRING)))

(use-package multi-term
  :disabled t
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
      ;; Internal handle for `multi-term' buffer.
      (multi-term-internal)
      ;; Switch buffer
      (switch-to-buffer term-buffer)))

  :config
  (defalias 'my-term-send-raw-at-prompt 'term-send-raw)

  (defun my-term-end-of-buffer ()
    (interactive)
    (call-interactively #'end-of-buffer)
    (if (and (eobp) (bolp))
        (delete-char -1)))

  (require 'term)

  (defadvice term-process-pager (after term-process-rebind-keys activate)
    (define-key term-pager-break-map  "\177" 'term-pager-back-page)))

(use-package multiple-cursors
  :disabled t
  :load-path "site-lisp/multiple-cursors-el"
  :bind (("C-S-c C-S-c" . mc/edit-lines)
         ("C->"         . mc/mark-next-like-this)
         ("C-<"         . mc/mark-previous-like-this)
         ("C-c C-<"     . mc/mark-all-like-this))
  :config
  (setq mc/list-file (expand-file-name "mc-lists.el" user-data-directory)))

(use-package nix-mode
  :mode "\\.nix\\'")

(use-package nf-procmail-mode
  :commands nf-procmail-mode)

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
            #'(lambda ()
                (add-hook 'after-save-hook 'update-nroff-timestamp nil t))))

(use-package nxml-mode
  :commands nxml-mode
  :init
  (defalias 'xml-mode 'nxml-mode)
  :config
  (defun my-nxml-mode-hook ()
    (bind-key "<return>" 'newline-and-indent nxml-mode-map))

  (add-hook 'nxml-mode-hook 'my-nxml-mode-hook)

  (defun tidy-xml-buffer ()
    (interactive)
    (save-excursion
      (call-process-region (point-min) (point-max) "tidy" t t nil
                           "-xml" "-i" "-wrap" "0" "-omit" "-q" "-utf8")))

  (bind-key "C-c M-h" 'tidy-xml-buffer nxml-mode-map))

(use-package on-screen
  :load-path "site-lisp/on-screen"
  :defer 5
  :config
  (on-screen-global-mode 1))

(use-package dot-org
  :load-path "override/org-mode"
  :commands my-org-startup
  :bind (("M-C"   . jump-to-org-agenda)
         ("M-m"   . org-smart-capture)
         ("M-M"   . org-inline-note)
         ("C-c a" . org-agenda)
         ("C-c S" . org-store-link)
         ("C-c l" . org-insert-link)
         ("C-. n" . org-velocity-read))
  :defer 30
  :config
  (when (and (not running-alternate-emacs)
             (quickping "192.168.9.133"))
    (run-with-idle-timer 300 t 'jump-to-org-agenda)
    (my-org-startup))

  (add-hook 'org-mode-hook #'(lambda () (yas-minor-mode 1))))

(use-package pabbrev
  :load-path "site-lisp/pabbrev"
  :commands pabbrev-mode
  :diminish pabbrev-mode)

(use-package paredit
  :commands paredit-mode
  :diminish paredit-mode
  :config
  (use-package paredit-ext)

  (bind-key "C-M-l" 'paredit-recentre-on-sexp paredit-mode-map)

  (bind-key ")" 'paredit-close-round-and-newline paredit-mode-map)
  (bind-key "M-)" 'paredit-close-round paredit-mode-map)

  (bind-key "M-k" 'paredit-raise-sexp paredit-mode-map)
  (bind-key "M-I" 'paredit-splice-sexp paredit-mode-map)

  (unbind-key "M-r" paredit-mode-map)
  (unbind-key "M-s" paredit-mode-map)

  (bind-key "C-. D" 'paredit-forward-down paredit-mode-map)
  (bind-key "C-. B" 'paredit-splice-sexp-killing-backward paredit-mode-map)
  (bind-key "C-. C" 'paredit-convolute-sexp paredit-mode-map)
  (bind-key "C-. F" 'paredit-splice-sexp-killing-forward paredit-mode-map)
  (bind-key "C-. a" 'paredit-add-to-next-list paredit-mode-map)
  (bind-key "C-. A" 'paredit-add-to-previous-list paredit-mode-map)
  (bind-key "C-. j" 'paredit-join-with-next-list paredit-mode-map)
  (bind-key "C-. J" 'paredit-join-with-previous-list paredit-mode-map))


(or (use-package mic-paren
      :defer 5
      :config
      (paren-activate))
    (use-package paren
      :defer 5
      :config
      (show-paren-mode 1)))

(use-package per-window-point
  :commands pwp-mode
  :defer 5
  :config
  (pwp-mode 1))

(use-package persian-johnw
  :disabled t)

(use-package persistent-scratch
  :disabled t
  :if (and window-system (not running-alternate-emacs)
           (not noninteractive)))

(use-package perspective
  :disabled t
  :config
  (use-package persp-projectile)
  (persp-mode))

(use-package popup-ruler
  :bind (("C-. r" . popup-ruler)
         ("C-. R" . popup-ruler-vertical)))

(use-package pp-c-l
  :commands pretty-control-l-mode
  :init
  (add-hook 'prog-mode-hook 'pretty-control-l-mode))

(use-package projectile
  :load-path "site-lisp/projectile"
  :diminish projectile-mode
  :commands projectile-global-mode
  :defer 5
  :bind-keymap ("C-c p" . projectile-command-map)
  :config
  (use-package helm-projectile
    :config
    (setq projectile-completion-system 'helm)
    (helm-projectile-on))
  (projectile-global-mode))

(use-package proof-site
  :load-path (lambda () (list (nix-lisp-path "ProofGeneral/generic")
                         (nix-lisp-path "ProofGeneral/lib")
                         (nix-lisp-path "ProofGeneral/coq")))
  :mode ("\\.v\\'" . coq-mode)
  :preface
  (eval-when-compile
    (defvar proof-auto-raise-buffers)
    (defvar proof-three-window-enable)
    (defvar proof-shrink-windows-tofit)

    (declare-function proof-get-window-for-buffer "proof-utils")
    (declare-function proof-resize-window-tofit "proof-utils")
    (declare-function window-bottom-p "proof-compat"))

  (defun my-proof-display-and-keep-buffer (buffer &optional pos force)
    (when (or force proof-auto-raise-buffers)
      (save-excursion
        (save-selected-window
          (let ((window (proof-get-window-for-buffer buffer)))
            (when (window-live-p window) ;; [fails sometimes?]
              (if proof-three-window-enable
                  (set-window-dedicated-p window nil))
              (select-window window)
              (if proof-shrink-windows-tofit
                  (proof-resize-window-tofit)
                ;; If we're not shrinking to fit, allow the size of
                ;; this window to change.  [NB: might be nicer to
                ;; fix the size based on user choice]
                (setq window-size-fixed nil))
              ;; For various reasons, point may get moved around in
              ;; response buffer.  Attempt to normalise its position.
              (goto-char (or pos (point-max)))
              (if pos
                  (beginning-of-line)
                (skip-chars-backward "\n\t "))
              ;; Ensure point visible.  Again, window may have died
              ;; inside shrink to fit, for some reason
              (when (window-live-p window)
                (unless (pos-visible-in-window-p (point) window)
                  (recenter -1))
                (with-current-buffer buffer
                  (if (window-bottom-p window)
                      (unless (local-variable-p 'mode-line-format)
                        ;; Don't show any mode line.
                        (set (make-local-variable 'mode-line-format) nil))
                    (unless mode-line-format
                      ;; If the buffer gets displayed elsewhere, re-add
                      ;; the modeline.
                      (kill-local-variable 'mode-line-format)))))))))))

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
       (holes-mode -1)
       (whitespace-mode 1)
       (ggtags-mode 1)
       ;; (set-input-method "Agda")
       ;; (proof-unicode-tokens-enable 1)
       (add-hook 'proof-shell-extend-queue-hook
                 (lambda ()
                   (set-window-dedicated-p (selected-window) t)))
       (defalias 'proof-display-and-keep-buffer
         'my-proof-display-and-keep-buffer)))

    (bind-key "M-RET" #'proof-goto-point coq-mode-map)
    (bind-key "RET" #'newline-and-indent coq-mode-map)
    (bind-key "C-c C-p" #'(lambda ()
                            (interactive)
                            (proof-layout-windows)
                            (proof-prf)) coq-mode-map)
    (bind-key "C-c C-a C-s" #'coq-SearchConstant coq-mode-map)
    (unbind-key "C-c h" coq-mode-map))

  (use-package pg-user
    :defer t
    :config
    (defadvice proof-retract-buffer
        (around my-proof-retract-buffer activate)
      (condition-case err ad-do-it
        (error (shell-command "killall ssrcoq"))))))

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

(use-package puppet-mode
  :disabled t
  :mode ("\\.pp\\'" . puppet-mode)
  :config
  (use-package puppet-ext))

(use-package python-mode
  :load-path "site-lisp/python-mode"
  :mode ("\\.py\\'" . python-mode)
  :interpreter ("python" . python-mode)
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

    (bind-key "C-c C-z" 'python-shell python-mode-map)
    (unbind-key "C-c c" python-mode-map))

  (add-hook 'python-mode-hook 'my-python-mode-hook))

(use-package quickrun
  :disabled t
  :load-path "site-lisp/emacs-quickrun"
  :bind ("C-c C-r" . quickrun))

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

(use-package repeat-insert
  :disabled t
  :commands (insert-patterned
             insert-patterned-2
             insert-patterned-3
             insert-patterned-4))

(use-package ruby-mode
  :load-path "site-lisp/ruby-mode"
  :mode ("\\.rb\\'" . ruby-mode)
  :interpreter ("ruby" . ruby-mode)
  :functions inf-ruby-keys
  :config
  (use-package yari
    :load-path "site-lisp/yari-with-buttons"
    :init
    (progn
      (defvar yari-helm-source-ri-pages
        '((name . "RI documentation")
          (candidates . (lambda () (yari-ruby-obarray)))
          (action  ("Show with Yari" . yari))
          (candidate-number-limit . 300)
          (requires-pattern . 2)
          "Source for completing RI documentation."))

      (defun helm-yari (&optional rehash)
        (interactive (list current-prefix-arg))
        (when current-prefix-arg (yari-ruby-obarray rehash))
        (helm 'yari-helm-source-ri-pages (yari-symbol-at-point)))))

  (defun my-ruby-smart-return ()
    (interactive)
    (when (memq (char-after) '(?\| ?\" ?\'))
      (forward-char))
    (call-interactively 'newline-and-indent))

  (defun my-ruby-mode-hook ()
    (require 'inf-ruby)
    (inf-ruby-keys)
    (bind-key "<return>" 'my-ruby-smart-return ruby-mode-map)
    (bind-key "C-h C-i" 'helm-yari ruby-mode-map))

  (add-hook 'ruby-mode-hook 'my-ruby-mode-hook))

(use-package sage
  :disabled t
  :load-path "/Applications/Misc/sage/local/share/emacs/site-lisp/sage-mode/"
  :config
  (defvar python-source-modes nil)
  (setq sage-command "/Applications/Misc/sage/sage")

  ;; If you want sage-view to typeset all your output and have plot()
  ;; commands inline, uncomment the following line and configure sage-view:
  (require 'sage-view)
  (add-hook 'sage-startup-before-prompt-hook 'compilation-setup)
  (add-hook 'sage-startup-after-prompt-hook 'sage-view)
  ;; You can use commands like
  ;; (add-hook 'sage-startup-after-prompt-hook
  ;;           'sage-view-disable-inline-output)
  (add-hook 'sage-startup-after-prompt-hook 'sage-view-disable-inline-plots t)
  ;; to enable some combination of features

  (setq sage-startup-before-prompt-command "")

  (let* ((str
          (shell-command-to-string
           (concat
            "find /nix/store/*-tetex-* -path "
            "'*/share/texmf-dist/tex/latex/preview' -type d | head -1")))
         (texinputs (concat ".:" (substring str 0 (1- (length str))) ":")))
    (setenv "TEXINPUTS" texinputs)

    (eval
     `(defadvice sage (around my-sage activate)
        (let ((process-environment
               (cons
                (concat "TEXINPUTS=" ,texinputs)
                (mapcar
                 (lambda (x)
                   (if (string-match "\\`PATH=" x)
                       (concat "PATH=/usr/bin:/bin:"
                               (expand-file-name "~/.nix-profile/bin")) x))
                 process-environment))))
          ad-do-it))))

  (bind-key "C-c Z" 'sage))

(use-package selectkey
  :disabled t
  :bind-keymap ("C-. b" . selectkey-select-prefix-map)
  :config
  (selectkey-define-select-key compile "c" "\\*compilation")
  (selectkey-define-select-key shell-command "o" "Shell Command")
  (selectkey-define-select-key shell "s" "\\*shell" (shell))
  (selectkey-define-select-key multi-term "t" "\\*terminal" (multi-term-next))
  (selectkey-define-select-key eshell "z" "\\*eshell" (eshell)))

(use-package session
  :if (not noninteractive)
  :load-path "site-lisp/session/lisp/"
  :preface
  (defun remove-session-use-package-from-settings ()
    (when (string= (file-name-nondirectory (buffer-file-name))
                   "settings.el")
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

(use-package slime
  :disabled t
  :load-path "site-lisp/slime"
  :commands (sbcl slime)
  :init
  (add-hook
   'slime-load-hook
   #'(lambda ()
       (slime-setup
        '(slime-asdf
          slime-autodoc
          slime-banner
          slime-c-p-c
          slime-editing-commands
          slime-fancy-inspector
          slime-fancy
          slime-fuzzy
          slime-highlight-edits
          slime-parse
          slime-presentation-streams
          slime-presentations
          slime-references
          slime-repl
          slime-sbcl-exts
          slime-package-fu
          slime-fontifying-fu
          slime-mdot-fu
          slime-scratch
          slime-tramp
          ;; slime-enclosing-context
          ;; slime-typeout-frame
          slime-xref-browser))

       (define-key slime-repl-mode-map [(control return)] 'other-window)

       (define-key slime-mode-map [return] 'paredit-newline)
       (define-key slime-mode-map [(control ?h) ?F] 'info-lookup-symbol)))

  :config
  (progn
    (eval-when-compile
      (defvar slime-repl-mode-map))

    (setq slime-net-coding-system 'utf-8-unix)

    (setq slime-lisp-implementations
          '((sbcl
             ("sbcl" "--core"
              "/Users/johnw/Library/Lisp/sbcl.core-with-slime-X86-64")
             :init
             (lambda (port-file _)
               (format "(swank:start-server %S)\n" port-file)))
            (ecl ("ecl" "-load" "/Users/johnw/Library/Lisp/init.lisp"))
            (clisp ("clisp" "-i" "/Users/johnw/Library/Lisp/lwinit.lisp"))))

    (setq slime-default-lisp 'sbcl)
    (setq slime-complete-symbol*-fancy t)
    (setq slime-complete-symbol-function 'slime-fuzzy-complete-symbol)

    (defun sbcl (&optional arg)
      (interactive "P")
      (let ((slime-default-lisp (if arg 'sbcl64 'sbcl))
            (current-prefix-arg nil))
        (slime)))
    (defun clisp () (interactive) (let ((slime-default-lisp 'clisp)) (slime)))
    (defun ecl () (interactive) (let ((slime-default-lisp 'ecl)) (slime)))

    (defun start-slime ()
      (interactive)
      (unless (slime-connected-p)
        (save-excursion (slime))))

    (add-hook 'slime-mode-hook 'start-slime)
    (add-hook 'slime-load-hook #'(lambda () (require 'slime-fancy)))
    (add-hook 'inferior-lisp-mode-hook #'(lambda () (inferior-slime-mode t)))

    (use-package hyperspec
      :config
      (setq common-lisp-hyperspec-root
            (expand-file-name "~/Library/Lisp/HyperSpec/")))))

(use-package smart-compile
  :disabled t
  :commands smart-compile
  :bind (("C-c c" . smart-compile)
         ("A-n"   . next-error)
         ("A-p"   . previous-error)))

(use-package smartparens
  :disabled t
  :load-path "site-lisp/smartparens"
  :commands (smartparens-mode show-smartparens-mode)
  :config
  (use-package smartparens-config))

(use-package smerge-mode
  :commands smerge-mode
  :config
  (setq smerge-command-prefix (kbd "C-. C-.")))

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

  (bind-key "/" 'sr-sticky-isearch-forward sr-mode-map)
  (bind-key "<backspace>" 'sr-scroll-quick-view-down sr-mode-map)
  (bind-key "C-x t" 'sr-toggle-truncate-lines sr-mode-map)

  (bind-key "q" 'sr-history-prev sr-mode-map)
  (bind-key "z" 'sr-quit sr-mode-map)

  (unbind-key "C-e" sr-mode-map)
  (unbind-key "C-p" sr-tabs-mode-map)
  (unbind-key "C-n" sr-tabs-mode-map)
  (unbind-key "M-<backspace>" sr-term-line-minor-mode-map)

  (bind-key "M-[" 'sr-tabs-prev sr-tabs-mode-map)
  (bind-key "M-]" 'sr-tabs-next sr-tabs-mode-map)

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
  :load-path "site-lisp/swiper"
  :bind ("C-. r" . swiper))

(use-package tablegen-mode
  :mode ("\\.td\\'" . tablegen-mode))

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

(use-package tiny
  :load-path "site-lisp/tiny"
  :bind ("C-. N" . tiny-expand))

(use-package tramp-sh
  :load-path "override/tramp"
  :defer t
  :config
  (add-to-list 'tramp-remote-path "/run/current-system/sw/bin"))

(use-package vkill
  :commands vkill
  :bind ("C-x L" . vkill-and-helm-occur)
  :preface
  (defun vkill-and-helm-occur ()
    (interactive)
    (vkill)
    (call-interactively #'helm-occur))

  :config
  (setq vkill-show-all-processes t))

(use-package wcount
  :disabled t
  :commands wcount-mode)

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
                           (string-match "\\.texi\\'" buffer-file-name))))
        (add-hook 'write-contents-hooks
                  #'(lambda () (ignore (whitespace-cleanup))) nil t)
        (whitespace-cleanup))))

  :init
  (add-hook 'find-file-hooks 'maybe-turn-on-whitespace t)

  :config
  (remove-hook 'find-file-hooks 'whitespace-buffer)
  (remove-hook 'kill-buffer-hook 'whitespace-buffer)

  ;; For some reason, having these in settings.el gets ignored if whitespace
  ;; loads lazily.
  (setq whitespace-auto-cleanup t
        whitespace-line-column 80
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

(use-package workgroups
  :load-path "site-lisp/workgroups"
  :diminish workgroups-mode
  :bind-keymap ("C-\\" . wg-map)
  :config
  (workgroups-mode 1)

  (let ((workgroups-file (expand-file-name "workgroups" user-data-directory)))
    (if (file-readable-p workgroups-file)
        (wg-load workgroups-file)))

  (bind-key "C-\\" 'wg-switch-to-previous-workgroup wg-map)
  (bind-key "\\" 'toggle-input-method wg-map))

(use-package wrap-region
  :load-path "site-lisp/wrap-region"
  :commands wrap-region-mode
  :diminish wrap-region-mode
  :config
  (wrap-region-add-wrappers
   '(("$" "$")
     ("/" "/" nil ruby-mode)
     ("/* " " */" "#" (java-mode javascript-mode css-mode c-mode c++-mode))
     ("`" "`" nil (markdown-mode ruby-mode shell-script-mode)))))

(use-package yaml-mode
  :load-path "site-lisp/yaml-mode"
  :mode ("\\.ya?ml\\'" . yaml-mode))

(use-package yasnippet
  :load-path "site-lisp/yasnippet"
  :diminish yas-minor-mode
  :commands (yas-expand yas-minor-mode)
  :functions (yas-guess-snippet-directories yas-table-name)
  :defines (yas-guessed-modes)
  :mode ("/\\.emacs\\.d/snippets/" . snippet-mode)
  :bind (("C-c y TAB" . yas-expand)
         ("C-c y s"   . yas-insert-snippet)
         ("C-c y n"   . yas-new-snippet)
         ("C-c y v"   . yas-visit-snippet-file))
  :preface
  (defun yas-new-snippet (&optional choose-instead-of-guess)
    (interactive "P")
    (let ((guessed-directories (yas-guess-snippet-directories)))
      (switch-to-buffer "*new snippet*")
      (erase-buffer)
      (kill-all-local-variables)
      (snippet-mode)
      (set (make-local-variable 'yas-guessed-modes)
           (mapcar #'(lambda (d)
                       (intern (yas-table-name (car d))))
                   guessed-directories))
      (unless (and choose-instead-of-guess
                   (not (y-or-n-p "Insert a snippet with useful headers? ")))
        (yas-expand-snippet
         (concat "\n"
                 "# -*- mode: snippet -*-\n"
                 "# name: $1\n"
                 "# --\n"
                 "$0\n")))))

  :config
  (yas-load-directory "~/.emacs.d/snippets/")

  (bind-key "C-i" 'yas-next-field-or-maybe-expand yas-keymap))

(use-package yaoddmuse
  :bind (("C-c w f" . yaoddmuse-browse-page-default)
         ("C-c w e" . yaoddmuse-edit-default)
         ("C-c w p" . yaoddmuse-post-library-default)))

(use-package zencoding-mode
  :disabled t
  :load-path "site-lisp/zencoding-mode"
  :commands zencoding-mode
  :init
  (add-hook 'nxml-mode-hook 'zencoding-mode)
  (add-hook 'html-mode-hook 'zencoding-mode)
  (add-hook 'html-mode-hook
            #'(lambda ()
                (bind-key "<return>" 'newline-and-indent html-mode-map)))

  :config
  (defvar zencoding-mode-keymap (make-sparse-keymap))
  (bind-key "C-c C-c" 'zencoding-expand-line zencoding-mode-keymap))

;;; Post initialization

(when window-system
  (let ((elapsed (float-time (time-subtract (current-time)
                                            emacs-start-time))))
    (message "Loading %s...done (%.3fs)" load-file-name elapsed))

  (add-hook 'after-init-hook
            `(lambda ()
               (let ((elapsed (float-time (time-subtract (current-time)
                                                         emacs-start-time))))
                 (message "Loading %s...done (%.3fs) [after-init]"
                          ,load-file-name elapsed)))
            t))

;;; init.el ends here
