;;;_. Initialization

(eval-when-compile (require 'cl))

(setq message-log-max 16384)

(defconst emacs-start-time (current-time))

(unless noninteractive
  (message "Loading %s..." load-file-name))

(load (expand-file-name "load-path" (file-name-directory load-file-name)))

(eval-when-compile
  ;; (defvar use-package-verbose t)
  ;; (defvar use-package-expand-minimally t)
  (require 'use-package))
(require 'diminish)
(require 'bind-key)

;;;_ , Utility macros and functions

(defmacro hook-into-modes (func modes)
  `(dolist (mode-hook ,modes)
     (add-hook mode-hook ,func)))

(defun system-idle-time ()
  (with-temp-buffer
    (call-process "ioreg" nil (current-buffer) nil
                  "-c" "IOHIDSystem" "-d" "4" "-S")
    (goto-char (point-min))
    (and (re-search-forward "\"HIDIdleTime\" = \\([0-9]+\\)" nil t)
         (/ (float (string-to-number (match-string 1)))
            1000000000.0))))

;; (defun cleanup-term-log ()
;;   "Do not show ^M in files containing mixed UNIX and DOS line endings."
;;   (interactive)
;;   (require 'ansi-color)
;;   (ansi-color-apply-on-region (point-min) (point-max))
;;   (goto-char (point-min))
;;   (while (re-search-forward "\\(.\\|$\\|P.+\\\\\n\\)" nil t)
;;     (overlay-put (make-overlay (match-beginning 0) (match-end 0))
;;                  'invisible t))
;;   (set-buffer-modified-p nil))

;; (add-hook 'find-file-hooks
;;           (function
;;            (lambda ()
;;              (if (string-match "/\\.iTerm/.*\\.log\\'"
;;                                (buffer-file-name))
;;                  (cleanup-term-log)))))

;;;_ , Read system environment

(defun read-system-environment ()
  (let ((plist (expand-file-name "~/.MacOSX/environment.plist")))
    (when (file-readable-p plist)
      (let ((dict (cdr (assq 'dict (cdar (xml-parse-file plist))))))
        (while dict
          (if (and (listp (car dict))
                   (eq 'key (caar dict)))
              (setenv (car (cddr (car dict)))
                      (car (cddr (car (cddr dict))))))
          (setq dict (cdr dict))))

      ;; Configure exec-path based on the new PATH
      (setq exec-path nil)
      (mapc (apply-partially #'add-to-list 'exec-path)
            (nreverse (split-string (getenv "PATH") ":"))))))

(unless (string-match "/nix/store" (getenv "PATH"))
  (read-system-environment)
  (add-hook 'after-init-hook 'read-system-environment))

;;;_ , Load customization settings

(defvar running-alternate-emacs nil)

(if (string-match (concat "Emacs\\([A-Za-z]+\\).app/Contents/MacOS/")
                  invocation-directory)

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

        (eval settings)))

  (load (expand-file-name "settings" user-emacs-directory)))

;;;_ , Enable disabled commands

(put 'downcase-region  'disabled nil)   ; Let downcasing work
(put 'erase-buffer     'disabled nil)
(put 'eval-expression  'disabled nil)   ; Let ESC-ESC work
(put 'narrow-to-page   'disabled nil)   ; Let narrowing work
(put 'narrow-to-region 'disabled nil)   ; Let narrowing work
(put 'set-goal-column  'disabled nil)
(put 'upcase-region    'disabled nil)   ; Let upcasing work

;;;_. Keybindings

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

;;;_ , global-map

;;;_  . C-

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

;;;_  . M-

(defadvice async-shell-command (before uniqify-running-shell-command activate)
  (let ((buf (get-buffer "*Async Shell Command*")))
    (if buf
        (let ((proc (get-buffer-process buf)))
          (if (and proc (eq 'run (process-status proc)))
              (with-current-buffer buf
                (rename-uniquely)))))))

(bind-key "M-!" 'async-shell-command)
(bind-key "M-/" 'dabbrev-expand)
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
(bind-key "M-H" 'mark-paragraph)
(bind-key "M-D" 'mark-defun)

(bind-key "M-g c" 'goto-char)
(bind-key "M-g l" 'goto-line)

(defun delete-indentation-forward ()
  (interactive)
  (delete-indentation t))

;;;(bind-key "M-s n" 'find-name-dired)
;;;(bind-key "M-s o" 'occur)

;;;_  . M-C-

(bind-key "<C-M-backspace>" 'backward-kill-sexp)

;;;_  . A-

(define-key key-translation-map (kbd "A-TAB") (kbd "C-TAB"))

;;;_ , ctl-x-map

;;;_  . C-x

(bind-key "C-x B" 'ido-switch-buffer-other-window)
(bind-key "C-x d" 'delete-whitespace-rectangle)
(bind-key "C-x F" 'set-fill-column)
(bind-key "C-x t" 'toggle-truncate-lines)

;;;_  . C-x C-

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

;;;_  . C-x M-

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

;;;_ , mode-specific-map

;;;_  . C-c

(bind-key "C-c <tab>" 'ff-find-other-file)
(bind-key "C-c SPC" 'just-one-space)

;; inspired by Erik Naggum's `recursive-edit-with-single-window'
(defmacro recursive-edit-preserving-window-config (body)
  "*Return a command that enters a recursive edit after executing BODY.
 Upon exiting the recursive edit (with\\[exit-recursive-edit] (exit)
 or \\[abort-recursive-edit] (abort)), restore window configuration
 in current frame."
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

(bind-key "C-c c" 'compile)

(defun delete-current-line (&optional arg)
  (interactive "p")
  (let ((here (point)))
    (beginning-of-line)
    (kill-line arg)
    (goto-char here)))

(bind-key "C-c d" 'delete-current-line)

(bind-key "C-c e E" 'elint-current-buffer)

(defun do-eval-buffer ()
  (interactive)
  (call-interactively 'eval-buffer)
  (message "Buffer has been evaluated"))

(bind-key "C-c e b" 'do-eval-buffer)
(bind-key "C-c e c" 'cancel-debug-on-entry)
(bind-key "C-c e d" 'debug-on-entry)
(bind-key "C-c e e" 'toggle-debug-on-error)
(bind-key "C-c e f" 'emacs-lisp-byte-compile-and-load)
(bind-key "C-c e j" 'emacs-lisp-mode)
(bind-key "C-c e l" 'find-library)
(bind-key "C-c e r" 'eval-region)
(bind-key "C-c e s" 'scratch)
(bind-key "C-c e z" 'byte-recompile-directory)

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
    (cond ((= width 2560) 'retina-imac)
          ((= width 1440) 'retina-macbook-pro))))

(if running-alternate-emacs
    (progn
      (defun emacs-min-top () 22)
      (defun emacs-min-left () 5)
      (defvar emacs-min-height 57)
      (defvar emacs-min-width 90))

  (defun emacs-min-top () 23)
  (defun emacs-min-left ()
    (cond ((eq display-name 'retina-imac) 975)
          (t 521)))
  (defvar emacs-min-height
    (cond ((eq display-name 'retina-imac) 55)
          (t 44)))
  (defvar emacs-min-width 100))

(defvar emacs-min-font
  (cond
   ((eq display-name 'retina-imac)
    (if running-alternate-emacs
        "-*-Myriad Pro-normal-normal-normal-*-20-*-*-*-p-0-iso10646-1"
      "-*-Source Code Pro-normal-normal-normal-*-20-*-*-*-m-0-iso10646-1"))
   (t
    (if running-alternate-emacs
        "-*-Myriad Pro-normal-normal-normal-*-17-*-*-*-p-0-iso10646-1"
      "-*-Source Code Pro-normal-normal-normal-*-15-*-*-*-m-0-iso10646-1"))))

(let ((frame-alist
       (list (cons 'top (emacs-min-top))
             (cons 'left (emacs-min-left))
             (cons 'height emacs-min-height)
             (cons 'width emacs-min-width)
             (cons 'font emacs-min-font))))
  (setq initial-frame-alist frame-alist))

(defun emacs-min ()
  (interactive)

  (set-frame-parameter (selected-frame) 'fullscreen nil)
  (set-frame-parameter (selected-frame) 'vertical-scroll-bars nil)
  (set-frame-parameter (selected-frame) 'horizontal-scroll-bars nil)

  (set-frame-parameter (selected-frame) 'top (emacs-min-top))
  (set-frame-parameter (selected-frame) 'left (emacs-min-left))
  (set-frame-parameter (selected-frame) 'height emacs-min-height)
  (set-frame-parameter (selected-frame) 'width emacs-min-width)

  (set-frame-font emacs-min-font)

  (when running-alternate-emacs
    (set-background-color "grey85")
    (set-face-background 'fringe "gray80")))

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

;;;_  . C-c C-

(defun delete-to-end-of-buffer ()
  (interactive)
  (kill-region (point) (point-max)))

(bind-key "C-c C-z" 'delete-to-end-of-buffer)

;;;_  . C-c M-

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

;;;_ , ctl-period-map

;;;_  . C-.

(bind-key "C-. m" 'kmacro-keymap)

(bind-key "C-. C-i" 'indent-rigidly)

;;;_ , help-map

(defvar lisp-find-map)
(define-prefix-command 'lisp-find-map)

(bind-key "C-h e" 'lisp-find-map)

;;;_  . C-h e

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

;;;_. Packages

;;;_ , cc-mode

(eval-when-compile
  (defvar yas-fallback-behavior))

(use-package cc-mode
  :mode (("\\.h\\(h?\\|xx\\|pp\\)\\'" . c++-mode)
         ("\\.m\\'"                   . c-mode)
         ("\\.mm\\'"                  . c++-mode))
  :init
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
    (gtags-mode 1)
    (hs-minor-mode 1)
    (hide-ifdef-mode 1)
    (whitespace-mode 1)
    (which-function-mode 1)
    ;; (auto-complete-mode 1)
    (yas-minor-mode 1)
    (bug-reference-prog-mode 1)

    (diminish 'gtags-mode)
    (diminish 'hs-minor-mode)
    (diminish 'hide-ifdef-mode)

    (bind-key "C-c p" 'insert-counting-printf c-mode-base-map)

    ;; (setq ac-sources (list 'ac-source-gtags))
    ;; (bind-key "<A-tab>" 'ac-complete c-mode-base-map)

    ;;(doxymacs-mode 1)
    ;;(doxymacs-font-lock)

    (bind-key "<return>" 'newline-and-indent c-mode-base-map)

    ;; (set (make-local-variable 'yas-fallback-behavior)
    ;;      '(apply my-c-indent-or-complete . nil))
    ;; (bind-key "<tab>" 'yas-expand-from-trigger-key c-mode-base-map)

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

  (add-hook 'c-mode-common-hook 'my-c-mode-common-hook)

  :config
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

;;;_ , abbrev

(use-package abbrev
  :disabled t
  :commands abbrev-mode
  :diminish abbrev-mode
  :init
  (hook-into-modes #'abbrev-mode '(text-mode-hook))

  :config
  (if (file-exists-p abbrev-file-name)
      (quietly-read-abbrev-file))

  (add-hook 'expand-load-hook
            (lambda ()
              (add-hook 'expand-expand-hook 'indent-according-to-mode)
              (add-hook 'expand-jump-hook 'indent-according-to-mode))))

;;;_ , ace-jump-mode

(use-package ace-jump-mode
  :bind ("M-h" . ace-jump-mode)
  :config
  (setq ace-jump-mode-submode-list
        '(ace-jump-char-mode
          ace-jump-word-mode
          ace-jump-line-mode)))

;;;_ , ace-isearch

(use-package ace-isearch
  :disabled t
  :config
  (global-ace-isearch-mode 1))

;;;_ , ag

(use-package ag
  :commands (ag ag-regexp)
  :init
  (use-package helm-ag
    :commands helm-ag))

;;;_ , agda

(eval-and-compile
  (defun agda-site-lisp ()
    (let ((agda
           (nth 1 (split-string
                   (shell-command-to-string "load-env-agda which agda")
                   "\n"))))
      (and agda
           (expand-file-name
            "../share/x86_64-osx-ghc-7.8.4/Agda-2.4.2.2/emacs-mode"
            (file-name-directory agda))))))

(use-package agda2-mode
  :mode "\\.agda\\'"
  :load-path (lambda () (list (agda-site-lisp)))
  :defines agda2-mode-map
  :init
  (use-package agda-input)
  :config
  (defun agda2-insert-helper-function (&optional prefix)
    (interactive "P")
    (let ((func-def (with-current-buffer "*Agda information*"
                      (buffer-string))))
      (save-excursion
        (forward-paragraph)
        (let ((name (car (split-string func-def " "))))
          (insert "  where\n    " func-def "    " name " x = ?\n")))))

  (bind-key "C-c C-i" 'agda2-insert-helper-function agda2-mode-map))

(defun char-mapping (key char)
  (bind-key key `(lambda () (interactive) (insert ,char))))

(char-mapping "A-G" "Γ")
(char-mapping "A-l" "λ x → ")
(char-mapping "A-:" " ∷ ")
(char-mapping "A-r" " → ")
(char-mapping "A-~" " ≅ ")
(char-mapping "A-=" " ≡ ")

;;;_ , alert

(use-package alert)

;;;_ , allout

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

;;;_ , archive-region

(use-package archive-region
  :disabled t
  :bind ("C-w" . kill-region-or-archive-region))

;;;_ , ascii

(use-package ascii
  :bind ("C-c e A" . ascii-toggle)
  :commands ascii-on
  :init
  (defun ascii-toggle ()
    (interactive)
    (if ascii-display
        (ascii-off)
      (ascii-on))))

;;;_ , auctex

(use-package tex-site
  :disabled t
  :load-path "site-lisp/auctex/preview/"
  :defines (latex-help-cmd-alist latex-help-file)
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

  (use-package latex-mode
    :defer t
    :config
    (progn
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
                                        ("(latex2e)Command Index"))))))

;;;_ , auto-complete

(use-package auto-complete-config
  :disabled t
  :diminish auto-complete-mode
  :init
  (use-package pos-tip)
  (ac-config-default)

  :config
  ;;(ac-set-trigger-key "TAB")
  (ac-set-trigger-key "<backtab>")
  (setq ac-use-menu-map t)

  (bind-key "A-M-?" 'ac-last-help)
  (unbind-key "C-s" ac-completing-map))

;;;_ , autopair

(use-package autopair
  :disabled t
  :commands autopair-mode
  :diminish autopair-mode
  :init
  (hook-into-modes #'autopair-mode '(c-mode-common-hook
                                     text-mode-hook
                                     ruby-mode-hook
                                     python-mode-hook
                                     sh-mode-hook)))

;;;_ , autorevert

(use-package autorevert
  :commands auto-revert-mode
  :diminish auto-revert-mode
  :init
  (add-hook 'find-file-hook #'(lambda () (auto-revert-mode 1))))

;;;_ , backup-each-save

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

(use-package backup-each-save
  :commands backup-each-save
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

;;;_ , bbdb

(use-package bbdb-com
  :commands bbdb-create
  :bind ("M-B" . bbdb))

;;;_ , bm

(use-package bm
  :disabled t
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

;;;_ , bookmark

(use-package bookmark
  :config
  (use-package bookmark+))

;;;_ , browse-kill-ring+

(use-package browse-kill-ring+)

;;;_ , cmake-mode

(use-package cmake-mode
  :mode (("CMakeLists\\.txt\\'" . cmake-mode)
         ("\\.cmake\\'"         . cmake-mode)))

;;;_ , compile

(defun find-directory (dir name)
  (catch 'file
    (let ((files
           (delete
            nil
            (mapcar
             (lambda (entry)
               (and (not (string-match
                          "\\`\\." (file-name-nondirectory entry)))
                    (file-directory-p entry)
                    entry))
             (directory-files dir t)))))
      (dolist (file files)
        (if (string= (file-name-nondirectory file) name)
            (throw 'file file)))
      (dolist (file files)
        (let ((result (find-directory file name)))
          (if result (throw 'file result)))))))

(use-package compile
  :defer t
  :config
  (defun cmake-project-filename ()
    (let ((filename (match-string-no-properties 1)))
      (save-match-data
        (with-temp-buffer
          (insert-file-contents-literally "cmake_install.cmake")
          (goto-char (point-min))
          (re-search-forward "Install script for directory: \\(.+\\)")
          (cons filename (match-string-no-properties 1))))))

  (push 'cmake compilation-error-regexp-alist)

  (push '(cmake "^CMake Error at \\(.+?\\):\\([0-9]+\\)"
                (cmake-project-filename) 2 2 2)
        compilation-error-regexp-alist-alist)

  (push '(cmake "^\\(?:CMake Error at \\|  \\)\\(.+?\\):\\([0-9]+\\) ([A-Za-z_][A-Za-z0-9_]*)"
                (cmake-project-filename) 2)
        compilation-error-regexp-alist-alist)

  (defun ghc-project-filename ()
    (let ((filename (match-string-no-properties 1)))
      (save-excursion
        (goto-char (point-min))
        (if (re-search-forward "^Building \\(.+?\\)-[0-9]" nil t)
            (cons filename (find-directory default-directory
                                           (match-string 1)))))))

  ;; (push 'ghc compilation-error-regexp-alist)

  ;; (push '(ghc "^\\(.+?\\.hs\\):\\([0-9]+\\):\\([0-9]+\\):"
  ;;             (ghc-project-filename) 2 3)
  ;;       compilation-error-regexp-alist-alist)

  (eval-when-compile
    (defvar exit-status))
  (add-hook 'compilation-finish-functions
            #'(lambda (buf why)
                (display-buffer buf)
                (if (> exit-status 0)
                    (alert "Compilation finished with errors"
                           :buffer buf :severity 'high)
                  (alert "Compilation finished" :buffer buf)))))

;;;_ , color-moccur

(let ((ad-redefinition-action 'accept))
  (use-package color-moccur
    :commands (isearch-moccur isearch-all)
    :bind ("M-s O" . moccur)
    :init
    (bind-key "M-o" 'isearch-moccur isearch-mode-map)
    (bind-key "M-O" 'isearch-moccur-all isearch-mode-map)
    :config
    (use-package moccur-edit)))

;;;_ , company-mode

(use-package company
  :diminish company-mode
  :config
  (global-company-mode t))

;;;_ , copy-code

(use-package copy-code
  :disabled t
  :bind ("A-M-W" . copy-code-as-rtf))

;;;_ , crosshairs

(use-package crosshairs
  :bind ("M-o c" . crosshairs-mode))

;;;_ , css-mode

(use-package css-mode
  :mode ("\\.css\\'" . css-mode))

;;;_ , cursor-chg

(use-package cursor-chg
  :config
  (change-cursor-mode 1)
  (toggle-cursor-type-when-idle 1))

;;;_ , debbugs

(use-package debbugs-gnu
  :disabled t
  :commands (debbugs-gnu debbugs-gnu-search))

;;;_ , dedicated

(use-package dedicated
  :bind ("C-. d" . dedicated-mode))

;;;_ , diff-mode

(use-package diff-mode
  :commands diff-mode
  :config
  (use-package diff-mode-))

;;;_ , dired

(use-package dired
  :defer t
  :init
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

  :config
  (defun dired-package-initialize ()
    (unless (featurep 'runner)
      (use-package dired-x)
      ;; (use-package dired-async)
      ;; (use-package dired-sort-map)
      (use-package runner)
      (use-package dired+)

      (bind-key "l" 'dired-up-directory dired-mode-map)

      (defun my-dired-switch-window ()
        (interactive)
        (if (eq major-mode 'sr-mode)
            (call-interactively #'sr-change-window)
          (call-interactively #'other-window)))

      (bind-key "<tab>" 'my-dired-switch-window dired-mode-map)

      (bind-key "M-!" 'async-shell-command dired-mode-map)
      (unbind-key "M-G" dired-mode-map)
      (unbind-key "M-s f" dired-mode-map)

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
            (funcall dired-omit-regexp-orig))))))

  (add-hook 'dired-mode-hook 'dired-package-initialize)

  (defun dired-double-jump (first-dir second-dir)
    (interactive
     (list (ido-read-directory-name "First directory: "
                                    (expand-file-name "~")
                                    nil nil "dl/")
           (ido-read-directory-name "Second directory: "
                                    (expand-file-name "~")
                                    nil nil "Archives/")))
    (dired first-dir)
    (dired-other-window second-dir))

  (bind-key "C-c J" 'dired-double-jump))

;;;_ , doxymacs

(use-package doxymacs
  :disabled t
  :load-path "site-lisp/doxymacs/lisp/")

;;;_ , eclim

(use-package eclim
  :defer t
  :config
  (global-eclim-mode)
  (use-package company-emacs-eclim
    :requires company
    :config
    (company-emacs-eclim-setup)))

(use-package eclimd
  :commands start-eclimd)

;;;_ , ediff

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

;;;_ , edit-server

(use-package edit-server
  :disabled t
  :if (and window-system
           (not running-alternate-emacs)
           (not noninteractive))
  :load-path "site-lisp/emacs_chrome/servers/"
  :init
  (add-hook 'after-init-hook 'server-start t)
  (add-hook 'after-init-hook 'edit-server-start t))

;;;_ , edit-var

(use-package edit-var
  :bind ("C-c e v" . edit-variable))

;;;_ , emms

(use-package emms-setup
  :disabled t
  :load-path "site-lisp/emms/lisp"
  :defines emms-info-functions
  :commands (emms-all emms-devel)
  :bind ("C-. M" . my-emms)
  :init
  (defvar emms-initialized nil)

  (defun my-emms ()
    (interactive)
    (unless emms-initialized
      (emms-devel)
      (emms-default-players)
      (require 'emms-info-libtag)
      (setq emms-info-functions '(emms-info-libtag))
      (setq emms-initialized t))
    (call-interactively #'emms-smart-browse))

  :config
  (bind-key "S-<f7>" 'emms-previous)
  (bind-key "S-<f8>" 'emms-pause)
  (bind-key "S-<f9>" 'emms-next)
  (bind-key "S-<f10>" 'emms-stop)

  (defun emms-player-mplayer-volume-up ()
    "Depends on mplayer’s -slave mode."
    (interactive)
    (process-send-string
     emms-player-simple-process-name "volume 1\n"))

  (defun emms-player-mplayer-volume-down ()
    "Depends on mplayer’s -slave mode."
    (interactive)
    (process-send-string
     emms-player-simple-process-name "volume -1\n"))

  (bind-key "C-. C--" 'emms-player-mplayer-volume-down)
  (bind-key "C-. C-=" 'emms-player-mplayer-volume-up))

;;;_ , erc

(defun lookup-password (host user port)
  (require 'auth-source)
  (funcall (plist-get
            (car (auth-source-search
                  :host host
                  :user user
                  :type 'netrc
                  :port port))
            :secret)))

(defun irc ()
  (interactive)
  (if (slowping "192.168.9.133")
      (progn
        (erc :server "192.168.9.133"
             :port 6697
             :nick "johnw"
             :password (lookup-password "192.168.9.133" "johnw/freenode" 6697))
        (erc :server "192.168.9.133"
             :port 6697
             :nick "johnw"
             :password (lookup-password "192.168.9.133" "johnw/bitlbee" 6697)))

    (erc-tls :server "irc.freenode.net"
             :port 6697
             :nick "johnw"
             :password (lookup-password "irc.freenode.net" "johnw" 6667))))

(eval-when-compile
  (defvar erc-timestamp-only-if-changed-flag)
  (defvar erc-timestamp-format)
  (defvar erc-fill-prefix)
  (defvar erc-fill-column)
  (defvar erc-insert-timestamp-function)
  (defvar erc-modified-channels-alist))

(defun setup-irc-environment ()
  (custom-set-faces
   '(erc-timestamp-face ((t (:foreground "dark violet")))))

  (setq erc-timestamp-only-if-changed-flag nil
        erc-timestamp-format "%H:%M "
        erc-fill-prefix "          "
        erc-fill-column 88
        erc-insert-timestamp-function 'erc-insert-timestamp-left)

  (set-input-method "Agda")

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

(use-package erc
  :if running-alternate-emacs
  :defer t
  :init
  (add-hook 'erc-mode-hook 'setup-irc-environment)
  (add-hook 'after-init-hook 'irc)

  :config
  (erc-track-minor-mode 1)
  (erc-track-mode 1)

  (use-package erc-alert)
  (use-package erc-highlight-nicknames)
  (use-package erc-patch)
  (use-package erc-macros)

  (use-package erc-yank
    :init
    (bind-key "C-y" 'erc-yank erc-mode-map))

  (use-package wtf
    :commands wtf-is)

  (add-hook 'erc-insert-pre-hook
            (lambda (s)
              (when (erc-foolish-content s)
                (setq erc-insert-this nil)))))

;;;_ , eshell

(defvar eshell-isearch-map
  (let ((map (copy-keymap isearch-mode-map)))
    (define-key map [(control ?m)] 'eshell-isearch-return)
    (define-key map [return] 'eshell-isearch-return)
    (define-key map [(control ?r)] 'eshell-isearch-repeat-backward)
    (define-key map [(control ?s)] 'eshell-isearch-repeat-forward)
    (define-key map [(control ?g)] 'eshell-isearch-abort)
    (define-key map [backspace] 'eshell-isearch-delete-char)
    (define-key map [delete] 'eshell-isearch-delete-char)
    map)
  "Keymap used in isearch in Eshell.")

(use-package eshell
  :commands (eshell eshell-command)
  :config
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

    (eval-after-load "em-unix"
      '(progn
         (unintern 'eshell/su nil)
         (unintern 'eshell/sudo nil))))

  (add-hook 'eshell-first-time-mode-hook 'eshell-initialize))

(use-package esh-toggle
  :requires eshell
  :bind ("C-x C-z" . eshell-toggle))

;;;_ , ess

(use-package ess-site
  :disabled t
  :load-path "site-lisp/ess/lisp/"
  :commands R)

;;;_ , eval-expr

(use-package eval-expr
  :bind ("M-:" . eval-expr)
  :config
  (setq eval-expr-print-function 'pp
        eval-expr-print-level 20
        eval-expr-print-length 100)

  (defun eval-expr-minibuffer-setup ()
    (set-syntax-table emacs-lisp-mode-syntax-table)
    (paredit-mode)))

;;;_ , eww

;; (use-package eww
;;   :bind ("A-M-g" . eww)
;;   :config
;;   (use-package eww-lnum
;;     :config
;;     (bind-key "f" 'eww-lnum-follow eww-mode-map)
;;     (bind-key "F" 'eww-lnum-universal eww-mode-map)))

;;;_ , fetchmail-mode

(use-package fetchmail-mode
  :commands fetchmail-mode)

;;;_ , flycheck

(use-package flycheck
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

;;;_ , flyspell

(use-package ispell
  :bind (("C-c i c" . ispell-comments-and-strings)
         ("C-c i d" . ispell-change-dictionary)
         ("C-c i k" . ispell-kill-ispell)
         ("C-c i m" . ispell-message)
         ("C-c i r" . ispell-region)))

(use-package flyspell
  :bind (("C-c i b" . flyspell-buffer)
         ("C-c i f" . flyspell-mode))
  :config
  (define-key flyspell-mode-map [(control ?.)] nil))

;;;_ , gist

(use-package gist
  :bind ("C-c G" . gist-region-or-buffer))

;;;_ , git-blame

(use-package git-blame
  :commands git-blame-mode)

;;;_ , git-messenger

(use-package git-messenger
  :bind ("C-x v m" . git-messenger:popup-message))

;;;_ , git-wip

(use-package git-wip-mode
  :disabled t
  :load-path "site-lisp/git-wip/emacs/"
  :demand t
  :diminish git-wip-mode)

;;;_ , gnus

(use-package dot-gnus
  :bind (("M-G"   . switch-to-gnus)
         ("C-x m" . compose-mail))
  :init
  (setq gnus-init-file (expand-file-name "dot-gnus" user-emacs-directory)
        gnus-home-directory "~/Messages/Gnus/"))

;;;_ , grep

(use-package grep
  :disabled t
  :bind (("M-s d" . find-grep-dired)
         ;; ("M-s f" . find-grep)
         ("M-s g" . grep)
         ("M-s p" . find-grep-in-project))
  :init
  (defun find-grep-in-project (command-args)
    (interactive
     (let ((default (thing-at-point 'symbol)))
       (list (read-shell-command "Run find (like this): "
                                 (cons (concat "git --no-pager grep -n "
                                               default)
                                       (+ 24 (length default)))
                                 'grep-find-history))))
    (if command-args
        (let ((null-device nil))      ; see grep
          (grep command-args))))

  :config
  (use-package grep-ed)
  (grep-apply-setting 'grep-command "egrep -nH -e ")
  (if t
      (progn
        (setq-default grep-first-column 1)
        (grep-apply-setting
         'grep-find-command
         '("ag --noheading --nocolor --smart-case --nogroup --column -- "
           . 61)))
    (grep-apply-setting
     'grep-find-command
     '("find . -name '*.hs' -type f -print0 | xargs -P4 -0 egrep -nH "
       . 62))))

;;;_ , gtags

(use-package gtags
  :commands gtags-mode
  :diminish gtags-mode
  :config
  (bind-key "C-c t ." 'gtags-find-rtag)
  (bind-key "C-c t f" 'gtags-find-file)
  (bind-key "C-c t p" 'gtags-parse-file)
  (bind-key "C-c t g" 'gtags-find-with-grep)
  (bind-key "C-c t i" 'gtags-find-with-idutils)
  (bind-key "C-c t s" 'gtags-find-symbol)
  (bind-key "C-c t r" 'gtags-find-rtag)
  (bind-key "C-c t v" 'gtags-visit-rootdir)

  (bind-key "<mouse-2>" 'gtags-find-tag-from-here gtags-mode-map)

  (use-package helm-gtags
    :bind ("M-T" . helm-gtags-select)
    :config
    (bind-key "M-," 'helm-gtags-resume gtags-mode-map)))

;;;_ , gud

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

;;;_ , guide-key

(use-package guide-key
  :diminish guide-key-mode
  :config
  (setq guide-key/guide-key-sequence
        '("C-x r" "C-x 4" "C-x 5" "C-h e" "C-." "M-s" "M-o"))
  (guide-key-mode 1))

;;;_ , haskell-mode

(use-package haskell-config
  :mode ("\\.l?hs\\'" . haskell-mode))

(defun snippet (name)
  (interactive "sName: ")
  (find-file (expand-file-name (concat name ".hs") "~/src/notes"))
  (haskell-mode)
  (goto-char (point-min))
  (when (eobp)
    (insert "hdr")
    (yas-expand)))

;;;_ , helm

(use-package helm-config
  :demand t
  :commands (helm-do-grep-1 helm-find helm--completing-read-default)
  :bind (("C-c h"   . helm-command-prefix)
         ("C-h a"   . helm-apropos)
         ("C-h e a" . my-helm-apropos)
         ("C-x f"   . helm-multi-files)
         ;; ("C-x C-f" . helm-find-files)
         ("M-s F"   . helm-for-files)
         ("M-s b"   . helm-occur)
         ("M-s f"   . my-helm-do-grep-r)
         ("M-s g"   . my-helm-do-grep)
         ("M-s n"   . my-helm-find)
         ("M-s o"   . helm-swoop)
         ("M-s /"   . helm-multi-swoop))

  :preface
  (defun my-helm-do-grep ()
    (interactive)
    (helm-do-grep-1 (list default-directory)))

  (defun my-helm-do-grep-r ()
    (interactive)
    (helm-do-grep-1 (list default-directory) t))

  (defun my-helm-find ()
    (interactive)
    (helm-find nil))

  (defvar helm-swoop-last-prefix-number)

  :config
  (use-package helm-commands)
  (use-package helm-files)
  (use-package helm-buffers)
  (use-package helm-grep)
  (use-package helm-ls-git)
  (use-package helm-match-plugin)
  (use-package helm-swoop)
  ;; (use-package helm-mode)

  (use-package helm-descbinds
    :bind ("C-h b" . helm-descbinds)
    :init
    (fset 'describe-bindings 'helm-descbinds))

  (helm-match-plugin-mode t)
  (helm-autoresize-mode t)

  (bind-key "<tab>" 'helm-execute-persistent-action helm-map)
  (bind-key "C-i" 'helm-execute-persistent-action helm-map)
  (bind-key "C-z" 'helm-select-action helm-map)
  (bind-key "A-v" 'helm-previous-page helm-map)

  (when (executable-find "curl")
    (setq helm-google-suggest-use-curl-p t)))

;; (use-package helm-ls-git
;;   :bind ("C-x f" . helm-ls-git-ls))

;;;_ , hi-lock

(use-package hi-lock
  :bind (("M-o l" . highlight-lines-matching-regexp)
         ("M-o r" . highlight-regexp)
         ("M-o w" . highlight-phrase)))

;;;_ , hilit-chg

(use-package hilit-chg
  :bind ("M-o C" . highlight-changes-mode))

;;;_ , hl-line

(use-package hl-line
  :commands hl-line-mode
  :bind (("M-o h" . hl-line-mode))
  :config
  (use-package hl-line+))

;;;_ , ibuffer

(use-package ibuffer
  :bind ("C-x C-b" . ibuffer)
  :init
  (add-hook 'ibuffer-mode-hook
            #'(lambda ()
                (ibuffer-switch-to-saved-filter-groups "default"))))

;;;_ , ido

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

(use-package ido
  :defines (ido-cur-item
            ido-require-match
            ido-selected
            ido-final-text
            ido-show-confirm-message)
  :config
  (ido-mode 'buffer)

  (use-package ido-hacks
    :config
    (ido-hacks-mode 1))

  (use-package flx-ido
    :disabled t
    :config
    (flx-ido-mode 1))

  (add-hook 'ido-minibuffer-setup-hook
            #'(lambda ()
                (bind-key "<return>" 'ido-smart-select-text
                          ido-file-completion-map))))

;;;_ , idris

(use-package idris-mode
  :disabled t
  :mode ("\\.idr\\'" . idris-mode)
  :config
  (defadvice idris-load-file (around my-idris-load-file activate)
    (let ((wind (selected-window)))
      ad-do-it
      (select-window wind))))

;;;_ , ielm

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

;;;_ , iflipb

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

(use-package iflipb
  :commands (iflipb-next-buffer iflipb-previous-buffer)
  ;; :bind (("M-`"   . my-iflipb-next-buffer)
  ;;        ("M-S-`" . my-iflipb-previous-buffer))
  :config
  (setq iflipb-always-ignore-buffers
        "\\`\\( \\|diary\\|ipa\\|\\.newsrc-dribble\\'\\)"
        iflipb-wrap-around t)

  (defun iflipb-first-iflipb-buffer-switch-command ()
    "Determines whether this is the first invocation of
iflipb-next-buffer or iflipb-previous-buffer this round."
    (not (and (or (eq last-command 'my-iflipb-next-buffer)
                  (eq last-command 'my-iflipb-previous-buffer))
              my-iflipb-ing-internal))))

;;;_ , image-file

(use-package image-file
  :disabled t
  :config
  (auto-image-file-mode 1))

;;;_ , info

(use-package info
  :bind ("C-h C-i" . info-lookup-symbol)
  :init
  (remove-hook 'menu-bar-update-hook 'mac-setup-help-topics)
  :config
  ;; (defadvice info-setup (after load-info+ activate)
  ;;   (use-package info+))

  (defadvice Info-exit (after remove-info-window activate)
    "When info mode is quit, remove the window."
    (if (> (length (window-list)) 1)
        (delete-window))))

(use-package info-look
  :commands info-lookup-add-help)

;;;_ , indirect

(use-package indirect
  :bind ("C-c C" . indirect-region))

;;;_ , initsplit

(use-package initsplit)

;;;_ , ipa

(use-package ipa
  :commands (ipa-insert ipa-load-annotations-into-buffer)
  :init
  (add-hook 'find-file-hook 'ipa-load-annotations-into-buffer))

;;;_ , isearch

(defun isearch-backward-other-window ()
  (interactive)
  (split-window-vertically)
  (call-interactively 'isearch-backward))

(defun isearch-forward-other-window ()
  (interactive)
  (split-window-vertically)
  (call-interactively 'isearch-forward))

(bind-key "C-M-r" 'isearch-backward-other-window)
(bind-key "C-M-s" 'isearch-forward-other-window)

(bind-key "C-c" 'isearch-toggle-case-fold isearch-mode-map)
(bind-key "C-t" 'isearch-toggle-regexp isearch-mode-map)
(bind-key "C-^" 'isearch-edit-string isearch-mode-map)
(bind-key "C-i" 'isearch-complete isearch-mode-map)

;;;_ , js2-mode

(use-package js2-mode
  :mode ("\\.js\\'" . js2-mode))

;;;_ , ledger

(use-package "ledger-mode"
  :load-path "~/src/ledger/lisp/"
  :commands ledger-mode
  :bind ("C-c L" . my-ledger-start-entry)
  :init
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
    (insert (format-time-string "%Y/%m/%d "))))

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

;;;_ , lisp-mode

;; Utilities every Emacs Lisp coder should master:
;;
;;   paredit          Lets you manipulate sexps with ease
;;   redshank         Think: Lisp refactoring
;;   edebug           Knowing the traditional debugger is good too
;;   eldoc
;;   cldoc
;;   elint
;;   elp
;;   ert
;;   ielm

(use-package lisp-mode
  ;; :load-path "site-lisp/slime/contrib/"
  :init
  (defface esk-paren-face
    '((((class color) (background dark))
       (:foreground "grey50"))
      (((class color) (background light))
       (:foreground "grey55")))
    "Face used to dim parentheses."
    :group 'starter-kit-faces)

  ;; Change lambda to an actual lambda symbol
  (mapc (lambda (major-mode)
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

  (defvar slime-mode nil)
  (defvar lisp-mode-initialized nil)

  (defun my-lisp-mode-hook ()
    (unless lisp-mode-initialized
      (setq lisp-mode-initialized t)

      (use-package redshank
        :diminish redshank-mode)

      (use-package elisp-slime-nav
        :diminish elisp-slime-nav-mode)

      (use-package edebug)

      (use-package eldoc
        :diminish eldoc-mode
        :defer t
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
        :diminish cldoc-mode)

      (use-package ert
        :commands ert-run-tests-interactively
        :bind ("C-c e t" . ert-run-tests-interactively))

      (use-package elint
        :commands 'elint-initialize
        :init
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

      ;; Register Info manuals related to Lisp
      (use-package info-lookmore
        :config
        (info-lookmore-elisp-cl)
        (info-lookmore-elisp-userlast)
        (info-lookmore-elisp-gnus)
        (info-lookmore-apropos-elisp))

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

    (if (memq major-mode
              '(emacs-lisp-mode inferior-emacs-lisp-mode ielm-mode))
        (progn
          (bind-key "<M-return>" 'outline-insert-heading emacs-lisp-mode-map)
          (bind-key "<tab>" 'my-elisp-indent-or-complete emacs-lisp-mode-map))
      (turn-on-cldoc-mode)

      (bind-key "<tab>" 'my-lisp-indent-or-complete lisp-mode-map)
      (bind-key "M-q" 'slime-reindent-defun lisp-mode-map)
      (bind-key "M-l" 'slime-selector lisp-mode-map))

    (autoload 'yas-minor-mode "yasnippet")
    (yas-minor-mode 1))

  (hook-into-modes 'my-lisp-mode-hook lisp-mode-hooks))

;;;_ , llvm-mode

(use-package llvm-mode
  :mode ("\\.ll\\'" . llvm-mode))

;;;_ , lua-mode

(use-package lua-mode
  :mode ("\\.lua\\'" . lua-mode)
  :interpreter ("lua" . lua-mode))

;;;_ , lusty-explorer

(use-package lusty-explorer
  :bind ("C-x C-f" . lusty-file-explorer)
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
  (let ((lusty--active-mode :file-explorer))
    (lusty--define-mode-map)
    (let* ((lusty--ignored-extensions-regex
            (concat "\\(?:" (regexp-opt completion-ignored-extensions)
                    "\\)$"))
           (minibuffer-local-filename-completion-map lusty-mode-map)
           (lusty-only-directories nil))
      (lusty--run 'read-file-name default-directory ""))))

;;;_ , macrostep

(use-package macrostep
  :bind ("C-c e m" . macrostep-expand))

;;;_ , magit

(use-package magit
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
  :init
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

  (add-hook 'magit-mode-hook 'hl-line-mode)

  :config
  (setenv "GIT_PAGER" "")

  (use-package magit-backup
    :diminish magit-backup-mode)

  (use-package magit-review
    :disabled t
    :commands magit-review
    :config (require 'json))

  (unbind-key "M-h" magit-mode-map)
  (unbind-key "M-s" magit-mode-map)
  (unbind-key "M-m" magit-mode-map)

  (add-hook 'magit-log-edit-mode-hook
            #'(lambda ()
                (set-fill-column 72)
                (flyspell-mode)))

  (add-hook 'magit-status-mode-hook #'(lambda () (magit-monitor t))))

;;;_ , markdown-mode

(use-package markdown-mode
  :mode (("\\`README\\.md\\'" . gfm-mode)
         ("\\.md\\'"          . markdown-mode)
         ("\\.markdown\\'"    . markdown-mode)))

;;;_ , mudel

(use-package mudel
  :disabled t
  :commands mudel
  :bind ("C-c M" . mud)
  :init
  (defun mud ()
    (interactive)
    (mudel "4dimensions" "4dimensions.org" 6000)))

;;;_ , mule

(eval-when-compile
  (defvar x-select-request-type))

(use-package mule
  :init
  (prefer-coding-system 'utf-8)
  (set-terminal-coding-system 'utf-8)
  (setq x-select-request-type '(UTF8_STRING COMPOUND_TEXT TEXT STRING)))

;;;_ , multi-term

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

;;;_ , multi-term

(use-package multiple-cursors
  :disabled t
  :bind (("C-S-c C-S-c" . mc/edit-lines)
         ("C->"         . mc/mark-next-like-this)
         ("C-<"         . mc/mark-previous-like-this)
         ("C-c C-<"     . mc/mark-all-like-this))
  :config
  (setq mc/list-file (expand-file-name "mc-lists.el" user-data-directory)))

;;;_ , nix-mode

(use-package nix-mode
  :mode ("\\.nix\\'" . nix-mode))

;;;_ , nf-procmail-mode

(use-package nf-procmail-mode
  :commands nf-procmail-mode)

;;;_ , nroff-mode

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

;;;_ , nxml-mode

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

;;;_ , on-screen

(use-package on-screen
  :config
  (on-screen-global-mode 1))

;;;_ , org-mode

(use-package dot-org
  :preface
  (defun my-org-startup ()
    (org-agenda-list)
    (org-fit-agenda-window)
    (org-agenda-to-appt)
    (other-window 1)
    (my-calendar)
    (run-with-idle-timer
     0.1 nil
     (lambda ()
       (let ((wind (get-buffer-window "*Org Agenda*")))
         (when wind
           (set-frame-selected-window nil wind)
           (call-interactively #'org-agenda-redo)))
       (let ((wind (get-buffer-window "*cfw-calendar*")))
         (when wind
           (set-frame-selected-window nil wind)
           (call-interactively #'cfw:refresh-calendar-buffer)))
       (let ((wind (get-buffer-window "*Org Agenda*")))
         (when wind
           (set-frame-selected-window nil wind)
           (call-interactively #'org-resolve-clocks))))))

  :commands org-agenda-list
  :bind (("M-C"   . jump-to-org-agenda)
         ("M-m"   . org-smart-capture)
         ("M-M"   . org-inline-note)
         ("C-c a" . org-agenda)
         ("C-c S" . org-store-link)
         ("C-c l" . org-insert-link)
         ("C-. n" . org-velocity-read))
  :init
  (when (and nil
             (not running-alternate-emacs)
             ;; (quickping "192.168.9.133")
             )
    (run-with-idle-timer 300 t 'jump-to-org-agenda)
    (add-hook 'after-init-hook #'my-org-startup)))

;;;_ , pabbrev

(use-package pabbrev
  :commands pabbrev-mode
  :diminish pabbrev-mode)

;;;_ , paredit

(use-package paredit
  :commands paredit-mode
  :diminish paredit-mode
  :config
  (use-package paredit-ext)

  (bind-key "C-M-l" 'paredit-recentre-on-sexp paredit-mode-map)

  (bind-key ")" 'paredit-close-round-and-newline paredit-mode-map)
  (bind-key "M-)" 'paredit-close-round paredit-mode-map)

  (bind-key "M-k" 'paredit-raise-sexp paredit-mode-map)
  ;; (bind-key "M-h" 'mark-containing-sexp paredit-mode-map)
  (bind-key "M-I" 'paredit-splice-sexp paredit-mode-map)

  (unbind-key "M-r" paredit-mode-map)
  (unbind-key "M-s" paredit-mode-map)

  (bind-key "C-. d" 'paredit-forward-down paredit-mode-map)
  (bind-key "C-. B" 'paredit-splice-sexp-killing-backward paredit-mode-map)
  (bind-key "C-. C" 'paredit-convolute-sexp paredit-mode-map)
  (bind-key "C-. F" 'paredit-splice-sexp-killing-forward paredit-mode-map)
  (bind-key "C-. a" 'paredit-add-to-next-list paredit-mode-map)
  (bind-key "C-. A" 'paredit-add-to-previous-list paredit-mode-map)
  (bind-key "C-. j" 'paredit-join-with-next-list paredit-mode-map)
  (bind-key "C-. J" 'paredit-join-with-previous-list paredit-mode-map)

  ;; (add-hook 'allout-mode-hook
  ;;           #'(lambda ()
  ;;               (bind-key "M-k" 'paredit-raise-sexp allout-mode-map)
  ;;               ;; (bind-key "M-h" 'mark-containing-sexp allout-mode-map)
  ;;               ))
  )

;;;_ , paren

(unless (use-package mic-paren
          :config
          (paren-activate))
  (use-package paren
    :config
    (show-paren-mode 1)))

;;;_ , per-window-point

(use-package per-window-point
  :config
  (pwp-mode 1))

;;;_ , persian-johnw

(use-package persian-johnw
  :disabled t)

;;;_ , persistent-scratch

(use-package persistent-scratch
  :disabled t
  :if (and window-system (not running-alternate-emacs)
           (not noninteractive)))

;;;_ , perspective

(use-package perspective
  :disabled t
  :config
  (use-package persp-projectile)
  (persp-mode))

;;;_ , popup-ruler

(use-package popup-ruler
  :bind (("C-. r" . popup-ruler)
         ("C-. R" . popup-ruler-vertical)))

;;;_ , powerline

(use-package powerline
  :disabled t
  :init
  (defface my-powerline-time-face
    '((t (:background "#ffff99" :inherit mode-line)))
    "Powerline face for displaying clocked time."
    :group 'powerline)

  :config
  (setq-default
   mode-line-format
   '("%e"
     (:eval
      (let*
          ((active (powerline-selected-window-active))
           (mode-line (if active 'mode-line 'mode-line-inactive))
           (face1 (if active 'powerline-active1 'powerline-inactive1))
           (face2 (if active 'powerline-active2 'powerline-inactive2))
           (separator-left
            (intern (format "powerline-%s-%s"
                            powerline-default-separator
                            (car powerline-default-separator-dir))))
           (separator-right
            (intern (format "powerline-%s-%s"
                            powerline-default-separator
                            (cdr powerline-default-separator-dir))))
           (lhs
            (list
             ;; (powerline-raw "%*" nil 'l)
             ;; (powerline-buffer-size nil 'l)
             ;; (powerline-raw mode-line-mule-info nil 'l)
             (powerline-raw " ")
             ;; (powerline-buffer-id nil 'l)
             (powerline-buffer-id nil 'l)
             ;; (when (and (boundp 'which-func-mode) which-func-mode)
             ;;   (powerline-raw which-func-format nil 'l))
             (powerline-raw " ")
             (funcall separator-left mode-line face2)
             ;; (when (boundp 'erc-modified-channels-object)
             ;;   (powerline-raw erc-modified-channels-object face1 'l))
             ;; (powerline-major-mode face1 'l)
             ;; (powerline-process face1)
             ;; (powerline-minor-modes face1 'l)
             ;; (powerline-narrow face1 'l)
             ;; (powerline-raw " " face1)
             ;; (funcall separator-left face1 face2)
             ;; (powerline-vc face2 'r)
             ))
           (rhs
            (append
             (list)
             (if (and active (org-clocking-p))
                 (list
                  ;; (powerline-raw " " 'my-powerline-time-face)
                  (powerline-raw
                   (format "  %s  "
                           (org-minutes-to-clocksum-string
                            (org-clock-get-clocked-time)))
                   'my-powerline-time-face)
                  ;; (powerline-raw " " 'my-powerline-time-face 'l)
                  ;; (powerline-raw global-mode-string face2 'r)
                  ;; (funcall separator-right face2 face1)
                  ;; (powerline-raw "%4l" face1 'l)
                  ;; (powerline-raw ":" face1 'l)
                  ;; (powerline-raw "%3c" face1 'r)
                  ;; (funcall separator-right face1 mode-line)
                  ;; (powerline-raw " ")
                  ;; (powerline-raw "%6p" nil 'r)
                  ;; (powerline-hud face2 face1)
                  )
               (list)))))
        (concat (powerline-render lhs)
                (powerline-fill face2 (powerline-width rhs))
                (powerline-render rhs)))))))
;;;_ , pp-c-l

(use-package pp-c-l
  :config
  (hook-into-modes 'pretty-control-l-mode '(prog-mode-hook)))

;;;_ , projectile

(use-package projectile
  :diminish projectile-mode
  :config
  (use-package helm-projectile
    :config
    (setq projectile-completion-system 'helm)
    (helm-projectile-on))
  (projectile-global-mode))

;;;_ , proofgeneral

(eval-and-compile
  (defun nix-lisp-path (part)
    (list (expand-file-name part nix-site-lisp-directory))))

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

(use-package proof-site
  :load-path "~/.nix-profile/share/emacs/site-lisp/ProofGeneral/generic"
  :config
  (use-package coq
    :mode ("\\.v\\'" . coq-mode)
    :load-path "~/.nix-profile/share/emacs/site-lisp/ProofGeneral/coq"
    :functions (proof-layout-windows proof-prf holes-mode)
    :config
    (add-hook
     'coq-mode-hook
     (lambda ()
       (holes-mode -1)
       (yas-minor-mode 1)
       (whitespace-mode 1)
       ;; (set-input-method "Agda")
       (add-hook 'proof-shell-extend-queue-hook
                 (lambda ()
                   (set-window-dedicated-p (selected-window) t)))
       (defalias 'proof-display-and-keep-buffer
         'my-proof-display-and-keep-buffer)))

    (bind-key "M-RET" 'proof-goto-point coq-mode-map)
    (bind-key "RET" 'newline-and-indent coq-mode-map)
    (bind-key "<tab>" 'yas-expand-from-trigger-key coq-mode-map)
    (bind-key "C-c C-p" (lambda ()
                          (interactive)
                          (proof-layout-windows)
                          (proof-prf)) coq-mode-map)
    (bind-key "C-c C-a C-s" 'coq-SearchConstant coq-mode-map)
    (unbind-key "C-c h" coq-mode-map)

    (use-package coq-seq-compile
      :disabled t
      :defer t
      :config
      (defun my-coq-seq-get-library-dependencies
          (lib-src-file &optional command-intro)
        (let ((coqdep-arguments
               (nconc (coq-include-options lib-src-file coq-load-path)
                      (list lib-src-file)))
              coqdep-status coqdep-output)
          (if coq-debug-auto-compilation
              (message "call coqdep arg list: %s" coqdep-arguments))
          (with-temp-buffer
            (setq coqdep-status
                  (apply 'call-process
                         coq-dependency-analyzer nil (current-buffer) nil
                         coqdep-arguments))
            (setq coqdep-output (buffer-string)))
          (if coq-debug-auto-compilation
              (message "coqdep status %s, output on %s: %s"
                       coqdep-status lib-src-file coqdep-output))
          (if (string-match coq-coqdep-error-regexp coqdep-output)
              ()
            (if (eq coqdep-status 0)
                (if (string-match ": \\(.*\\)$" coqdep-output)
                    (cdr-safe (split-string (match-string 1 coqdep-output)))
                  ())
              (let* ((this-command (cons coq-dependency-analyzer
                                         coqdep-arguments))
                     (full-command (if command-intro
                                       (cons command-intro this-command)
                                     this-command)))
                ;; display the error
                (coq-init-compile-response-buffer
                 (mapconcat 'identity full-command " "))
                (let ((inhibit-read-only t))
                  (with-current-buffer coq-compile-response-buffer
                    (insert coqdep-output)))
                (coq-display-compile-response-buffer)
                "unsatisfied dependencies")))))

      (defalias 'coq-seq-get-library-dependencies
        'my-coq-seq-get-library-dependencies))

    (use-package pg-user
      :defer t
      :config
      (defadvice proof-retract-buffer
          (around my-proof-retract-buffer activate)
        (condition-case err ad-do-it
          (error (shell-command "killall ssrcoq")))))))

;;;_ , ps-print

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

;;;_ , puppet-mode

(use-package puppet-mode
  :disabled t
  :mode ("\\.pp\\'" . puppet-mode)
  :config
  (use-package puppet-ext))

;;;_ , python-mode

(use-package python-mode
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

;;;_ , quickrun

(use-package quickrun
  :disabled t
  :bind ("C-c C-r" . quickrun))

;;;_ , rainbow-mode

(use-package rainbow-mode
  :commands rainbow-mode)

;;;_ , recentf

(use-package recentf
  :if (not noninteractive)
  :config
  (recentf-mode 1)

  (defun recentf-add-dired-directory ()
    (if (and dired-directory
             (file-directory-p dired-directory)
             (not (string= "/" dired-directory)))
        (let ((last-idx (1- (length dired-directory))))
          (recentf-add-file
           (if (= ?/ (aref dired-directory last-idx))
               (substring dired-directory 0 last-idx)
             dired-directory)))))

  (add-hook 'dired-mode-hook 'recentf-add-dired-directory))

;;;_ , repeat-insert

(use-package repeat-insert
  :disabled t
  :commands (insert-patterned
             insert-patterned-2
             insert-patterned-3
             insert-patterned-4))

;;;_ , ruby-mode

(use-package ruby-mode
  :mode ("\\.rb\\'" . ruby-mode)
  :interpreter ("ruby" . ruby-mode)
  :functions inf-ruby-keys
  :config
  (use-package yari
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
    (bind-key "C-h C-i" 'helm-yari ruby-mode-map)

    (set (make-local-variable 'yas-fallback-behavior)
         '(apply ruby-indent-command . nil))
    (bind-key "<tab>" 'yas-expand-from-trigger-key ruby-mode-map))

  (add-hook 'ruby-mode-hook 'my-ruby-mode-hook))

;;;_ , sage-mode

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

;;;_ , selectkey

(use-package selectkey
  :disabled t
  :bind-keymap ("C-. b" . selectkey-select-prefix-map)
  :config
  (selectkey-define-select-key compile "c" "\\*compilation")
  (selectkey-define-select-key shell-command "o" "Shell Command")
  (selectkey-define-select-key shell "s" "\\*shell" (shell))
  (selectkey-define-select-key multi-term "t" "\\*terminal" (multi-term-next))
  (selectkey-define-select-key eshell "z" "\\*eshell" (eshell)))

;;;_ , session

(use-package session
  :if (not noninteractive)
  :load-path "site-lisp/session/lisp/"
  :config
  (session-initialize)

  (defun remove-session-use-package-from-settings ()
    (when (string= (file-name-nondirectory (buffer-file-name))
                   "settings.el")
      (save-excursion
        (goto-char (point-min))
        (when (re-search-forward "^ '(session-use-package " nil t)
          (delete-region (line-beginning-position)
                         (1+ (line-end-position)))))))

  (add-hook 'before-save-hook 'remove-session-use-package-from-settings)

  ;; expanded folded secitons as required
  (defun le::maybe-reveal ()
    (when (and (or (memq major-mode  '(org-mode outline-mode))
                   (and (boundp 'outline-minor-mode)
                        outline-minor-mode))
               (outline-invisible-p))
      (if (eq major-mode 'org-mode)
          (org-reveal)
        (show-subtree))))

  (add-hook 'session-after-jump-to-last-change-hook 'le::maybe-reveal)

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

  (run-with-idle-timer 60 t 'save-information)

  (if window-system
      (add-hook 'after-init-hook 'session-initialize t)))

;;;_ , sh-script

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

;;;_ , sh-toggle

(use-package sh-toggle
  :bind ("C-. C-z" . shell-toggle))

;;;_ , slime

(use-package slime
  :disabled t
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

;;;_ , smart-compile

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

(bind-key "M-O" 'show-compilation)

(defun compilation-ansi-color-process-output ()
  (ansi-color-process-output nil)
  (set (make-local-variable 'comint-last-output-start)
       (point-marker)))

(add-hook 'compilation-filter-hook #'compilation-ansi-color-process-output)

(use-package smart-compile
  :disabled t
  :commands smart-compile
  :bind (("C-c c" . smart-compile)
         ("A-n"   . next-error)
         ("A-p"   . previous-error)))

;;;_ , smartparens

(use-package smartparens
  :commands (smartparens-mode show-smartparens-mode)
  :config (require 'smartparens-config))

;;;_ , smerge-mode

(use-package smerge-mode
  :commands smerge-mode
  :config
  (setq smerge-command-prefix (kbd "C-. C-.")))

;;;_ , stopwatch

(use-package stopwatch
  :bind ("<f8>" . stopwatch))

;;;_ , sunrise-commander

(use-package sunrise-commander
  :bind (("C-c j" . my-activate-sunrise)
         ("C-c C-j" . sunrise-cd))
  :commands sunrise
  :defines sr-tabs-mode-map
  :init
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

;;;_ , tablegen-mode

(use-package tablegen-mode
  :mode ("\\.td\\'" . tablegen-mode))

;;;_ , texinfo

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

;;;_ , textexpander

(bind-key "A-v" 'scroll-down)
(bind-key "M-v" 'yank)

;;;_ , tiny

(use-package tiny
  :bind ("C-. N" . tiny-expand))

;;;_ , twittering-mode

(use-package twittering-mode
  :disabled t
  :commands twit
  :config
  (setq twittering-use-master-password t))

;;;_ , undo-tree

(use-package undo-tree
  :disabled t
  :commands undo-tree-mode
  :config
  (add-hook 'find-file-hook (lambda () (undo-tree-mode 1))))

;;;_ , vkill

(use-package vkill
  :commands vkill
  :bind ("C-x L" . vkill-and-helm-occur)
  :init
  (defun vkill-and-helm-occur ()
    (interactive)
    (vkill)
    (call-interactively #'helm-occur))

  :config
  (setq vkill-show-all-processes t))

;;;_ , w3m

(use-package w3m
  :disabled t
  :commands (w3m-search w3m-find-file)
  :bind (("C-. u"   . w3m-browse-url)
         ("C-. U"   . w3m-browse-url-new-session)
         ("C-. A-u" . w3m-browse-chrome-url-new-session)
         ("C-. w"   . show-browser)
         ("A-M-e"   . goto-emacswiki)
         ("A-M-g"   . w3m-search)
         ("A-M-w"   . wikipedia-query))
  :init
  (setq w3m-command "w3m")

  (setq w3m-coding-system 'utf-8
        w3m-file-coding-system 'utf-8
        w3m-file-name-coding-system 'utf-8
        w3m-input-coding-system 'utf-8
        w3m-output-coding-system 'utf-8
        w3m-terminal-coding-system 'utf-8)

  (add-hook 'w3m-mode-hook 'w3m-link-numbering-mode)

  (autoload 'w3m-session-crash-recovery-remove "w3m-session")

  (defun show-browser ()
    (interactive)
    (let ((w3m-buf
           (catch 'found
             (dolist (buf (buffer-list))
               (if (string-match "\\*w3m" (buffer-name buf))
                   (throw 'found buf))))))
      (if w3m-buf
          (switch-to-buffer-other-window w3m-buf)
        (call-interactively 'w3m-find-file))))

  (defun wikipedia-query (term)
    (interactive (list (read-string "Wikipedia search: " (word-at-point))))
    (require 'w3m-search)
    (w3m-search "en.wikipedia" term))

  (eval-when-compile
    (autoload 'w3m-search-escape-query-string "w3m-search"))

  (defun wolfram-alpha-query (term)
    (interactive (list (read-string "Ask Wolfram Alpha: " (word-at-point))))
    (require 'w3m-search)
    (w3m-browse-url (concat "http://m.wolframalpha.com/input/?i="
                            (w3m-search-escape-query-string term))))

  (defun goto-emacswiki ()
    (interactive)
    (w3m-browse-url "http://www.emacswiki.org"))

  (defun w3m-browse-url-new-session (url)
    (interactive (progn
                   (require 'browse-url)
                   (browse-url-interactive-arg "Emacs-w3m URL: ")))
    (w3m-browse-url url t))

  (defun w3m-browse-chrome-url-new-session ()
    (interactive)
    (let ((url (do-applescript
                (string-to-multibyte "tell application \"Google Chrome\"
  URL of active tab of front window
  end tell"))))
      (w3m-browse-url (substring url 1 (1- (length url))) t)))

  :config
  (let (proxy-host proxy-port)
    (with-temp-buffer
      (shell-command "scutil --proxy" (current-buffer))

      (when (re-search-forward "HTTPPort : \\([0-9]+\\)" nil t)
        (setq proxy-port (match-string 1)))
      (when (re-search-forward "HTTPProxy : \\(\\S-+\\)" nil t)
        (setq proxy-host (match-string 1))))

    (if (and proxy-host proxy-port)
        (setq w3m-command-arguments
              (nconc w3m-command-arguments
                     (list "-o" (format "http_proxy=http://%s:%s/"
                                        proxy-host proxy-port)))))

    (use-package w3m-type-ahead
      :requires w3m
      :init
      (add-hook 'w3m-mode-hook 'w3m-type-ahead-mode))

    (add-hook 'w3m-display-hook
              (lambda (url)
                (let ((buffer-read-only nil))
                  (delete-trailing-whitespace))))

    (defun my-w3m-linknum-follow ()
      (interactive)
      (w3m-linknum-follow))

    (bind-key "k" 'w3m-delete-buffer w3m-mode-map)
    (bind-key "i" 'w3m-view-previous-page w3m-mode-map)
    (bind-key "p" 'w3m-previous-anchor w3m-mode-map)
    (bind-key "n" 'w3m-next-anchor w3m-mode-map)

    (defun dka-w3m-textarea-hook()
      (save-excursion
        (while (re-search-forward "\r\n" nil t)
          (replace-match "\n" nil nil))
        (delete-other-windows)))

    (add-hook 'w3m-form-input-textarea-mode-hook 'dka-w3m-textarea-hook)

    (bind-key "<return>" 'w3m-view-url-with-external-browser
              w3m-minor-mode-map)
    (bind-key "S-<return>" 'w3m-safe-view-this-url w3m-minor-mode-map)))

;;;_ , wcount-mode

(use-package wcount-mode
  :commands wcount)

;;;_ , whitespace

(use-package whitespace
  :diminish (global-whitespace-mode
             whitespace-mode
             whitespace-newline-mode)
  :commands (whitespace-buffer
             whitespace-cleanup
             whitespace-mode)
  :demand t
  :init
  (hook-into-modes 'whitespace-mode
                   '(prog-mode-hook
                     c-mode-common-hook))

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
                  #'(lambda ()
                      (ignore (whitespace-cleanup))) nil t)
        (whitespace-cleanup))))

  (add-hook 'find-file-hooks 'maybe-turn-on-whitespace t)

  :config
  (remove-hook 'find-file-hooks 'whitespace-buffer)
  (remove-hook 'kill-buffer-hook 'whitespace-buffer))

;;;_ , winner

(use-package winner
  ;; :diminish winner-mode
  :if (not noninteractive)
  :bind (("M-N" . winner-redo)
         ("M-P" . winner-undo))
  :demand t
  :config
  (winner-mode 1))

;;;_ , workgroups

(use-package workgroups
  :diminish workgroups-mode
  :if (not noninteractive)
  :demand t
  :config
  (workgroups-mode 1)

  (let ((workgroups-file (expand-file-name "workgroups" user-data-directory)))
    (if (file-readable-p workgroups-file)
        (wg-load workgroups-file)))

  (bind-key "C-\\" 'wg-switch-to-previous-workgroup wg-map)
  (bind-key "\\" 'toggle-input-method wg-map))

;;;_ , wrap-region

(use-package wrap-region
  :commands wrap-region-mode
  :diminish wrap-region-mode
  :config
  (wrap-region-add-wrappers
   '(("$" "$")
     ("/" "/" nil ruby-mode)
     ("/* " " */" "#" (java-mode javascript-mode css-mode c-mode c++-mode))
     ("`" "`" nil (markdown-mode ruby-mode shell-script-mode)))))

;;;_ , yaml-mode

(use-package yaml-mode
  :mode ("\\.ya?ml\\'" . yaml-mode))

;;;_ , yasnippet

(use-package yasnippet
  :if (not noninteractive)
  :diminish yas-minor-mode
  :commands yas-minor-mode
  :defines yas-guessed-modes
  :mode ("/\\.emacs\\.d/snippets/" . snippet-mode)
  :bind (("C-c y TAB" . yas-expand)
         ("C-c y n"   . yas-new-snippet)
         ("C-c y f"   . yas-find-snippets)
         ("C-c y r"   . yas-reload-all)
         ("C-c y v"   . yas-visit-snippet-file))
  :init
  (hook-into-modes #'(lambda () (yas-minor-mode 1))
                   '(haskell-mode-hook
                     coq-mode-hook
                     org-mode-hook
                     ruby-mode-hook
                     message-mode-hook
                     gud-mode-hook
                     erc-mode-hook))
  :config
  (yas-load-directory "~/.emacs.d/snippets/")

  (bind-key "C-i" 'yas-next-field-or-maybe-expand yas-keymap)

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
        (yas-expand-snippet "\
# -*- mode: snippet -*-
# name: $1
# --
$0")))))

;;;_ , yaoddmuse

(use-package yaoddmuse
  :bind (("C-c w f" . yaoddmuse-browse-page-default)
         ("C-c w e" . yaoddmuse-edit-default)
         ("C-c w p" . yaoddmuse-post-library-default)))

;;;_ , zencoding-mode

(use-package zencoding-mode
  :disabled t
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

;;;_. Post initialization

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

;; Local Variables:
;;   mode: emacs-lisp
;;   outline-regexp: "^;;;_\\([,. ]+\\)"
;; End:

;;; init.el ends here
