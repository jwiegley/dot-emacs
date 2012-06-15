;;;_. Initialization

(defconst emacs-start-time (current-time))

(message "Loading %s..." load-file-name)

(setq message-log-max 16384)

;;;_ , Create use-package macro, to simplify customizations

(eval-when-compile
  (require 'cl))

(defvar use-package-verbose nil)

(defmacro hook-into-modes (func modes)
  `(dolist (mode-hook ,modes)
     (add-hook mode-hook ,func)))

(defmacro use-package (name &rest args)
  (let* ((commands (plist-get args :commands))
         (init-body (plist-get args :init))
         (config-body (plist-get args :config))
         (diminish-var (plist-get args :diminish))
         (defines (plist-get args :defines))
         (predicate (plist-get args :if))
         (defines-eval (if (null defines)
                           nil
                         (if (listp defines)
                             (mapcar (lambda (var) `(defvar ,var)) defines)
                           `((defvar ,defines)))))
         (requires (plist-get args :requires))
         (requires-test (if (null requires)
                            t
                          (if (listp requires)
                              `(not (member nil (mapcar #'featurep
                                                        (quote ,requires))))
                            `(featurep (quote ,requires)))))
         (name-string (if (stringp name) name
                        (symbol-name name))))
    (if diminish-var
        (setq config-body
              `(progn
                 ,config-body
                 (ignore-errors
                   ,@(if (listp diminish-var)
                         (mapcar (lambda (var) `(diminish (quote ,var)))
                                 diminish-var)
                       `((diminish (quote ,diminish-var))))))))
    (unless (plist-get args :disabled)
      (if (or commands (plist-get args :defer))
          (let (form)
            (unless (listp commands)
              (setq commands (list commands)))
            (dolist (command commands)
              (add-to-list
               'form `(autoload (function ,command)
                        ,name-string nil t)))
            `(progn
               (eval-when-compile
                 ,@defines-eval
                 ,(if (stringp name)
                      `(load ,name t)
                    `(require ',name nil t)))
               (when ,(or predicate t)
                 (let ((now (current-time)))
                   ,(if use-package-verbose
                        `(message "Pre-loading package %s..." ,name-string))
                   ,@form
                   ,init-body
                   ,(unless (null config-body)
                      `(eval-after-load ,name-string
                         '(when ,requires-test
                            (let ((now (current-time)))
                              ,(if use-package-verbose
                                   `(message "Configuring package %s..."
                                             ,name-string))
                              ,config-body
                              ,(when use-package-verbose
                                 `(let ((elapsed
                                         (float-time
                                          (time-subtract (current-time) now))))
                                    (if (> elapsed 0.01)
                                        (message
                                         "Configuring package %s...done (%.3fs)"
                                         ,name-string elapsed)
                                      (message "Configuring package %s...done"
                                               ,name-string))))))))
                   ,(when use-package-verbose
                      `(let ((elapsed
                              (float-time
                               (time-subtract (current-time) now))))
                         (if (> elapsed 0.01)
                             (message "Pre-loading package %s...done (%.3fs)"
                                      ,name-string elapsed)
                           (message "Pre-loading package %s...done"
                                    ,name-string)))))
                 t)))
        `(progn
           (eval-when-compile
             ,@defines-eval
             ,(if (stringp name)
                  `(load ,name t)
                `(require ',name nil t)))
           (when (and ,(or predicate t)
                      ,requires-test
                      ,(if (stringp name)
                           `(load ,name t)
                         `(require ',name nil t)))
             (let ((now (current-time)))
               ,(if use-package-verbose
                    `(message "Loading package %s..." ,name-string))
               ,init-body
               ,config-body
               ,(when use-package-verbose
                  `(let ((elapsed (float-time (time-subtract (current-time)
                                                             now))))
                     (if (> elapsed 0.01)
                         (message "Loading package %s...done (%.3fs)"
                                  ,name-string elapsed)
                       (message "Loading package %s...done"
                                ,name-string)))))
             t))))))

(put 'use-package 'lisp-indent-function 1)

(font-lock-add-keywords 'emacs-lisp-mode
                        '(("(use-package\\>" . font-lock-keyword-face)))

;;;_ , Create override-global-mode to force key remappings

(require 'easy-mmode)

(defvar override-global-map (make-keymap)
  "override-global-mode keymap")

(define-minor-mode override-global-mode
  "A minor mode so that keymap settings override other modes."
  t "" override-global-map)

(defun global-override-key (key command)
  (define-key global-map key command)
  (define-key override-global-map key command))

(add-hook 'after-init-hook
          (function
           (lambda ()
             (override-global-mode 1))))

;;;_ , Read system environment

(let ((plist (expand-file-name "~/.MacOSX/environment.plist")))
  (when (file-readable-p plist)
    (let ((dict (cdr (assq #'dict (cdar (xml-parse-file plist))))))
      (while dict
        (if (and (listp (car dict))
                 (eq 'key (caar dict)))
            (setenv (car (cddr (car dict)))
                    (car (cddr (car (cddr dict))))))
        (setq dict (cdr dict))))

    ;; Configure exec-path based on the new PATH
    (setq exec-path nil)
    (mapc #'(lambda (path)
              (add-to-list 'exec-path path))
          (nreverse (split-string (getenv "PATH") ":")))))

;;;_ , Load customization settings

(defvar running-alternate-emacs nil)

(if (string= invocation-directory
             "/Applications/Misc/Emacs.app/Contents/MacOS/")

    (load (expand-file-name "settings" user-emacs-directory))

  (let ((settings (with-temp-buffer
                    (insert-file-contents
                     (expand-file-name "settings.el" user-emacs-directory))
                    (goto-char (point-min))
                    (read (current-buffer)))))

    (setq running-alternate-emacs t
          user-data-directory
          (replace-regexp-in-string "/data/" "/data-alt/" user-data-directory))

    (let* ((regexp "/\\.emacs\\.d/data/")
           (replace "/.emacs.d/data-alt/"))
      (dolist (setting settings)
        (let ((value (and (listp setting)
                          (nth 1 (nth 1 setting)))))
          (if (and (stringp value)
                   (string-match regexp value))
              (setcar (nthcdr 1 (nth 1 setting))
                      (replace-regexp-in-string regexp replace value)))))

      (eval settings))))

;;;_ , Enable disabled commands

(put 'downcase-region  'disabled nil)   ; Let upcasing work
(put 'erase-buffer     'disabled nil)
(put 'eval-expression  'disabled nil)   ; Let ESC-ESC work
(put 'narrow-to-page   'disabled nil)   ; Let narrowing work
(put 'narrow-to-region 'disabled nil)   ; Let narrowing work
(put 'set-goal-column  'disabled nil)
(put 'upcase-region    'disabled nil)   ; Let downcasing work

;;;_. Keybindings

;;;_ , C-?

(global-override-key [(control return)] 'other-window)

(defun collapse-or-expand ()
  (interactive)
  (if (> (length (window-list)) 1)
      (delete-other-windows)
    (bury-buffer)))

(define-key global-map [(control ?z)] 'collapse-or-expand)

;;;_ , ctl-x-map

(define-key ctl-x-map [?d] 'delete-whitespace-rectangle)
(define-key ctl-x-map [(shift ?f)] 'set-fill-column)
(define-key ctl-x-map [?m] 'compose-mail)

(defun edit-with-sudo ()
  (interactive)
  (let ((buf (current-buffer)))
    (find-file (concat "/sudo::" (buffer-file-name)))
    (kill-buffer buf)))

(define-key ctl-x-map [(shift ?s)] 'edit-with-sudo)
(define-key ctl-x-map [?t] 'toggle-truncate-lines)

;;;_  . C-x C-?

(define-key ctl-x-map [(control ?b)] 'ibuffer)

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

(define-key ctl-x-map [(control ?d)] 'duplicate-line)
(define-key ctl-x-map [(control ?e)] 'pp-eval-last-sexp)
(define-key ctl-x-map [(control ?n)] 'next-line)

;;;_  . C-x M-?

(define-key ctl-x-map [(meta ?n)] 'set-goal-column)

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

(define-key ctl-x-map [(meta ?q)] 'refill-paragraph)
(define-key ctl-x-map [(meta ?z)] 'shell-toggle)

;;;_ , mode-specific-map

;;;_  . C-c ?

(define-key mode-specific-map [tab] 'ff-find-other-file)
(define-key mode-specific-map [space] 'just-one-space)
(define-key mode-specific-map [? ] 'just-one-space)

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

(define-key mode-specific-map [?0]
  (recursive-edit-preserving-window-config (delete-window)))
(define-key mode-specific-map [?1]
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

(define-key mode-specific-map [?d] 'delete-current-line)

(define-key mode-specific-map [?e ?E] 'elint-current-buffer)

(defun do-eval-buffer ()
  (interactive)
  (call-interactively 'eval-buffer)
  (message "Buffer has been evaluated"))

(define-key mode-specific-map [?e ?b] 'do-eval-buffer)
(define-key mode-specific-map [?e ?c] 'cancel-debug-on-entry)
(define-key mode-specific-map [?e ?d] 'debug-on-entry)
(define-key mode-specific-map [?e ?e] 'toggle-debug-on-error)
(define-key mode-specific-map [?e ?f] 'emacs-lisp-byte-compile-and-load)
(define-key mode-specific-map [?e ?l] 'find-library)
(define-key mode-specific-map [?e ?r] 'eval-region)
(define-key mode-specific-map [?e ?s] 'scratch)
(define-key mode-specific-map [?e ?v] 'edit-variable)

(defun find-which (name)
  (interactive "sCommand name: ")
  (find-file-other-window
   (substring (shell-command-to-string (format "which %s" name)) 0 -1)))

(define-key mode-specific-map [?e ?w] 'find-which)
(define-key mode-specific-map [?e ?z] 'byte-recompile-directory)

(define-key mode-specific-map [?f] 'flush-lines)
(define-key mode-specific-map [?g] 'ignore)
(define-key mode-specific-map [?G] 'gist-region-or-buffer)
(define-key mode-specific-map [?h] 'crosshairs-mode)

(define-key mode-specific-map [?i ?b] 'flyspell-buffer)
(define-key mode-specific-map [?i ?c] 'ispell-comments-and-strings)
(define-key mode-specific-map [?i ?d] 'ispell-change-dictionary)
(define-key mode-specific-map [?i ?f] 'flyspell-mode)
(define-key mode-specific-map [?i ?k] 'ispell-kill-ispell)
(define-key mode-specific-map [?i ?m] 'ispell-message)
(define-key mode-specific-map [?i ?r] 'ispell-region)

(define-key mode-specific-map [?k] 'keep-lines)

(when window-system
  (if running-alternate-emacs
      (progn
        (defvar emacs-min-top (if (= 1050 (x-display-pixel-height)) 537 537))
        (defvar emacs-min-left 9)
        (defvar emacs-min-height 35)
        (defvar emacs-min-width 80))

    (defvar emacs-min-top 22)
    (defvar emacs-min-left (- (x-display-pixel-width) 918))
    (defvar emacs-min-height (if (= 1050 (x-display-pixel-height)) 64 64))
    (defvar emacs-min-width 100)))

(defun emacs-min ()
  (interactive)
  (set-frame-parameter (selected-frame) 'fullscreen nil)
  (set-frame-parameter (selected-frame) 'vertical-scroll-bars nil)
  (set-frame-parameter (selected-frame) 'horizontal-scroll-bars nil)
  (set-frame-parameter (selected-frame) 'top emacs-min-top)
  (set-frame-parameter (selected-frame) 'left emacs-min-left)
  (set-frame-parameter (selected-frame) 'height emacs-min-height)
  (set-frame-parameter (selected-frame) 'width emacs-min-width)

  (when running-alternate-emacs
    (set-background-color "grey85")
    (set-fringe-style 0)))

(if window-system
    (add-hook 'after-init-hook 'emacs-min))

(defun emacs-max ()
  (interactive)
  (if t
      (progn
        (set-frame-parameter (selected-frame) 'fullscreen 'fullboth)
        (set-frame-parameter (selected-frame) 'vertical-scroll-bars nil)
        (set-frame-parameter (selected-frame) 'horizontal-scroll-bars nil))
    (set-frame-parameter (selected-frame) 'top 26)
    (set-frame-parameter (selected-frame) 'left 2)
    (set-frame-parameter (selected-frame) 'width
                         (floor (/ (float (x-display-pixel-width)) 9.15)))
    (if (= 1050 (x-display-pixel-height))
        (set-frame-parameter (selected-frame) 'height
                             (if (>= emacs-major-version 24)
                                 66
                               55))
      (set-frame-parameter (selected-frame) 'height
                           (if (>= emacs-major-version 24)
                               75
                             64)))))

(defun emacs-toggle-size ()
  (interactive)
  (if (> (cdr (assq 'width (frame-parameters))) 100)
      (emacs-min)
    (emacs-max)))

(define-key mode-specific-map [?m] 'emacs-toggle-size)

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
                    python-mode perl-mode java-mode groovy-mode)))
      (set symbol value))
  :type 'string
  :group 'mail)

(defun insert-user-timestamp ()
  "Insert a quick timestamp using the value of `user-initials'."
  (interactive)
  (insert (format "%s (%s): " user-initials
                  (format-time-string "%Y-%m-%d" (current-time)))))

(define-key mode-specific-map [?n] 'insert-user-timestamp)
(define-key mode-specific-map [?o] 'customize-option)
(define-key mode-specific-map [?O] 'customize-group)

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

(define-key mode-specific-map [?p] 'insert-counting-printf)

(define-key mode-specific-map [?q] 'fill-region)
(define-key mode-specific-map [?r] 'replace-regexp)
(define-key mode-specific-map [?s] 'replace-string)
(define-key mode-specific-map [?u] 'rename-uniquely)
(define-key mode-specific-map [?v] 'ffap)

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

(define-key mode-specific-map [?w ?f] 'yaoddmuse-browse-page-default)
(define-key mode-specific-map [?w ?e] 'yaoddmuse-edit-default)
(define-key mode-specific-map [?w ?p] 'yaoddmuse-post-library-default)

(define-key mode-specific-map [?z] 'clean-buffer-list)

(define-key mode-specific-map [?\[] 'align-regexp)
(define-key mode-specific-map [?=]  'count-matches)
(define-key mode-specific-map [?\;] 'comment-or-uncomment-region)

;;;_  . C-c C-?

(defun delete-to-end-of-buffer ()
  (interactive)
  (kill-region (point) (point-max)))

(define-key mode-specific-map [(control ?z)] 'delete-to-end-of-buffer)

;;;_  . C-c M-?

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

(define-key mode-specific-map [(meta ?q)] 'unfill-paragraph)

(defun unfill-region (beg end)
  (interactive "r")
  (setq end (copy-marker end))
  (save-excursion
    (goto-char beg)
    (while (< (point) end)
      (unfill-paragraph 1)
      (forward-paragraph))))

;;;_ , help-map

(defvar lisp-find-map)
(define-prefix-command 'lisp-find-map)
(define-key help-map [?e] 'lisp-find-map)
(define-key lisp-find-map [?a] 'my-helm-apropos)
(define-key lisp-find-map [?c] 'finder-commentary)
(define-key lisp-find-map [?e] 'view-echo-area-messages)
(define-key lisp-find-map [?f] 'find-function)
(define-key lisp-find-map [?F] 'find-face-definition)

;;; jww (2012-06-14): Change this to use helm
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

    (flet ((switch-in-other-buffer
            (buf)
            (when buf
              (split-window-vertically)
              (switch-to-buffer-other-window buf))))
      (switch-to-buffer find-buf)
      (switch-in-other-buffer desc-buf)
      (switch-in-other-buffer info-buf)
      ;;(switch-in-other-buffer cust-buf)
      (balance-windows))))

(define-key lisp-find-map [?d] 'my-describe-symbol)
(define-key lisp-find-map [?i] 'info-apropos)
(define-key lisp-find-map [?k] 'find-function-on-key)
(define-key lisp-find-map [?l] 'find-library)

(defun scratch ()
  (interactive)
  (let ((current-mode major-mode))
    (switch-to-buffer-other-window (get-buffer-create "*scratch*"))
    (goto-char (point-min))
    (when (looking-at ";")
      (forward-line 4)
      (delete-region (point-min) (point)))
    (goto-char (point-max))
    (funcall current-mode)))

(define-key lisp-find-map [?s] 'scratch)
(define-key lisp-find-map [?v] 'find-variable)

;;;_ , M-?

(define-key global-map [(meta ?/)] 'dabbrev-expand)

(define-key global-map [(meta ?g) ?c] 'goto-char)
(define-key global-map [(meta ?g) ?l] 'goto-line)

(defun delete-indentation-forward ()
  (interactive)
  (delete-indentation t))

(define-key global-map [(meta ?j)] 'delete-indentation-forward)
(define-key global-map [(meta ?J)] 'delete-indentation)

(define-key global-map [(meta ?s) ?a] 'helm-do-grep)

(defun my-helm-occur ()
  (interactive)
  (require 'helm-regexp)
  (helm-other-buffer 'helm-c-source-occur "*Helm Occur*"))

(define-key global-map [(meta ?s) ?b] 'my-helm-occur)
(define-key global-map [(meta ?s) ?F] 'helm-for-files)
(define-key global-map [(meta ?s) ?n] 'find-name-dired)
(define-key global-map [(meta ?s) ?o] 'occur)

(define-key global-map [remap eval-expression] 'pp-eval-expression)

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
(define-key global-map [(meta ?`)]  'other-frame)

(define-key global-map [(meta shift ?w)] 'mark-word)

(defun mark-line (&optional arg)
  (interactive "p")
  (beginning-of-line)
  (let ((here (point)))
    (dotimes (i arg)
      (end-of-line))
    (set-mark (point))
    (goto-char here)))

(define-key global-map [(meta shift ?l)] 'mark-line)

(defun mark-sentence (&optional arg)
  (interactive "P")
  (backward-sentence)
  (mark-end-of-sentence arg))

(define-key global-map [(meta shift ?s)] 'mark-sentence)
(define-key global-map [(meta shift ?x)] 'mark-sexp)
(define-key global-map [(meta shift ?h)] 'mark-paragraph)
(define-key global-map [(meta shift ?d)] 'mark-defun)

(define-key global-map [(meta alt ?w)] 'copy-code-as-rtf)

;;;_ , C-M-?

(define-key global-map [(control meta backspace)] 'backward-kill-sexp)

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

;;;_ , A-?

(define-key key-translation-map (kbd "A-TAB") (kbd "M-TAB"))

;;;_. Packages

;;;_ , abbrev

(use-package abbrev
  :diminish abbrev-mode
  :init
  (if (file-exists-p abbrev-file-name)
      (quietly-read-abbrev-file))
  :config
  (add-hook 'expand-load-hook
            (lambda ()
              (add-hook 'expand-expand-hook 'indent-according-to-mode)
              (add-hook 'expand-jump-hook 'indent-according-to-mode))))

;;;_ , ace-jump-mode

(use-package ace-jump-mode
  :commands ace-jump-mode
  :init
  (global-override-key [(meta ?,)] 'ace-jump-mode))

;;;_ , allout

(use-package allout
  :diminish allout-mode
  :defer t
  :config
  (progn
    (defvar allout-unprefixed-keybindings nil)

    (defun my-allout-mode-hook ()
      (dolist (mapping '((?b . allout-hide-bodies)
                         (?c . allout-hide-current-entry)
                         (?l . allout-hide-current-leaves)
                         (?i . allout-show-current-branches)
                         (?e . allout-show-entry)
                         (?o . allout-show-to-offshoot)))
        (define-key allout-mode-map
          (vconcat allout-command-prefix
                   (vector (car mapping))) (cdr mapping)))

      (if (eq 'emacs-lisp-mode major-mode)
          (define-key emacs-lisp-mode-map [(control ?k)] 'paredit-kill)))

    (add-hook 'allout-mode-hook 'my-allout-mode-hook)))

;;;_ , archive-region

(use-package archive-region)

;;;_ , auctex

(use-package tex-site
  :defines (latex-help-cmd-alist
            latex-help-file)
  :commands latex-mode
  :init
  (add-to-list 'auto-mode-alist '("\\.tex$" . latex-mode))

  :config
  (progn
    (defun latex-help-get-cmd-alist ()  ;corrected version:
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
      (info-lookup-add-help :mode 'latex-mode
                            :regexp ".*"
                            :parse-rule "\\\\?[a-zA-Z]+\\|\\\\[^a-zA-Z]"
                            :doc-spec '(("(latex2e)Concept Index" )
                                        ("(latex2e)Command Index"))))))

;;;_ , auto-complete

(use-package auto-complete-config
  :commands auto-complete-mode
  :diminish auto-complete-mode
  :config
  (progn
    (ac-set-trigger-key "TAB")

    (setq ac-use-menu-map t)

    ;; Default settings
    (define-key ac-menu-map "\C-n" 'ac-next)
    (define-key ac-menu-map "\C-p" 'ac-previous)))

;;;_ , autorevert

(use-package autorevert
  :init
  (global-auto-revert-mode 1))

;;;_ , backup-each-save

(use-package backup-each-save
  :init
  (progn
    (add-hook 'after-save-hook 'backup-each-save)

    (defun backup-each-save-filter (filename)
      (message "Checking '%s'" filename)
      (not (string-match
            "\\(^/tmp\\|\\.emacs\\.d/data/\\|\\.newsrc\\(\\.eld\\)?\\)"
            filename)))

    (setq backup-each-save-filter-function 'backup-each-save-filter)

    (defun my-dont-backup-files-p (filename)
      (unless (string-match filename "/\\(archive/sent/\\|recentf$\\)")
        (normal-backup-enable-predicate filename)))

    (setq backup-enable-predicate 'my-dont-backup-files-p)))

;;;_ , bm

(use-package bm
  :commands (bm-toggle bm-next bm-previous bm-show bm-show-all)
  :init
  (progn
    (define-key global-map [(alt ?b)] 'bm-last-in-previous-buffer)
    (define-key global-map [(alt ?f)] 'bm-first-in-next-buffer)
    (define-key global-map [(alt ?g)] 'bm-previous)
    (define-key global-map [(alt ?l)] 'bm-show-all)
    (define-key global-map [(alt ?m)] 'bm-toggle)
    (define-key global-map [(alt ?n)] 'bm-next)
    (define-key global-map [(alt ?p)] 'bm-previous)))

;;;_ , bookmark

(use-package bookmark
  :defer t
  :config
  (use-package bookmark+))

;;;_ , browse-kill-ring+

(use-package browse-kill-ring+)

;;;_ , cc-mode

(use-package cc-mode
  :commands (c-mode c++-mode)
  :init
  (progn
    (add-to-list 'auto-mode-alist '("\\.h\\(h?\\|xx\\|pp\\)\\'" . c++-mode))
    (add-to-list 'auto-mode-alist '("\\.m\\'" . c-mode))
    (add-to-list 'auto-mode-alist '("\\.mm\\'" . c++-mode))

    (defun my-c-indent-or-complete ()
      (interactive)
      (let ((class (syntax-class (syntax-after (1- (point))))))
        (if (or (bolp) (and (/= 2 class)
                            (/= 3 class)))
            (call-interactively 'indent-according-to-mode)
          (if t
              (call-interactively 'auto-complete)
            (call-interactively 'company-complete-common)))))

    (defun my-c-mode-common-hook ()
      (abbrev-mode 1)
      (gtags-mode 1)
      (hs-minor-mode 1)
      (hide-ifdef-mode 1)
      (whitespace-mode 1)
      (which-function-mode 1)
      (auto-complete-mode 1)

      (diminish 'hs-minor-mode)
      (diminish 'hide-ifdef-mode)

      (if t
          (progn
            (auto-complete-mode 1)
            (setq ac-sources (append '(ac-source-gtags
                                       ;; ac-source-clang
                                       ac-source-yasnippet)
                                     ac-sources))
            (define-key c-mode-base-map [(alt tab)] 'ac-complete))
        (company-mode 1)
        (define-key c-mode-base-map [(alt tab)] 'company-complete-common))

      ;;(doxymacs-mode 1)
      ;;(doxymacs-font-lock)

      (define-key c-mode-base-map [return] 'newline-and-indent)

      (set (make-local-variable 'yas/fallback-behavior)
           '(apply my-c-indent-or-complete . nil))
      (define-key c-mode-base-map [tab] 'yas/expand-from-trigger-key)

      (define-key c-mode-base-map [(meta ?j)] 'delete-indentation-forward)
      (define-key c-mode-base-map [(control ?c) (control ?i)]
        'c-includes-current-file)

      (set (make-local-variable 'parens-require-spaces) nil)
      (setq indicate-empty-lines t)
      (setq fill-column 72)

      (define-key c-mode-base-map [(meta ?q)] 'c-fill-paragraph)

      (let ((bufname (buffer-file-name)))
        (when bufname
          (cond
           ((string-match "/ledger/" bufname)
            (c-set-style "ledger"))
           ((string-match "/ansi/" bufname)
            (c-set-style "edg")
            (substitute-key-definition 'fill-paragraph 'ti-refill-comment
                                       c-mode-base-map global-map)
            (define-key c-mode-base-map [(meta ?q)] 'ti-refill-comment))
           (t
            (c-set-style "clang")))))

      (font-lock-add-keywords 'c++-mode '(("\\<\\(assert\\|DEBUG\\)("
                                           1 font-lock-warning-face t))))

    (add-hook 'c-mode-common-hook 'my-c-mode-common-hook))

  :config
  (progn
    (setq c-syntactic-indentation nil)

    (define-key c-mode-base-map "#" 'self-insert-command)
    (define-key c-mode-base-map "{" 'self-insert-command)
    (define-key c-mode-base-map "}" 'self-insert-command)
    (define-key c-mode-base-map "/" 'self-insert-command)
    (define-key c-mode-base-map "*" 'self-insert-command)
    (define-key c-mode-base-map ";" 'self-insert-command)
    (define-key c-mode-base-map "," 'self-insert-command)
    (define-key c-mode-base-map ":" 'self-insert-command)
    (define-key c-mode-base-map "(" 'self-insert-command)
    (define-key c-mode-base-map ")" 'self-insert-command)
    (define-key c++-mode-map "<"    'self-insert-command)
    (define-key c++-mode-map ">"    'self-insert-command)

    (add-to-list 'c-style-alist
                 '("edg"
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
      (find-file-noselect "~/Contracts/TI/bugslayer/cl_0603o/cl_0603o.c")
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
              (set-fill-column (- 80    ; width of the text
                                  6     ; width of "/*  */"
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
        (goto-char here)))))

;;;_ , cmake-mode

(use-package cmake-mode
  :commands cmake-mode
  :init
  (progn
    (add-to-list 'auto-mode-alist '("CMakeLists\\.txt\\'" . cmake-mode))
    (add-to-list 'auto-mode-alist '("\\.cmake\\'" . cmake-mode))))

;;;_ , crosshairs

(use-package crosshairs
  :commands crosshairs-mode
  :init
  (define-key global-map [(meta ?o) ?c] 'crosshairs-mode))

;;;_ , css-mode

(use-package css-mode
  :commands css-mode
  :init
  (add-to-list 'auto-mode-alist '("\\.css$" . css-mode)))

;;;_ , diff-mode

(use-package diff-mode
  :commands diff-mode
  :config
  (use-package diff-mode-))

;;;_ , diminish

(use-package diminish
  :commands diminish)

;;;_ , dired

(use-package dired
  :defer t
  :config
  (progn
    (defun dired-package-initialize ()
      (unless (featurep 'dired-async)
        (use-package dired-x)
        (use-package dired-async)
        (use-package dired-sort-map)
        (use-package runner)

        (setq dired-use-ls-dired t)

        (define-key dired-mode-map [?l] 'dired-up-directory)

        (defun my-dired-switch-window ()
          (interactive)
          (if (eq major-mode 'sr-mode)
              (call-interactively #'sr-change-window)
            (call-interactively #'other-window)))

        (define-key dired-mode-map [tab] 'my-dired-switch-window)

        (define-key dired-mode-map [(meta shift ?g)] nil)
        (define-key dired-mode-map [(meta ?s) ?f] nil)

        (defadvice dired-omit-startup (after diminish-dired-omit activate)
          "Make sure to remove \"Omit\" from the modeline."
          (diminish 'dired-omit-mode))

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

    (define-key mode-specific-map [?J] 'dired-double-jump)))

;;;_ , ediff

(use-package ediff
  :defer t
  :config
  (progn
    (defun ediff-keep-both ()
      (interactive)
      (with-current-buffer ediff-buffer-C
        (beginning-of-line)
        (assert (or (looking-at "<<<<<<")
                    (re-search-backward "^<<<<<<" nil t)
                    (re-search-forward "^<<<<<<" nil t)))
        (beginning-of-line)
        (let ((beg (point)))
          (forward-line)
          (delete-region beg (point))
          (re-search-forward "^>>>>>>>")
          (beginning-of-line)
          (setq beg (point))
          (forward-line)
          (delete-region beg (point))
          (re-search-forward "^#######")
          (beginning-of-line)
          (setq beg (point))
          (re-search-forward "^=======")
          (beginning-of-line)
          (forward-line)
          (delete-region beg (point)))))

    (add-hook 'ediff-keymap-setup-hook
              (function
               (lambda ()
                 (define-key ediff-mode-map [?c] 'ediff-keep-both))))

    (defun keep-mine ()
      (interactive)
      (beginning-of-line)
      (assert (or (looking-at "<<<<<<")
                  (re-search-backward "^<<<<<<" nil t)
                  (re-search-forward "^<<<<<<" nil t)))
      (goto-char (match-beginning 0))
      (let ((beg (point))
            (hashes (re-search-forward "^#######" (+ (point) 10000) t)))
        (forward-line)
        (delete-region beg (point))
        (re-search-forward (if hashes "^>>>>>>>" "^======="))
        (setq beg (match-beginning 0))
        (re-search-forward (if hashes "^=======" "^>>>>>>>"))
        (forward-line)
        (delete-region beg (point))))

    (defun keep-theirs ()
      (interactive)
      (beginning-of-line)
      (assert (or (looking-at "<<<<<<")
                  (re-search-backward "^<<<<<<" nil t)
                  (re-search-forward "^<<<<<<" nil t)))
      (goto-char (match-beginning 0))
      (let ((beg (point))
            (hashes (re-search-forward "^#######" (+ (point) 10000) t)))
        (re-search-forward (if hashes "^>>>>>>>" "^======="))
        (forward-line)
        (delete-region beg (point))
        (re-search-forward (if hashes "^#######" "^>>>>>>>"))
        (beginning-of-line)
        (setq beg (point))
        (when hashes
          (re-search-forward "^=======")
          (beginning-of-line))
        (forward-line)
        (delete-region beg (point))))

    (defun keep-both ()
      (interactive)
      (beginning-of-line)
      (assert (or (looking-at "<<<<<<")
                  (re-search-backward "^<<<<<<" nil t)
                  (re-search-forward "^<<<<<<" nil t)))
      (beginning-of-line)
      (let ((beg (point)))
        (forward-line)
        (delete-region beg (point))
        (re-search-forward "^>>>>>>>")
        (beginning-of-line)
        (setq beg (point))
        (forward-line)
        (delete-region beg (point))
        (re-search-forward "^#######")
        (beginning-of-line)
        (setq beg (point))
        (re-search-forward "^=======")
        (beginning-of-line)
        (forward-line)
        (delete-region beg (point))))))

;;;_ , edit-server

(use-package edit-server
  :if (and window-system (not running-alternate-emacs))
  :init
  (progn
    (add-hook 'after-init-hook 'server-start t)
    (add-hook 'after-init-hook 'edit-server-start t)))

;;;_ , erc

(use-package erc
  ;; :commands erc
  :if running-alternate-emacs
  :init
  (progn
    (use-package auth-source
      :commands auth-source-search)

    (defun irc ()
      (interactive)
      (erc :server "irc.freenode.net"
           :port 6667
           :nick "johnw"
           :password (funcall
                      (plist-get
                       (car (auth-source-search :host "irc.freenode.net"
                                                :user "johnw"
                                                :type 'netrc
                                                :port 6667))
                       :secret)))
      (erc :server "irc.oftc.net"
           :port 6667
           :nick "johnw"))

    (defun im ()
      (interactive)
      (erc :server "localhost"
           :port 6667
           :nick "johnw"
           :password (funcall
                      (plist-get
                       (car (auth-source-search :host "bitlbee"
                                                :user "johnw"
                                                :type 'netrc
                                                :port 6667))
                       :secret)))))

  :config
  (progn
    (use-package erc-alert)
    (use-package erc-highlight-nicknames)
    (use-package erc-patch)

    (erc-track-minor-mode 1)
    (erc-track-mode 1)

    (defun switch-to-bitlbee ()
      (interactive)
      (switch-to-buffer-other-window "&bitlbee")
      (call-interactively 'erc-channel-names)
      (goto-char (point-max)))

    (define-key mode-specific-map [?b] 'switch-to-bitlbee)

    (defun erc-cmd-WTF (term &rest ignore)
      "Look up definition for TERM."
      (let ((def (wtf-is term)))
        (if def
            (let ((msg (concat "{Term} " (upcase term) " is " def)))
              (with-temp-buffer
                (insert msg)
                (kill-ring-save (point-min) (point-max)))
              (message msg))
          (message (concat "No definition found for " (upcase term))))))

    (defun erc-cmd-FOOL (term &rest ignore)
      (add-to-list 'erc-fools term))

    (defun erc-cmd-UNFOOL (term &rest ignore)
      (setq erc-fools (delete term erc-fools)))))

;;;_ , eshell

(use-package eshell
  :defer t
  :config
  (progn
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
      '(unintern 'eshell/rm))))

(use-package esh-toggle
  :requires eshell
  :commands eshell-toggle
  :init
  (define-key ctl-x-map [(control ?z)] 'eshell-toggle))

;;;_ , fold-dwim

(use-package fold-dwim
  :commands (fold-dwim-toggle fold-dwim-hide-all fold-dwim-show-all)
  :init
  (progn
    (define-key global-map [f13] 'fold-dwim-toggle)
    (define-key global-map [f14] 'fold-dwim-hide-all)
    (define-key global-map [f15] 'fold-dwim-show-all)))

;;;_ , gnus

(use-package dot-gnus
  :commands switch-to-gnus
  :init
  (progn
    (setq gnus-init-file (expand-file-name "dot-gnus" user-emacs-directory)
          gnus-home-directory "~/Messages/Gnus/") ; a necessary override

    (define-key global-map [(meta shift ?g)] 'switch-to-gnus)))

;;;_ , grep

(use-package grep
  :defer t
  :init
  (progn
    (define-key global-map [(meta ?s) ?d] 'find-grep-dired)
    (define-key global-map [(meta ?s) ?f] 'find-grep)
    (define-key global-map [(meta ?s) ?g] 'grep)

    (defun find-grep-in-project (command-args)
      (interactive
       (let ((default (thing-at-point 'symbol)))
         (list (read-shell-command "Run find (like this): "
                                   (cons (concat "git --no-pager grep -n "
                                                 default)
                                         (+ 24 (length default)))
                                   'grep-find-history))))
      (when command-args
        (let ((null-device nil))        ; see grep
          (grep command-args))))

    (define-key global-map [(meta ?s) ?p] 'find-grep-in-project))
  :config
  (progn
    (grep-apply-setting 'grep-command "grep -nH -e ")
    (grep-apply-setting
     'grep-find-command
     '("find . -type f -print0 | xargs -P4 -0 egrep -nH -e " . 52))))

;;;_ , gtags

(use-package gtags
  :commands gtags-mode
  :diminish gtags-mode
  :config
  (progn
    (define-key global-map [(meta ?.)] 'gtags-find-tag)

    (define-key mode-specific-map [?t ?.] 'gtags-find-rtag)
    (define-key mode-specific-map [?t ?f] 'gtags-find-file)
    (define-key mode-specific-map [?t ?p] 'gtags-parse-file)
    (define-key mode-specific-map [?t ?g] 'gtags-find-with-grep)
    (define-key mode-specific-map [?t ?i] 'gtags-find-with-idutils)
    (define-key mode-specific-map [?t ?s] 'gtags-find-symbol)
    (define-key mode-specific-map [?t ?r] 'gtags-find-rtag)
    (define-key mode-specific-map [?t ?v] 'gtags-visit-rootdir)

    (define-key gtags-mode-map [mouse-2] 'gtags-find-tag-from-here)

    (when (featurep 'helm)
      (use-package helm-gtags)

      (define-key global-map [(meta shift ?t)] 'helm-gtags-select)
      (define-key gtags-mode-map "\e," 'helm-gtags-resume))))

;;;_ , gud

(use-package gud
  :commands gud-gdb
  :init
  (progn
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

    (define-key global-map [(meta shift ?b)] 'show-debugger))

  :config
  (progn
    (define-key global-map [f9] 'gud-cont)
    (define-key global-map [f10] 'gud-next)
    (define-key global-map [f11] 'gud-step)
    (define-key global-map [(shift f11)] 'gud-finish)))

;;;_ , haskell-mode

(use-package haskell-mode
  :commands haskell-mode
  :init
  (add-to-list 'auto-mode-alist '("\\.l?hs$" . haskell-mode))
  :config
  (progn
    (eval-after-load "haskell-site-file"
      '(progn
         (require 'inf-haskell)
         (require 'hs-lint)))

    (defun my-haskell-mode-hook ()
      (setq haskell-saved-check-command haskell-check-command)

      (define-key haskell-mode-map [(control ?c) ?w]
        'flymake-display-err-menu-for-current-line)
      (define-key haskell-mode-map [(control ?c) ?*]
        'flymake-start-syntax-check)
      (define-key haskell-mode-map [(meta ?n)] 'flymake-goto-next-error)
      (define-key haskell-mode-map [(meta ?p)] 'flymake-goto-prev-error))

    (add-hook 'haskell-mode-hook 'my-haskell-mode-hook)

    (use-package ghc
      :commands ghc-init
      :init
      (add-hook 'haskell-mode-hook 'ghc-init))))

;;;_ , helm

(use-package helm
  :defer t
  :config
  (progn
    (use-package helm-config)

    (use-package helm-descbinds
      :commands helm-descbinds
      :init
      (fset 'describe-bindings 'helm-descbinds))

    (use-package helm-match-plugin
      :init
      (helm-match-plugin-mode t))

    (define-key mode-specific-map [(meta ?x)] 'helm-M-x)

    (define-key help-map [?a] 'helm-c-apropos)

    (defun my-helm-apropos ()
      (interactive)
      (require 'helm-elisp)
      (require 'helm-misc)
      (let ((default (thing-at-point 'symbol)))
        (helm
         :prompt "Info about: "
         :candidate-number-limit 5
         :sources
         (append (mapcar (lambda (func)
                           (funcall func default))
                         '(helm-c-source-emacs-commands
                           helm-c-source-emacs-functions
                           helm-c-source-emacs-variables
                           helm-c-source-emacs-faces
                           helm-c-source-helm-attributes))
                 '(helm-c-source-info-emacs
                   helm-c-source-info-elisp
                   helm-c-source-info-gnus
                   helm-c-source-info-org
                   helm-c-source-info-cl
                   helm-c-source-emacs-source-defun)))))))

;;;_ , hi-lock

(use-package hi-lock
  :commands (highlight-regexp
             highlight-phrase
             highlight-lines-matching-regexp)
  :init
  (progn
    (define-key global-map [(meta ?o) ?l] 'highlight-lines-matching-regexp)
    (define-key global-map [(meta ?o) ?r] 'highlight-regexp)
    (define-key global-map [(meta ?o) ?w] 'highlight-phrase)))

;;;_ , hilit-chg

(use-package hilit-chg
  :commands highlight-changes-mode
  :init
  (define-key global-map [(meta ?o) ?C] 'highlight-changes-mode))

;;;_ , hl-line

(use-package hl-line
  :commands hl-line-mode
  :init
  (define-key global-map [(meta ?o) ?h] 'hl-line-mode)

  :config
  (use-package hl-line+))

;;;_ , ido

(use-package ido
  :defines (ido-cur-item
            ido-require-match
            ido-selected
            ido-final-text
            ido-show-confirm-message)
  :init
  (ido-mode 'buffer)
  :config
  (progn
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

    (add-hook 'ido-minibuffer-setup-hook
              (function
               (lambda ()
                 (define-key ido-file-completion-map "\C-m"
                   'ido-smart-select-text))))

    (defun ido-switch-buffer-tiny-frame (buffer)
      (interactive (list (ido-read-buffer "Buffer: " nil t)))
      (with-selected-frame
          (make-frame '((width                . 80)
                        (height               . 22)
                        (left-fringe          . 0)
                        (right-fringe         . 0)
                        (vertical-scroll-bars . nil)
                        (unsplittable         . t)
                        (has-modeline-p       . nil)
                        ;;(background-color     . "grey80")
                        (minibuffer           . nil)))
        (switch-to-buffer buffer)
        (set (make-local-variable 'mode-line-format) nil)))

    (define-key ctl-x-map [?5 ?t] 'ido-switch-buffer-tiny-frame)

    (defun ido-bookmark-jump (bookmark &optional display-func)
      (interactive
       (list
        (ido-completing-read "Jump to bookmark: "
                             (mapcar #'car bookmark-alist)
                             nil 0 nil 'bookmark-history)))
      (unless bookmark
        (error "No bookmark specified"))
      (bookmark-maybe-historicize-string bookmark)
      (bookmark--jump-via bookmark (or display-func 'switch-to-buffer)))

    (define-key ctl-x-map [?r ?b] 'ido-bookmark-jump)))

;;;_ , image-file

(use-package image-file
  :init
  (auto-image-file-mode 1))

;;;_ , info

(use-package info
  :defer t
  :init
  (progn
    (define-key global-map [(control ?h) (control ?i)] 'info-lookup-symbol))

  :config
  (progn
    (defadvice info-setup (after load-info+ activate)
      (use-package info+))

    (defadvice Info-exit (after remove-info-window activate)
      "When info mode is quit, remove the window."
      (if (> (length (window-list)) 1)
          (delete-window)))))

;;;_ , indirect

(use-package indirect
  :commands indirect-region
  :init
  (define-key mode-specific-map [?C] 'indirect-region))

;;;_ , initsplit

(use-package initsplit)

;;;_ , ipa

(use-package ipa)

;;;_ , isearch

(use-package "isearch"
  :defer t
  :config
  (progn
    (define-key isearch-mode-map [(control ?c)] 'isearch-toggle-case-fold)
    (define-key isearch-mode-map [(control ?t)] 'isearch-toggle-regexp)
    (define-key isearch-mode-map [(control ?^)] 'isearch-edit-string)
    (define-key isearch-mode-map [(control ?i)] 'isearch-complete)))

;;;_ , ledger

(use-package "ldg-new"
  :commands ledger-mode
  :init
  (progn
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

    (define-key mode-specific-map [?L] 'my-ledger-start-entry)

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
          (forward-line))))))

;;;_ , lisp-mode

(use-package lisp-mode
  :commands (emacs-lisp-mode
             lisp-mode
             inferior-lisp-mode
             lisp-interaction-mode)
  :init
  (defface esk-paren-face
    '((((class color) (background dark))
       (:foreground "grey50"))
      (((class color) (background light))
       (:foreground "grey55")))
    "Face used to dim parentheses."
    :group 'starter-kit-faces)

  :config
  (progn
    (defvar slime-mode nil)
    (defvar lisp-mode-initialized nil)

    (defun initialize-lisp-mode ()
      (unless lisp-mode-initialized
        (setq lisp-mode-initialized t)

        (use-package paren
          :init
          (show-paren-mode 1))

        (use-package paredit
          :diminish paredit-mode
          :commands paredit-mode

          (use-package redshank
            :diminish redshank-mode
            :commands paredit-mode)

          (use-package edebug)

          (use-package eldoc
            :diminish eldoc-mode
            :defer t
            :init
            (use-package eldoc-extension
              :defer t
              :init
              (add-hook 'emacs-lisp-mode-hook
                        #'(lambda () (require 'eldoc-extension)) t)))

          (use-package elint
            :commands 'elint-initialize
            :init
            (defun elint-current-buffer ()
              (interactive)
              (elint-initialize)
              (elint-current-buffer))

            :config
            (progn
              (add-to-list 'elint-standard-variables 'current-prefix-arg)
              (add-to-list 'elint-standard-variables 'command-line-args-left)
              (add-to-list 'elint-standard-variables 'buffer-file-coding-system)
              (add-to-list 'elint-standard-variables 'emacs-major-version)
              (add-to-list 'elint-standard-variables 'window-system)))

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

          ;; Change lambda to an actual lambda symbol
          (mapc (lambda (major-mode)
                  (font-lock-add-keywords
                   major-mode
                   `(("(\\(lambda\\)\\>"
                      (0 (ignore
                          (compose-region (match-beginning 1)
                                          (match-end 1) ?λ))))
                     ("(\\|)" . 'esk-paren-face))))
                '(emacs-lisp-mode
                  inferior-emacs-lisp-mode
                  lisp-mode
                  inferior-lisp-mode
                  slime-repl-mode))

          ;; Register Info manuals related to Lisp
          (use-package info-lookmore
            :init
            (progn
              (info-lookmore-elisp-cl)
              (info-lookmore-elisp-userlast)
              (info-lookmore-elisp-gnus)
              (info-lookmore-apropos-elisp)))

          (mapc (lambda (mode)
                  (info-lookup-add-help
                   :mode mode
                   :regexp "[^][()'\" \t\n]+"
                   :ignore-case t
                   :doc-spec '(("(ansicl)Symbol Index" nil nil nil))))
                '(lisp-mode slime-mode slime-repl-mode
                            inferior-slime-mode)))))

    (defun my-lisp-mode-hook (&optional emacs-lisp-p)
      (initialize-lisp-mode)

      (auto-fill-mode 1)
      (paredit-mode 1)
      (redshank-mode 1)

      (let (mode-map)
        (if emacs-lisp-p
            (progn
              (setq mode-map emacs-lisp-mode-map)
              (define-key mode-map [(meta return)] 'outline-insert-heading)
              (define-key mode-map [tab] 'my-elisp-indent-or-complete)
              ;; (define-key mode-map [tab] 'yas/expand)
              )
          (turn-on-cldoc-mode)

          (setq mode-map lisp-mode-map)
          (define-key mode-map [tab] 'my-lisp-indent-or-complete)
          (define-key mode-map [(meta ?q)] 'slime-reindent-defun)
          (define-key mode-map [(meta ?l)] 'slime-selector))))

    (hook-into-modes #'my-lisp-mode-hook
                     '(lisp-mode-hook
                       inferior-lisp-mode-hook
                       slime-repl-mode-hook))

    (hook-into-modes #'my-lisp-mode-hook
                     '(emacs-lisp-mode-hook))))

;;;_ , log4j-mode

(use-package log4j-mode
  :disabled t
  :commands log4j-mode
  :init
  (add-to-list 'auto-mode-alist '("\\.log$" . log4j-mode)))

;;;_ , lua-mode

(use-package lua-mode
  :disabled t
  :commands lua-mode
  :init
  (progn
    (add-to-list 'auto-mode-alist '("\\.lua$" . lua-mode))
    (add-to-list 'interpreter-mode-alist '("lua" . lua-mode))))

;;;_ , lusty-explorer

(use-package lusty-explorer
  :commands lusty-file-explorer
  :init
  (define-key ctl-x-map [(control ?f)] 'lusty-file-explorer)
  :config
  (add-hook 'lusty-setup-hook
            (lambda ()
              (define-key lusty-mode-map [space] 'lusty-select-match)
              (define-key lusty-mode-map [? ] 'lusty-select-match)
              (define-key lusty-mode-map [(control ?d)] 'exit-minibuffer))))

;;;_ , magit

(use-package magit
  :commands magit-status
  :init
  (define-key ctl-x-map [?g] 'magit-status)
  :config
  (progn
    (setenv "GIT_PAGER" "")

    (add-hook 'magit-log-edit-mode-hook
              #'(lambda ()
                  (set-fill-column 72)
                  (flyspell-mode)
                  (orgstruct++-mode)))

    (require 'magit-topgit)
    (require 'rebase-mode)

    (defun start-git-monitor ()
      (interactive)
      (start-process "git-monitor" (current-buffer) "~/bin/git-monitor"))

    ;;(add-hook 'magit-status-mode-hook 'start-git-monitor)

    (defun git-commit-changes ()
      (start-process "*git commit*" nil "git" "commit" "-a" "-m" "changes"))

    (when (featurep 'helm)
      (defvar helm-c-source-git-files
        '((name . "Files under Git version control")
          (init . helm-c-source-git-files-init)
          (candidates-in-buffer)
          (type . file))
        "Search for files in the current Git project.")

      (defun helm-c-source-git-files-init ()
        "Build `helm-candidate-buffer' of Git files."
        (with-current-buffer (helm-candidate-buffer 'local)
          (mapcar
           (lambda (item)
             (insert (expand-file-name item) ?\n))
           (split-string (shell-command-to-string "git ls-files") "\n"))))

      (defun helm-find-git-file ()
        (interactive)
        (helm :sources 'helm-c-source-git-files
              :input ""
              :prompt "Find file: "
              :buffer "*Helm git file*"))

      (define-key ctl-x-map [?f] 'helm-find-git-file)
      (define-key global-map [(meta ?g) ?g] 'helm-find-git-file))))

;;;_ , markdown-mode

(use-package markdown-mode
  :commands markdown-mode
  :init
  (progn
    (add-to-list 'auto-mode-alist '("\\.md$" . markdown-mode))

    (defun markdown-preview-file ()
      "run Marked on the current file and revert the buffer"
      (interactive)
      (shell-command
       (format "open -a /Applications/Marked.app %s"
               (shell-quote-argument (buffer-file-name)))))

    (define-key mode-specific-map [shift ?m] 'markdown-preview-file)))

;;;_ , merlin

(defun merlin-record-times ()
  (interactive)
  (require 'rx)
  (let* ((text (buffer-substring-no-properties (line-beginning-position)
                                               (line-end-position)))
         (regex
          (rx (and string-start (0+ space)
                   (group (and (= 2 num) ?/ (= 2 num) ?/ (= 2 num)
                               space (= 2 num) ?: (= 2 num) space
                               (in "AP") ?M)) (1+ space)
                   (group (and (= 2 num) ?/ (= 2 num) ?/ (= 2 num)
                               space (= 2 num) ?: (= 2 num) space
                               (in "AP") ?M)) (1+ space)
                   (? (and (group ?*) (1+ space)))
                   (group (1+ (or digit (in ".hms"))))
                   (1+ space) (group (1+ nonl)) string-end))))
    (if (string-match regex text)
        (let ((start (match-string 1 text))
              (end (match-string 2 text))
              (cleared (match-string 3 text))
              (duration (match-string 4 text)) commodity
              (account (match-string 5 text)))
          (when (string-match "\\([0-9.]+\\)\\([mhs]\\)" duration)
            (setq commodity (match-string 2 duration)
                  duration (match-string 1 duration))
            (cond ((string= commodity "h")
                   (setq commodity "hours"))
                  ((string= commodity "m")
                   (setq commodity "minutes"))
                  ((string= commodity "s")
                   (setq commodity "seconds"))))
          (if (string-match "\\([0-9.][0-9.a-z]+\\)" account)
              (setq account (match-string 1 account)))
          (do-applescript
           (format
            "
tell application \"Merlin\"
  activate

  set act to 0

  set listActivity to every activity of first document
  repeat with oneActivity in listActivity
    if subtitle of oneActivity is \"%s\" then
      set act to oneActivity
      exit repeat
    end if
  end repeat

  if act is 0 then
    set myselection to selected object of main window of first document as list

    if (count of myselection) is 0 then
      display dialog \"Please select activity to set time for\" buttons {\"OK\"}
    else
      set act to beginning of myselection
    end if
  end if

  if act is 0 or (class of act is project) or (is milestone of act is true) then
    display dialog \"Cannot locate activity for %s\" buttons {\"OK\"}
  else
    tell act
      if ((class is not project) and (is milestone is not true)) then
        set actual start date to (date \"%s\")
        set given actual work to {amount:%s, unit:%s, floating:false, ¬
            relative error:0}
        if %s then
          set actual end date to (date \"%s\")
          delete last actuals reporting date

          set given remaining work to {amount:0, unit:hours, floating:false, ¬
              relative error:0}
        else
          delete actual end date
          set last actuals reporting date to (date \"%s\")

          -- set theReturnedItems to (display dialog \"Enter remaining hours for \" ¬
          --     with title \"Given Remaining Work\" with icon stop ¬
          --     default answer \"\" buttons {\"OK\", \"Cancel\"} default button 1)
          -- set theAnswer to the text returned of theReturnedItems
          -- set theButtonName to the button returned of theReturnedItems
          --
          -- set given remaining work to {amount:(theAnswer as number), unit:hours, ¬
          --        floating:false, relative error:0}
        end if
      end if
    end tell
  end if
end tell" account account start duration commodity (if cleared "true" "false")
          end end))))))

;;;_ , mule

(use-package mule
  :init
  (progn
    (prefer-coding-system 'utf-8)
    (set-terminal-coding-system 'utf-8)
    (setq x-select-request-type '(UTF8_STRING COMPOUND_TEXT TEXT STRING))))

;;;_ , nroff-mode

(use-package nroff-mode
  :commands nroff-mode
  :config
  (progn
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
                 (add-hook 'after-save-hook 'update-nroff-timestamp nil t))))))

;;;_ , nxml-mode

(use-package nxml-mode
  :commands nxml-mode
  :init
  (defalias 'xml-mode 'nxml-mode)
  :config
  (progn
    (defun my-nxml-mode-hook ()
      (define-key nxml-mode-map [return] 'newline-and-indent))

    (add-hook 'nxml-mode-hook 'my-nxml-mode-hook)

    (defun tidy-xml-buffer ()
      (interactive)
      (save-excursion
        (call-process-region (point-min) (point-max) "tidy" t t nil
                             "-xml" "-i" "-wrap" "0" "-omit" "-q")))

    (define-key nxml-mode-map [(control shift ?h)] 'tidy-xml-buffer)))

;;;_ , org-mode

(use-package dot-org
  :if (not running-alternate-emacs)
  :commands (org-agenda
             jump-to-org-agenda
             org-smart-capture
             org-inline-note
             org-store-link
             org-insert-link
             orgstruct++-mode)
  :init
  (progn
    (define-key global-map [(meta shift ?c)] 'jump-to-org-agenda)
    (define-key global-map [(meta ?m)] 'org-smart-capture)
    (define-key global-map [(meta shift ?m)] 'org-inline-note)

    (define-key mode-specific-map [?a] 'org-agenda)

    (define-key mode-specific-map [?S] 'org-store-link)
    (define-key mode-specific-map [?l] 'org-insert-link)

    (run-with-idle-timer 300 t 'jump-to-org-agenda)))

;;;_ , per-window-point

(use-package per-window-point
  :init
  (pwp-mode 1))

;;;_ , persistent-scratch

(use-package persistent-scratch
  :if window-system)

;;;_ , pp-c-l

(use-package pp-c-l
  :commands pretty-control-l-mode
  :init
  (hook-into-modes 'pretty-control-l-mode '(emacs-lisp-mode-hook)))

;;;_ , ps-print

(use-package ps-print
  :defer t
  :config
  (progn
    (defun ps-spool-to-pdf (beg end &rest ignore)
      (interactive "r")
      (let ((temp-file (concat (make-temp-name "ps2pdf") ".pdf")))
        (call-process-region beg end (executable-find "ps2pdf")
                             nil nil nil "-" temp-file)
        (call-process (executable-find "open") nil nil nil temp-file)))

    (setq ps-print-region-function 'ps-spool-to-pdf)))

;;;_ , puppet-mode

(use-package puppet-mode
  :commands puppet-mode
  :init
  (add-to-list 'auto-mode-alist '("\\.pp$" . puppet-mode)))

;;;_ , python-mode

(use-package python-mode
  :commands python-mode
  :init
  (progn
    (add-to-list 'auto-mode-alist '("\\.py$" . python-mode))
    (add-to-list 'interpreter-mode-alist '("python" . python-mode)))

  :config
  (progn
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

      (define-key python-mode-map [(control ?c) (control ?z)] 'python-shell)
      (define-key python-mode-map [(control ?c) ?c] 'compile))

    (add-hook 'python-mode-hook 'my-python-mode-hook)))

;;;_ , quickrun

(use-package quickrun
  :commands quickrun
  :init
  (define-key mode-specific-map [(control ?r)] 'quickrun))

;;;_ , recentf

(use-package recentf
  :if window-system
  :init
  (recentf-mode 1))

;;;_ , session

(use-package session
  :if window-system
  :init
  (progn
    (session-initialize)

    (defun save-information ()
      (dolist (func kill-emacs-hook)
        (unless (memq func '(exit-gnus-on-exit server-force-stop))
          (funcall func)))
      (unless (eq 'listen (process-status server-process))
        (server-start)))

    (run-with-idle-timer 300 t 'save-information)

    (if window-system
        (add-hook 'after-init-hook 'session-initialize t))))

;;;_ , sh-script

(use-package sh-script
  :defer t
  :config
  (progn
    (defvar sh-script-initialized nil)
    (defun initialize-sh-script ()
      (unless sh-script-initialized
        (setq sh-script-initialized t)
        (info-lookup-add-help :mode 'shell-script-mode
                              :regexp ".*"
                              :doc-spec
                              '(("(bash)Index")))))

    (add-hook 'shell-mode-hook 'initialize-sh-script)))

;;;_ , smart-compile

(use-package smart-compile
  :commands smart-compile
  :init
  (progn
    (define-key mode-specific-map [?c] 'smart-compile)

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

    (define-key global-map [(meta shift ?o)] 'show-compilation)))

;;;_ , springboard

(use-package springboard
  :commands springboard
  :init
  (global-override-key [(control ?.)] 'springboard))

;;;_ , stopwatch

(use-package stopwatch
  :commands stopwatch
  :init
  (define-key global-map [f8] 'stopwatch))

;;;_ , sunrise-commander

(use-package sunrise-commander
  :commands (sunrise sunrise-cd)
  :init
  (progn
    (defun my-activate-sunrise ()
      (interactive)
      (let ((sunrise-exists
             (count-if (lambda (buf)
                         (string-match " (Sunrise)$" (buffer-name buf)))
                       (buffer-list))))
        (if (> sunrise-exists 0)
            (call-interactively 'sunrise)
          (sunrise "~/dl/" "~/Archives/"))))

    (define-key mode-specific-map [?j] 'my-activate-sunrise)
    (define-key mode-specific-map [(control ?j)] 'sunrise-cd))

  :config
  (progn
    (require 'sunrise-x-modeline)
    (require 'sunrise-x-tree)
    (require 'sunrise-x-tabs)
    (require 'sunrise-x-loop)

    (define-key sr-mode-map "/" 'sr-sticky-isearch-forward)
    (define-key sr-mode-map "\C-e" 'end-of-line)
    (define-key sr-mode-map "l" 'sr-dired-prev-subdir)

    (define-key sr-tabs-mode-map [(control ?p)] 'previous-line)
    (define-key sr-tabs-mode-map [(control ?n)] 'next-line)

    (define-key sr-tabs-mode-map [(meta ?\[)] 'sr-tabs-prev)
    (define-key sr-tabs-mode-map [(meta ?\])] 'sr-tabs-next)

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
          (message "Opening \"%s\" ..." fname))))))

;;;_ , texinfo

(use-package texinfo
  :defines texinfo-section-list
  :commands texinfo-mode
  :init
  (add-to-list 'auto-mode-alist '("\\.texi$" . texinfo-mode))

  :config
  (progn
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
              5)))))))

;;;_ , vkill

(use-package vkill
  :commands vkill
  :init
  (progn
    (if (featurep 'helm)
        (progn
          (defun vkill-and-helm-occur ()
            (interactive)
            (vkill)
            (call-interactively #'helm-occur))

          (define-key ctl-x-map [?L] 'vkill-and-helm-occur))
      (define-key ctl-x-map [?L] 'vkill)))
  :config
  (setq vkill-show-all-processes t))

;;;_ , w3m

(use-package w3m
  :commands (w3m-browse-url
             w3m-search
             w3m-search-escape-query-string)
  :init
  (progn
    (setq w3m-command "/opt/local/bin/w3m")

    (defun wikipedia-query (term)
      (interactive (list (read-string "Wikipedia search: " (word-at-point))))
      (w3m-search "en.wikipedia" term))

    (defun wolfram-alpha-query (term)
      (interactive (list (read-string "Ask Wolfram Alpha: " (word-at-point))))
      (w3m-browse-url (format "http://m.wolframalpha.com/input/?i=%s"
                              (w3m-search-escape-query-string term))))

    (define-key global-map [(alt meta ?g)] 'w3m-search)
    (define-key global-map [(alt meta ?h)] 'wolfram-alpha-query)
    (define-key global-map [(alt meta ?w)] 'wikipedia-query))

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

    (define-key w3m-minor-mode-map "\C-m" 'w3m-view-url-with-external-browser)))

;;;_ , whitespace

(use-package whitespace
  :diminish (global-whitespace-mode
             whitespace-mode
             whitespace-newline-mode)
  :commands (whitespace-buffer
             whitespace-cleanup
             whitespace-mode)
  :init
  (progn
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
                             (string-match "\\.texi$" buffer-file-name))))
          (add-hook 'write-contents-hooks
                    #'(lambda ()
                        (ignore (whitespace-cleanup))) nil t)
          (whitespace-cleanup))))

    (add-hook 'find-file-hooks 'maybe-turn-on-whitespace t))

  :config
  (progn
    (remove-hook 'find-file-hooks 'whitespace-buffer)
    (remove-hook 'kill-buffer-hook 'whitespace-buffer)))

;;;_ , winner

(use-package winner
  :diminish winner-mode
  :if window-system
  :init
  (progn
    (winner-mode 1)

    (define-key global-map [(meta shift ?n)] 'winner-redo)
    (define-key global-map [(meta shift ?p)] 'winner-undo)))

;;;_ , workgroups

(use-package workgroups
  :diminish workgroups-mode
  :commands wg-switch-to-index-1
  :if window-system
  :init
  (progn
    (defvar workgroups-preload-map)
    (define-prefix-command 'workgroups-preload-map)
    (define-key global-map [(control ?\\)] 'workgroups-preload-map)

    (define-key workgroups-preload-map [(control ?\\)] 'wg-switch-to-index-1)
    (define-key workgroups-preload-map [?1] 'wg-switch-to-index-1))

  :config
  (progn
    (workgroups-mode 1)

    (let ((workgroups-file (expand-file-name "workgroups" user-data-directory)))
      (if (file-readable-p workgroups-file)
          (wg-load workgroups-file)))

    (define-key wg-map [(control ?\\)] 'wg-switch-to-previous-workgroup)
    (define-key wg-map [?\\] 'toggle-input-method)))

;;;_ , wrap-region

(use-package wrap-region
  :commands wrap-region-mode
  :diminish wrap-region-mode
  :config
  (wrap-region-add-wrappers
   '(("$" "$")
     ("/" "/" nil ruby-mode)
     ("/* " " */" "#" (java-mode javascript-mode css-mode
                                 c-mode c++-mode))
     ("`" "`" nil (markdown-mode ruby-mode shell-script-mode)))))

;;;_ , write-room

(defun write-room ()
  "Make a frame without any bling."
  (interactive)
  ;; to restore:
  ;; (setq mode-line-format (default-value 'mode-line-format))
  (let ((frame (make-frame
                '((minibuffer . nil)
                  (vertical-scroll-bars . nil)
                  (left-fringe . 0); no fringe
                  (right-fringe . 0)
                  (background-mode . dark)
                  (background-color . "cornsilk")
                  (foreground-color . "black")
                  (cursor-color . "green")
                  (border-width . 0)
                  (border-color . "black"); should be unnecessary
                  (internal-border-width . 64); whitespace!
                  (cursor-type . box)
                  (menu-bar-lines . 0)
                  (tool-bar-lines . 0)
                  (fullscreen . fullboth)  ; this should work
                  (unsplittable . t)))))
    (select-frame frame)
    (find-file "~/Documents/Notes.txt")
    (setq mode-line-format nil
          fill-column 65)
    (set-window-margins (selected-window) 50 50)))

;;;_ , yasnippet

(use-package yasnippet
  :diminish yas/minor-mode
  :commands (yas/minor-mode yas/expand snippet-mode)
  :init
  (progn
    (add-to-list 'auto-mode-alist
                 '("/\\.emacs\\.d/snippets/" . snippet-mode))

    (hook-into-modes 'yas/minor-mode
                     '(org-mode-hook
                       ruby-mode-hook
                       message-mode-hook
                       gud-mode-hook)))
  :config
  (progn
    (yas/initialize)
    (yas/load-directory (expand-file-name "snippets/" user-emacs-directory))

    (define-key yas/keymap [tab] 'yas/next-field-or-maybe-expand)

    (defun yas/new-snippet (&optional choose-instead-of-guess)
      (interactive "P")
      (let ((guessed-directories (yas/guess-snippet-directories)))
        (switch-to-buffer "*new snippet*")
        (erase-buffer)
        (kill-all-local-variables)
        (snippet-mode)
        (set (make-local-variable 'yas/guessed-modes)
             (mapcar #'(lambda (d)
                         (intern (yas/table-name (car d))))
                     guessed-directories))
        (unless (and choose-instead-of-guess
                     (not (y-or-n-p "Insert a snippet with useful headers? ")))
          (yas/expand-snippet "\
# -*- mode: snippet -*-
# name: $1
# --
$0"))))

    (define-key mode-specific-map [?y ?n] 'yas/new-snippet)
    (define-key mode-specific-map [?y tab] 'yas/expand)
    (define-key mode-specific-map [?y ?f] 'yas/find-snippets)
    (define-key mode-specific-map [?y ?r] 'yas/reload-all)
    (define-key mode-specific-map [?y ?v] 'yas/visit-snippet-file)))

;;;_ , zencoding-mode

(use-package zencoding-mode
  :disabled t
  :commands zencoding-mode
  :init
  (progn
    (add-hook 'nxml-mode-hook 'zencoding-mode)
    (add-hook 'html-mode-hook 'zencoding-mode)
    (add-hook 'html-mode-hook
              (function
               (lambda ()
                 (define-key html-mode-map [return] 'newline-and-indent)))))

  :config
  (progn
    (defvar zencoding-mode-keymap (make-sparse-keymap))
    (define-key zencoding-mode-keymap (kbd "C-c C-c") 'zencoding-expand-line)))

;;;_ , ruby-mode

(use-package ruby-mode
  :commands ruby-mode
  :config
  (progn
    (require 'inf-ruby)

    (use-package ruby-tools)

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
      (inf-ruby-keys)

      (define-key ruby-mode-map [return] 'my-ruby-smart-return)
      (define-key ruby-mode-map [(control ?h) (control ?i)] 'helm-yari)

      (set (make-local-variable 'yas/fallback-behavior)
           '(apply ruby-indent-command . nil))
      (define-key ruby-mode-map [tab] 'yas/expand-from-trigger-key))

    (add-hook 'ruby-mode-hook 'my-ruby-mode-hook)))

;;;_. Post initialization

(let ((elapsed (float-time (time-subtract (current-time)
                                          emacs-start-time))))
  (message "Loading %s...done (%.3fs)" load-file-name elapsed))

(add-hook 'after-init-hook
          `(lambda ()
             (let ((elapsed (float-time (time-subtract (current-time)
                                                       emacs-start-time))))
               (message "Loading %s...done (%.3fs) [after-init]"
                        ,load-file-name elapsed)))
          t)

;; Local Variables:
;;   mode: emacs-lisp
;;   mode: allout
;;   outline-regexp: "^;;;_\\([,. ]+\\)"
;; End:

;;; emacs.el ends here
