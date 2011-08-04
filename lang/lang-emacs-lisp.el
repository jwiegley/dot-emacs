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

;;;_  + column-marker

(autoload 'column-marker-1 "column-marker")

(add-hook 'emacs-lisp-mode-hook (lambda () (column-marker-1 79)))

;;;_  + highlight-parentheses

(autoload 'highlight-parentheses-mode "highlight-parentheses")

(add-hook 'emacs-lisp-mode-hook 'highlight-parentheses-mode)

;;;_  + paredit

(autoload 'paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)
(autoload 'turn-on-paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)

(dolist (hook '(emacs-lisp-mode-hook))
  (add-hook hook 'turn-on-paredit-mode))

;;;_  + redshank

(autoload 'redshank-mode "redshank"
  "Minor mode for restructuring Lisp code (i.e., refactoring)." t)

(dolist (hook '(emacs-lisp-mode-hook
		lisp-mode-hook
		slime-repl-mode-hook))
  (add-hook hook #'(lambda () (redshank-mode +1))))

;;;_ * eval-expr

(when (load "eval-expr" t)
  (eval-expr-install))
