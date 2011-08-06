;;;_ * eldoc

(add-hook 'emacs-lisp-mode-hook (lambda () (require 'edebug)))

;;;_ * eldoc

(eval-after-load "eldoc"
  '(diminish 'eldoc-mode))

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

(add-hook 'emacs-lisp-mode-hook 'turn-on-auto-fill)

(font-lock-add-keywords 'emacs-lisp-mode
                        '(("(\\(lambda\\)\\>"
                           (0 (ignore
                               (compose-region (match-beginning 1)
                                               (match-end 1) ?λ))))))

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

;;;_  + column-marker

(add-hook 'emacs-lisp-mode-hook (lambda () (column-marker-1 79)))

;;;_  + highlight-parentheses

(autoload 'highlight-parentheses-mode "highlight-parentheses")

(add-hook 'emacs-lisp-mode-hook 'highlight-parentheses-mode)

(eval-after-load "highlight-parentheses"
  '(diminish 'highlight-parentheses-mode))

;;;_  + paredit

(autoload 'paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)
(autoload 'turn-on-paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)

(add-hook 'emacs-lisp-mode-hook 'turn-on-paredit-mode)

(eval-after-load "paredit"
  '(diminish 'paredit-mode))

;;;_  + redshank

(autoload 'redshank-mode "redshank"
  "Minor mode for restructuring Lisp code (i.e., refactoring)." t)

(add-hook 'emacs-lisp-mode-hook #'(lambda () (redshank-mode +1)))

(eval-after-load "redshank"
  '(diminish 'redshank-mode))

;;; lang-emacs-lisp.el ends here
