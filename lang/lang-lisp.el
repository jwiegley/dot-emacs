;;;_ * ansicl

(require 'info-look)

(mapc (lambda (mode)
        (info-lookup-add-help
         :mode mode
         :regexp "[^][()'\" \t\n]+"
         :ignore-case t
         :doc-spec '(("(ansicl)Symbol Index" nil nil nil))))
      '(lisp-mode slime-mode slime-repl-mode inferior-slime-mode))

(defadvice Info-exit (after remove-info-window activate)
  "When info mode is quit, remove the window."
  (if (> (length (window-list)) 1)
      (delete-window)))

;;;_ * cldoc

(autoload 'turn-on-cldoc-mode "cldoc" nil t)

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

;;;_  + highlight-parentheses

(autoload 'highlight-parentheses-mode "highlight-parentheses")

(eval-after-load "highlight-parentheses"
  '(diminish 'highlight-parentheses-mode))

;;;_ * paredit

(autoload 'paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)

(eval-after-load "paredit"
  '(diminish 'paredit-mode))

;;;_ * redhank

(autoload 'redshank-mode "redshank"
  "Minor mode for restructuring Lisp code (i.e., refactoring)." t)

(eval-after-load "redshank"
  '(diminish 'redshank-mode))

;;;_ * lisp

(defun format-it ()
  (interactive)
  (let ((sym (thing-at-point 'symbol)))
    (delete-backward-char (length sym))
    (insert "(format t \"" sym " = ~S~%\" " sym ")")))

(put 'iterate 'lisp-indent-function 1)
(put 'mapping 'lisp-indent-function 1)
(put 'producing 'lisp-indent-function 1)

(mapc (lambda (major-mode)
	(font-lock-add-keywords
	 major-mode
	 `(("(\\(lambda\\)\\>"
	    (0 (ignore
		(compose-region (match-beginning 1)
				(match-end 1) ?λ)))))))
      '(emacs-lisp-mode
        inferior-emacs-lisp-mode
        lisp-mode
        inferior-lisp-mode
        slime-repl-mode))

(defface esk-paren-face
  '((((class color) (background dark))
     (:foreground "grey50"))
    (((class color) (background light))
     (:foreground "grey55")))
  "Face used to dim parentheses."
  :group 'starter-kit-faces)

(dolist (x '(scheme emacs-lisp lisp clojure))
  (when window-system
    (font-lock-add-keywords
     (intern (concat (symbol-name x) "-mode"))
     '(("(\\|)" . 'esk-paren-face)))))

;;;_ * lisp-mode-hook

(defun elisp-indent-or-complete (&optional arg)
  (interactive "p")
  (call-interactively 'lisp-indent-line)
  (unless (or (looking-back "^\\s-*")
	      (bolp)
	      (not (looking-back "[-A-Za-z0-9_*+/=<>!?]+")))
    (call-interactively 'lisp-complete-symbol)))

(defun indent-or-complete (&optional arg)
  (interactive "p")
  (if (or (looking-back "^\\s-*") (bolp))
      (call-interactively 'lisp-indent-line)
    (call-interactively 'slime-indent-and-complete-symbol)))

(defun my-lisp-mode-hook (&optional emacs-lisp-p)
  (let (mode-map)
    (if emacs-lisp-p
        (progn
          (require 'edebug)

          (setq mode-map emacs-lisp-mode-map)

          (define-key mode-map [tab] 'elisp-indent-or-complete)
          (define-key mode-map [tab] 'yas/expand))

      (turn-on-cldoc-mode)

      (setq mode-map lisp-mode-map)

      (define-key mode-map [tab] 'indent-or-complete)
      (define-key mode-map [(meta ?q)] 'slime-reindent-defun)
      (define-key mode-map [(meta ?l)] 'slime-selector))

    (auto-fill-mode 1)
    (paredit-mode 1)
    (redshank-mode 1)
    ;;(highlight-parentheses-mode 1)
    
    (column-marker-1 79)

    (define-key mode-map [(control ?h) ?F] 'info-lookup-symbol)))

(mapc (lambda (hook)
        (add-hook hook 'my-lisp-mode-hook))
      '(lisp-mode-hook inferior-lisp-mode-hook slime-repl-mode-hook))

(add-hook 'emacs-lisp-mode-hook (function (lambda () (my-lisp-mode-hook t))))

;;;_ * slime

(require 'slime)

(add-hook 'slime-load-hook
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

(setq slime-net-coding-system 'utf-8-unix)

(setq slime-lisp-implementations
      '(
	(sbcl ("sbcl" "--core" "/Users/johnw/Library/Lisp/sbcl.core-with-slime-X86-64")
	      :init (lambda (port-file _)
		      (format "(swank:start-server %S :coding-system \"utf-8-unix\")\n"
			      port-file))
	      :coding-system utf-8-unix)
        (ecl ("ecl" "-load" "/Users/johnw/Library/Lisp/lwinit.lisp"))
	(clisp ("clisp" "-i" "/Users/johnw/Library/Lisp/lwinit.lisp")
	       :coding-system utf-8-unix)))

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

(eval-after-load "hyperspec"
  '(progn
     (setq common-lisp-hyperspec-root
	   "/opt/local/share/doc/lisp/HyperSpec-7-0/HyperSpec/")))

(define-key ctl-x-map [(control ?e)] 'pp-eval-last-sexp)

;;; lang-lisp.el ends here
