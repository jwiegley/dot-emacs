;;;_ * cldoc

(autoload 'turn-on-cldoc-mode "cldoc" nil t)

(dolist (hook '(lisp-mode-hook
		slime-repl-mode-hook))
  (add-hook hook 'turn-on-cldoc-mode))

;;;_ * ansicl

(require 'info-look)

(dolist (mode '(lisp-mode slime-mode slime-repl-mode
			  inferior-slime-mode))
  (info-lookup-add-help :mode mode
			:regexp "[^][()'\" \t\n]+"
			:ignore-case t
			:doc-spec '(("(ansicl)Symbol Index" nil nil nil))))

(eval-after-load "lisp-mode"
  '(progn
     (define-key lisp-mode-map [(control ?h) ?f] 'info-lookup-symbol)))

(defadvice Info-exit (after remove-info-window activate)
  "When info mode is quit, remove the window."
  (if (> (length (window-list)) 1)
      (delete-window)))

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

;;;_ * lisp

(add-hook 'lisp-mode-hook 'turn-on-auto-fill)

(defun format-it ()
  (interactive)
  (let ((sym (thing-at-point 'symbol)))
    (delete-backward-char (length sym))
    (insert "(format t \"" sym " = ~S~%\" " sym ")")))

(put 'iterate 'lisp-indent-function 1)
(put 'mapping 'lisp-indent-function 1)
(put 'producing 'lisp-indent-function 1)

(eval-after-load "speedbar"
 '(progn
   (add-to-list 'speedbar-obj-alist '("\\.lisp$" . ".fasl"))
   (speedbar-add-supported-extension ".lisp")))

(mapc (lambda (major-mode)
	(font-lock-add-keywords
	 major-mode
	 `(("(\\(lambda\\)\\>"
	    (0 (ignore
		(compose-region (match-beginning 1)
				(match-end 1) ?λ)))))))
      '(emacs-lisp-mode inferior-emacs-lisp-mode lisp-mode slime-repl-mode
			inferior-lisp-mode scheme-mode scheme48-mode
			inferior-scheme-mode))

(require 'column-marker)
(add-hook 'lisp-mode-hook (lambda () (interactive) (column-marker-1 80)))

;;;_ * paredit

(autoload 'paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)
(autoload 'turn-on-paredit-mode "paredit"
  "Minor mode for pseudo-structurally editing Lisp code." t)

(dolist (hook '(emacs-lisp-mode-hook
		lisp-mode-hook
		slime-repl-mode-hook))
  (add-hook hook 'turn-on-paredit-mode))

;;;_ * redhank

(autoload 'redshank-mode "redshank"
  "Minor mode for restructuring Lisp code (i.e., refactoring)." t)

(dolist (hook '(emacs-lisp-mode-hook
		lisp-mode-hook
		slime-repl-mode-hook))
  (add-hook hook #'(lambda () (redshank-mode +1))))

;;;_ * slime

(add-to-list 'load-path "~/Library/Emacs/site-lisp/slime")
(add-to-list 'load-path "~/Library/Emacs/site-lisp/slime/contrib")

(require 'slime)

(slime-setup
 '(inferior-slime
   slime-asdf
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
   slime-scratch
   slime-tramp
   ;; slime-typeout-frame
   slime-xref-browser))

;;(setq slime-net-coding-system 'utf-8-unix)

(setq slime-lisp-implementations
      '((sbcl ("/usr/local/bin/sbcl"
	       "--core" "/Users/johnw/Library/Lisp/sbcl.core-with-slime-X86")
	      :init (lambda (port-file _)
		      (format "(swank:start-server %S :coding-system \"utf-8-unix\")\n"
			      port-file))
	      :coding-system utf-8-unix)
	(sbcl-cvs ("/Users/johnw/src/sbcl/src/runtime/sbcl"
		   "--core" "/Users/johnw/src/sbcl/output/sbcl.core")
		  :init (lambda (port-file _)
			  (format "(swank:start-server %S :coding-system \"utf-8-unix\")\n"
				  port-file))
		  :coding-system utf-8-unix)
	(sbcl64 ("/usr/local/stow/sbcl-X86-64/bin/sbcl"
		 "--core" "/Users/johnw/Library/Lisp/sbcl.core-with-slime-X86-64")
		:init (lambda (port-file _)
			(format "(swank:start-server %S :coding-system \"utf-8-unix\")\n"
				port-file))
		:coding-system utf-8-unix)
	(cmucl ("lisp"))
	(ecl ("ecl"))
	(allegro ("/usr/local/stow/AllegroCL/alisp"))
	(clisp ("clisp") :coding-system utf-8-unix)
	(lispworks (""))
	(openmcl ("/usr/local/stow/openmcl-darwinx8664-snapshot-070722/dx86cl64"))))

(setq slime-default-lisp 'sbcl)
(setq slime-complete-symbol*-fancy t)
(setq slime-complete-symbol-function 'slime-fuzzy-complete-symbol)

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
	   "/Users/johnw/Reference/Computing/Languages/Common Lisp/HyperSpec/")))

(defun indent-or-complete (&optional arg)
  (interactive "p")
  (if (or (looking-back "^\\s-*") (bolp))
      (call-interactively 'lisp-indent-line)
    (call-interactively 'slime-indent-and-complete-symbol)))

(eval-after-load "lisp-mode"
  '(progn
     (define-key lisp-mode-map [tab] 'indent-or-complete)
     (define-key lisp-mode-map [(meta ?q)] 'slime-reindent-defun)
     (define-key lisp-mode-map [(meta ?l)] 'slime-selector)))

(eval-after-load "slime"
  '(progn
     (define-key slime-mode-map [return] 'paredit-newline)
     (define-key slime-repl-mode-map [tab] 'indent-or-complete)
     (define-key slime-repl-mode-map [(control return)] 'other-window)

     (define-key inferior-slime-mode-map [(control ?c) (control ?p)]
       'slime-repl-previous-prompt)

     (define-key slime-mode-map [(control ?h) ?f] 'info-lookup-symbol)
     (define-key slime-repl-mode-map [(control ?h) ?f] 'info-lookup-symbol)
     (define-key inferior-slime-mode-map [(control ?h) ?f] 'info-lookup-symbol)))
