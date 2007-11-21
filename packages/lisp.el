;;;_ * cldoc

(autoload 'turn-on-cldoc-mode "cldoc" nil t)

(dolist (hook '(lisp-mode-hook
		slime-repl-mode-hook))
  (add-hook hook 'turn-on-cldoc-mode))

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

(defun slime-load-periods ()
  (interactive)
  (slime-eval-async
   '(cl:progn
     (asdf:oos 'asdf:load-op :periods))))

(defun slime-load-ledger ()
  (interactive)
  (slime-eval-async
   '(cl:progn
     (asdf:oos 'asdf:load-op :ledger)
     (asdf:oos 'asdf:load-op :ledger.textual))))

;;(setq slime-net-coding-system 'utf-8-unix)

(setq slime-lisp-implementations
      '((sbcl ("/usr/local/stow/sbcl-1.0.11-i386/bin/sbcl"
	       "--core" "/Users/johnw/Library/Lisp/sbcl.core-with-slime-X86")
	      :init (lambda (port-file _)
		      (format "(swank:start-server %S :coding-system \"utf-8-unix\")\n"
			      port-file))
	      :coding-system utf-8-unix)
	(sbcl-git ("/Users/johnw/src/sbcl/src/runtime/sbcl"
		   "--core" "/Users/johnw/src/sbcl/output/sbcl.core")
		  :init (lambda (port-file _)
			  (format "(swank:start-server %S :coding-system \"utf-8-unix\")\n"
				  port-file))
		  :coding-system utf-8-unix)
	(sbcl64 ("/usr/local/stow/sbcl-1.0.11-x86_64/bin/sbcl"
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
     (define-key lisp-mode-map [(meta ?l)] 'slime-selector)
     (define-key lisp-mode-map [(control ?h) ?f] 'slime-hyperspec-lookup)
     (define-key lisp-mode-map [(control ?c) ?!]
  'slime-switch-to-output-buffer)))

(defvar hyperspec-symbols (make-hash-table :test #'equal))
(defvar hyperspec-urls (make-hash-table :test #'equal))

(setq hyperspec-symbol-table
      "/Users/johnw/Reference/Computing/Languages/Common Lisp/HyperSpec/Data/Map_Sym.txt")

(defun build-hyperspec-symbol-reference ()
  (let ((index-buffer (find-file-noselect hyperspec-symbol-table)))
    (labels ((get-one-line () (prog1 
				  (delete* ?\n (thing-at-point 'line))
				(forward-line))))
      (save-excursion
	(set-buffer index-buffer)
	(goto-char (point-min))
	(while (< (point) (point-max))
	  (let* ((symbol (downcase (get-one-line)))
		 (relative-url (get-one-line)))
	    (setf relative-url
		  (subseq relative-url
			  (1+ (position ?\/ relative-url
					:from-end t))))
	    (puthash symbol relative-url hyperspec-symbols)
	    (unless (gethash relative-url hyperspec-urls)
	      (puthash relative-url symbol hyperspec-urls))))))))

(defun hyperspec-info (symbol-name)
  (interactive (list (let* ((symbol-at-point (slime-symbol-name-at-point))
                            (stripped-symbol 
                             (and symbol-at-point
                                  (downcase
                                   (common-lisp-hyperspec-strip-cl-package 
                                    symbol-at-point)))))
                       (if (and stripped-symbol
                                (intern-soft stripped-symbol
                                             common-lisp-hyperspec-symbols))
                           stripped-symbol
                         (completing-read
                          "Look up symbol in Common Lisp HyperSpec: "
                          common-lisp-hyperspec-symbols #'boundp
                          t stripped-symbol
                          'common-lisp-hyperspec-history)))))
  (let* ((url (gethash (downcase symbol-name) hyperspec-symbols))
	 (symbol (and url (gethash url hyperspec-urls))))
    (when symbol
      (info (concatenate 'string "(gcl) " symbol)))))

(eval-after-load "slime"
  '(progn
     (define-key slime-mode-map [return] 'paredit-newline)

     (define-key slime-repl-mode-map [tab] 'indent-or-complete)
     (define-key slime-repl-mode-map [(control return)] 'other-window)

     (define-key inferior-slime-mode-map [(control ?c) (control ?p)]
       'slime-repl-previous-prompt)
     (define-key inferior-slime-mode-map [(control return)] 'other-window)))
