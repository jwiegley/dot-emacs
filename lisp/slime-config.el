;;;   - slime

(require 'slime)

(eval-when-compile
  (defvar slime-repl-mode-map))

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

