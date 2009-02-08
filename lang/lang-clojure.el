(add-to-list 'load-path "~/Library/Emacs/site-lisp/slime")
(add-to-list 'load-path "~/Library/Emacs/site-lisp/slime/contrib")

(setq slime-net-coding-system 'utf-8-unix
      swank-clojure-jar-path "/opt/local/share/java/clojure/lib/clojure.jar"
      swank-clojure-binary "clojure")

(require 'slime)
(require 'clojure-mode)
(require 'swank-clojure-autoload)

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
   slime-package-fu
   slime-fontifying-fu
   slime-mdot-fu
   slime-scratch
   slime-tramp
   slime-enclosing-context
   slime-xref-browser))

(setq slime-complete-symbol*-fancy t
      slime-complete-symbol-function 'slime-fuzzy-complete-symbol)

(add-to-list 'auto-mode-alist '("\\.clj$" . clojure-mode))

(defun start-slime ()
  (interactive)
  (unless (slime-connected-p)
    (save-excursion (slime))))

(add-hook 'slime-mode-hook 'start-slime)
(add-hook 'slime-load-hook #'(lambda () (require 'slime-fancy)))
(add-hook 'inferior-lisp-mode-hook #'(lambda () (inferior-slime-mode t)))

(defun indent-or-complete (&optional arg)
  (interactive "p")
  (if (or (looking-back "^\\s-*") (bolp))
      (call-interactively 'lisp-indent-line)
    (call-interactively 'slime-indent-and-complete-symbol)))

(eval-after-load "slime"
  '(progn
     (define-key slime-mode-map [return] 'paredit-newline)
     (define-key slime-repl-mode-map [tab] 'indent-or-complete)
     (define-key slime-repl-mode-map [(control return)] 'other-window)))

;; lang-clojure.el ends here
