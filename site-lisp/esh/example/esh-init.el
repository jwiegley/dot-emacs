;;;;;;;;;;;;;;;;;;;;;;;;
;; Load a color theme ;;
;;;;;;;;;;;;;;;;;;;;;;;;

(load-theme 'tango t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Register a few inline macros ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'esh)
(esh-latex-add-inline-verb "\\cverb" 'c-mode)
(esh-latex-add-inline-verb "\\javaverb" 'java-mode)
(esh-latex-add-inline-verb "\\pythonverb" 'python-mode)
(esh-latex-add-inline-verb "\\normallisp" 'emacs-lisp-mode)
(esh-latex-add-inline-verb "\\prettylisp" 'prettified-emacs-lisp-mode)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define a variant of Emacs-Lisp-mode that prettifies symbols ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun prettified-emacs-lisp-mode ()
  (emacs-lisp-mode)
  (setq-local prettify-symbols-alist
              '(("<=" . ?≤) ("or" . ?∨) ("/+/" . ?⊕)
                ("lambda" . ?λ) ("approx=" . ?≈)))
  (prettify-symbols-mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For the following to work, you'll need to modify the Makefile to  ;;
;; use the --cask option, and run ``cask install`` in this directory ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See https://github.com/cask/cask for more on managing Emacs packages
;; with Cask; it's a bit like virtualenvs for Python.

;;; Haskell

(require 'haskell nil t)
(setq-default haskell-font-lock-symbols t)

;;; Racket

(when (require 'racket-mode nil t)
  (defun my-racket-setup ()
    (setq-local prettify-symbols-alist '(("lambda" . ?λ)))
    (prettify-symbols-mode))
  (add-hook 'racket-mode-hook #'my-racket-setup))

;;; Dafny

(require 'dafny-mode nil t)

;;; F*

(require 'fstar-mode nil t)

;;; OCaml

(when (require 'tuareg nil t)
  (defun my-tuareg-setup ()
    (setq-local prettify-symbols-alist '(("fun" . ?λ) ("->" . ?→)))
    (prettify-symbols-mode))
  (add-hook 'tuareg-mode-hook #'my-tuareg-setup))

;;; Coq

;; This looks for a local install of Proof-General, because PG isn't on MELPA
(add-to-list 'load-path "~/.emacs.d/lisp/PG/generic/")
(when (and (require 'proof-site nil t)
           (require 'company-coq nil t))
  (setq-default proof-splash-seen t
                company-coq-local-symbols '(("->>" . ?↦) ("|>" . ?▹))
                company-coq-disabled-features '(code-folding))
  (add-hook #'coq-mode-hook #'company-coq-mode)
  (defun prettified-coq-mode ()
    (coq-mode)
    (company-coq-mode)))

;;; Ur/Web

;; Not on MELPA
;; (when (require 'urweb-mode nil t)
;;   (defun my-urweb-setup ()
;;     (setq-local prettify-symbols-alist '(("::" . ?∷) ("=>" . ?⇒)))
;;     (prettify-symbols-mode))
;;   (add-hook 'urweb-mode-hook #'my-urweb-setup))

;;;;;;;;;;;;;;;;;;;
;; Compatibility ;;
;;;;;;;;;;;;;;;;;;;

(eval-and-compile
  ;; Escape unicode symbols when using pdfLaTeX
  (when (getenv "ESH_PDFLATEX")
    (setq esh-substitute-unicode-symbols t)
    (esh-latex-add-unicode-substitution "∷" "\\ensuremath{::}"))
  ;; Disable prettification when using Emacs < 24.5
  (unless (fboundp 'prettify-symbols-mode)
    (fset 'prettify-symbols-mode #'ignore)))
