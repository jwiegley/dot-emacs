;;;_ * groovy-mode

(load "haskell-site-file" t)

(defun my-haskell-mode-hook ()
  (flymake-mode)

  (turn-on-haskell-doc-mode)
  (turn-on-haskell-indentation)

  (define-key haskell-mode-map [(control ?c) ?w]
    'flymake-display-err-menu-for-current-line)
  (define-key haskell-mode-map [(control ?c) ?*]
    'flymake-start-syntax-check)
  (define-key haskell-mode-map [(meta ?n)] 'flymake-goto-next-error)
  (define-key haskell-mode-map [(meta ?p)] 'flymake-goto-prev-error))

(add-hook 'haskell-mode-hook 'my-haskell-mode-hook)

(load "inf-haskell" t)
(load "hs-lint" t)
