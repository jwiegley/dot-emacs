;;;_ * groovy-mode

(load "haskell-site-file" t)

(defun my-haskell-mode-hook ()
  (flymake-mode)

  (setq haskell-saved-check-command haskell-check-command)

  (define-key haskell-mode-map [(control ?c) ?w]
    'flymake-display-err-menu-for-current-line)
  (define-key haskell-mode-map [(control ?c) ?*]
    'flymake-start-syntax-check)
  (define-key haskell-mode-map [(meta ?n)] 'flymake-goto-next-error)
  (define-key haskell-mode-map [(meta ?p)] 'flymake-goto-prev-error))

(load "inf-haskell" t)
(load "hs-lint" t)
