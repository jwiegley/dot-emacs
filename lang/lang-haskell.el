;;;_ * groovy-mode

(autoload 'haskell-mode "haskell-site-file" nil t)

(add-to-list 'auto-mode-alist '("\\.l?hs$" . haskell-mode))

(defun my-haskell-mode-hook ()
       ;;(flymake-mode)

       (setq haskell-saved-check-command haskell-check-command)

       (define-key haskell-mode-map [(control ?c) ?w]
         'flymake-display-err-menu-for-current-line)
       (define-key haskell-mode-map [(control ?c) ?*]
         'flymake-start-syntax-check)
       (define-key haskell-mode-map [(meta ?n)] 'flymake-goto-next-error)
       (define-key haskell-mode-map [(meta ?p)] 'flymake-goto-prev-error))

(eval-after-load "haskell-site-file"
  '(progn
     (require 'inf-haskell)
     (require 'hs-lint)))
