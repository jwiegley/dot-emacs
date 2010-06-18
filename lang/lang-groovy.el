;;;_ * groovy-mode

(autoload 'groovy-mode "groovy" "" t)

(add-to-list 'interpreter-mode-alist '("groovy" . groovy-mode))
(add-to-list 'auto-mode-alist '("\\.groovy\\'" . groovy-mode))

(defun my-groovy-mode-hook ()
  (define-key groovy-mode-map "\C-m" 'newline-and-indent)
  (setq groovy-indent-level 3)
  (setq indent-tabs-mode nil)
  (set-fill-column 100))

(add-hook 'groovy-mode-hook 'my-groovy-mode-hook)
