;;;_ * ruby

(autoload 'ruby-mode "ruby-mode"
  "Mode for editing ruby source files" t)
(autoload 'ruby-electric-mode "ruby-electric" t)

(setq ri-ruby-program "/usr/local/bin/ruby")
(setq ri-ruby-script "/Users/johnw/bin/ri-emacs.rb")

(autoload 'ri "ri-ruby" nil t)

(add-to-list 'auto-mode-alist '("\\.rb$" . ruby-mode))
(add-to-list 'interpreter-mode-alist '("ruby" . ruby-mode))

(autoload 'run-ruby "inf-ruby" "Run an inferior Ruby process")
(autoload 'inf-ruby-keys "inf-ruby"
  "Set local key defs for inf-ruby in ruby-mode")
(add-hook 'ruby-mode-hook '(lambda () (inf-ruby-keys)))
(add-hook 'ruby-mode-hook 'turn-on-font-lock)

(defun my-ruby-mode-hook ()
  (setq standard-indent 2)
  (ruby-electric-mode t)
  (local-set-key [f1] 'ri)
  (local-set-key "\M-\C-i" 'ri-ruby-complete-symbol)
  (local-set-key [f4] 'ri-ruby-show-args)
  (define-key ruby-mode-map "\C-c\C-a" 'ruby-eval-buffer))

(add-hook 'ruby-mode-hook 'my-ruby-mode-hook)

(autoload 'rubydb "rdebug" "Ruby debugger" t)

(provide 'lang-ruby)
