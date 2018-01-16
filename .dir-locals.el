((emacs-lisp-mode
  (compile-command . "cask exec ert-runner --reporter ert")
  (eval ignore-errors
        (push (quote ("Tests" "(\\(\\<ert-deftest\\)\\>\\s *\\(\\(?:\\sw\\|\\s_\\)+\\)?" 2)) imenu-generic-expression)
        (when (string-match-p "test" (buffer-file-name))
          (setq-local emojify-inhibit-emojify-in-current-buffer-p t)))))
