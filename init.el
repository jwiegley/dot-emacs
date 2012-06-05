;;; init.el --- Where all the magic begins

(if (featurep 'aquamacs)
    (load "~/.emacs.d/init-aquamacs")

  (load "~/.emacs.d/load-path")

  (defmacro use-package (name &rest args)
    (let ((commands (plist-get args :commands))
          (init-body (plist-get args :init))
          (config-body (plist-get args :config))
          (diminish-var (plist-get args :diminish))
          (name-string (if (stringp name) name
                         (symbol-name name))))
      (if diminish-var
          (setq config-body
                `(progn
                   ,config-body
                   (ignore-errors (diminish (quote ,diminish-var))))))
      (if (or commands (plist-get args :defer))
          (let (form)
            (unless (listp commands)
              (setq commands (list commands)))
            (dolist (command commands)
              (add-to-list
               'form `(autoload (function ,command)
                        ,name-string nil t)))
            `(progn
               ,@form
               ,init-body
               (eval-after-load ,name-string
                 (quote ,config-body))))
        `(when ,(if (stringp name)
                    `(load ,name t)
                  `(require ',name nil t))
           ,init-body
           ,config-body))))

  (put 'use-package 'lisp-indent-function 1)

  (font-lock-add-keywords 'emacs-lisp-mode
                          '(("(use-package\\>" . font-lock-keyword-face)))

  (load "~/.emacs.d/emacs"))

;;; init.el ends here
