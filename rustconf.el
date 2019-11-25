(require 'use-package)

(use-package direnv
  :demand t
  :init
  (defconst emacs-binary-path (directory-file-name
                               (file-name-directory
                                (executable-find "emacsclient"))))
  :config
  (eval-after-load 'flycheck
    '(setq flycheck-executable-find
           (lambda (cmd)
             (add-hook 'post-command-hook #'direnv--maybe-update-environment)
             (direnv-update-environment default-directory)
             (executable-find cmd))))

  (add-hook 'rust-mode-hook
            (lambda ()
              (add-hook 'post-command-hook #'direnv--maybe-update-environment)
              (direnv-update-environment default-directory)))

  (defun patch-direnv-environment (&rest _args)
    (setenv "PATH" (concat emacs-binary-path ":" (getenv "PATH")))
    (setq exec-path (cons (file-name-as-directory emacs-binary-path)
                          exec-path)))

  (advice-add 'direnv-update-directory-environment
              :after #'patch-direnv-environment)

  (add-hook 'git-commit-mode-hook #'patch-direnv-environment)
  (add-hook 'magit-status-mode-hook #'patch-direnv-environment))

(use-package lsp-mode
  :commands lsp)

(use-package lsp-ui
  :hook (lsp-mode . lsp-ui-mode)
  :config
  (define-key lsp-ui-mode-map [remap xref-find-definitions]
    #'lsp-ui-peek-find-definitions)
  (define-key lsp-ui-mode-map [remap xref-find-references]
    #'lsp-ui-peek-find-references))

(use-package cargo
  :hook (rust-mode . cargo-minor-mode)
  :bind (:map cargo-minor-mode-map
              ("C-c C-c C-y" . cargo-process-clippy))
  :config
  (defadvice cargo-process-clippy
      (around my-cargo-process-clippy activate)
    (let ((cargo-process--command-flags (concat cargo-process--command-flags
                                                " --tests -- -D clippy::all")))
      ad-do-it)))

(use-package rust-mode
  :mode "\\.rs\\'"
  :hook (rust-mode . lsp)
  :config
  (add-hook 'rust-mode-hook
            #'(lambda ()
                ;; (aggressive-indent-mode 1)
                ;; (electric-pair-mode 1)
                (flycheck-mode 1)
                (bind-key "M-n" #'flycheck-next-error rust-mode-map)
                (bind-key "M-p" #'flycheck-previous-error rust-mode-map))))

(use-package flycheck-rust
  :config (add-hook 'flycheck-mode-hook #'flycheck-rust-setup))

(use-package yasnippet
  :demand t
  :diminish yas-minor-mode
  :bind (("C-c y d" . yas-load-directory)
         ("C-c y i" . yas-insert-snippet)
         ("C-c y f" . yas-visit-snippet-file)
         ("C-c y n" . yas-new-snippet)
         ("C-c y t" . yas-tryout-snippet)
         ("C-c y l" . yas-describe-tables)
         ("C-c y g" . yas/global-mode)
         ("C-c y m" . yas/minor-mode)
         ("C-c y r" . yas-reload-all)
         ("C-c y x" . yas-expand))
  :bind (:map yas-keymap
              ("C-i" . yas-next-field-or-maybe-expand))
  :mode ("/\\.emacs\\.d/snippets/" . snippet-mode)
  :config
  ;; (yas-load-directory (emacs-path "snippets"))
  (yas-global-mode 1))
